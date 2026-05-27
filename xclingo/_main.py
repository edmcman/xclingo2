from typing import Iterable, Sequence
from clingo import Model, Function, String
from clingo.ast import ProgramBuilder, parse_string
from clingo.control import Control
from clingo.symbol import SymbolType
from xclingo.explanation import Explanation
from xclingo.preprocessor import Preprocessor

from clingo.core import MessageCode

class Context:
    def label(self, text, tup):
        if text.type == SymbolType.String:
            text = text.string
        else:
            text = str(text).strip('"')
        for val in tup.arguments:
            text = text.replace("%", val.string if val.type==SymbolType.String else str(val), 1)
        return [String(text)]

    def inbody(self, body):
        if len(body.arguments)>0:
            return [Function(
                '',
                [a, body],
                True,
            )
            for a in body.arguments]
        else:
            return Function('empty', [], True)

class Explainer():
    def __init__(self, internal_control_arguments=['1'], auto_trace="none"):
        self._preprocessor = Preprocessor()
        self._memory = []
        
        self._internal_control_arguments = internal_control_arguments 
        self._auto_trace = auto_trace
        self._translated = False
        self._current_model = []

        self._no_labels = False
        self._no_show_trace = False

    def logger(self, _code, msg):
        if _code == MessageCode.AtomUndefined:
            if 'xclingo_muted(Cause)' in msg:
                return
            if '_xclingo_label_tree/3' in msg:
                return
            if '_xclingo_label' in msg:
                self._no_labels = True
                return
            if '_xclingo_show_trace' in msg:
                self._no_show_trace = True
        print(msg)

    def print_messages(self):
        if self._no_labels:
            print('xclingo info: any atom or rule has been labelled.')
        if self._no_show_trace:
            print('xclingo info: any atom has been affected by a %!show_trace annotation.')
    
    def clean_log(self):
        self._no_labels = False
        self._no_show_trace = False

    def _getExplainerLP(self, auto_trace="none"):
        if hasattr(self, '_explainerLP') == False:
            setattr(self, '_explainerLP', self._loadExplainerLP(auto_trace))
        return self._explainerLP

    def _loadExplainerLP(self, auto_trace="none"):
        try:
            import importlib.resources as pkg_resources
        except ImportError:
            # Try backported to PY<37 `importlib_resources`.
            import importlib_resources as pkg_resources

        from . import xclingo_lp  # relative-import the *package* containing the templates
        program = pkg_resources.read_text(xclingo_lp, 'xclingo.lp')
        if auto_trace == "all":
            program += pkg_resources.read_text(xclingo_lp, 'autotrace_all.lp')
        elif auto_trace == "facts":
            program += pkg_resources.read_text(xclingo_lp, 'autotrace_facts.lp')
        return program

    def add(self, program_name:str, parameters: Iterable[str], program:str):
        self._memory.append((program_name, program))

    def _initialize_control(self):
        return Control(
            self._internal_control_arguments + \
                [
                    '--project=project'
                ], 
            logger=self.logger)

    def _translate_program(self):
        self._preprocessor._rule_count = 1
        for name, program in self._memory:
            self._preprocessor.translate_program(program, name=name)

    def _ground(self, control, model, context=None):
        """Grounding for the explainer clingo control. It translates the program and adds the original program's model as facts.

        Args:
            control (_type_): _description_
            model (_type_): _description_
            context (_type_, optional): _description_. Defaults to None.
        """
        if not self._translated:
            self._translate_program()
            self._translated = True
            
        with ProgramBuilder(control) as builder:
            parse_string(
                self._getExplainerLP(auto_trace=self._auto_trace)+self._preprocessor.get_translation(),
                lambda ast: builder.add(ast),
            )
        
        with control.backend() as backend:
            for sym in model.symbols(atoms=True):
                atm_id = backend.add_atom(Function('_xclingo_model', [sym], True))
                backend.add_rule([atm_id], [], False)
            
        control.ground([('base', [])], context=context if context is not None else Context())


    def _get_explanations(self, control):
        with control.solve(yield_=True) as it:
            for expl_model in it:
                syms = expl_model.symbols(shown=True)  # shown is True because we want to get only the summarized graph
                if len(syms)>0:
                    yield Explanation.from_model(syms)
    
    def _get_models(self, control):
        with control.solve(yield_=True) as it:
            for expl_model in it:
                yield expl_model

    def get_xclingo_models(self, model:Model) -> Iterable[Explanation]:
        control = self._initialize_control()
        self.clean_log()
        self._ground(control, model)
        self.print_messages()
        return self._get_models(control)

    def explain(self, model:Model, context=None) -> Iterable[Explanation]:
        control = self._initialize_control()    
        self.clean_log()
        self._ground(control, model, context)
        self.print_messages()
        return self._get_explanations(control)


class _FrozenModel:
    """Holds atoms captured from a live Model so they can be explained after solve."""
    def __init__(self, syms): self._syms = syms
    def symbols(self, atoms=False, **_): return self._syms


class XclingoControl:
    def __init__(self, n_solutions='1', n_explanations='0', auto_trace='none', clingo_flags=None):
        self.n_solutions = n_solutions
        self.n_explanations = n_explanations

        # Always enumerate all models (0); explain() limits output to n_solutions.
        # This ensures optimization programs run to proven optimality before explanation.
        self.control = Control(['0'] + (clingo_flags or []))
        self.explainer = Explainer(
            [
                n_explanations if type(n_explanations)==str else str(n_explanations), 
            ], 
            auto_trace=auto_trace
        )

        self._explainer_context = None

    def add(self, name, parameters, program):
        """It adds a program to the control.

        Args:
            name (str): name of program block to add.
            parameters (Iterable[str]): a list (or iterable) of for the program.
            program (str): a logic program in ASP format.
        """
        self.control.add("base", parameters, program)
        self.explainer.add(name, [], program)
        
    def ground(self, context=None):
        """Ground (only base for now) programs.

        Args:
            context (Object, optional): Context to be passed to the original program control. Defaults to None.
        """
        self.control.ground([("base", [])], context)

    def get_xclingo_models(self):
        """Returns the clingo.Model objects of the explainer, this is the models which represent the explanations.

        Returns:
            Generator[cilngo.Model]: a generator of clingo.Model objects.
        """
        with self.control.solve(yield_=True) as it:
            for model in it:
                return self.explainer.get_xclingo_models(model)

    def explain(self, on_explanation=None):
        """Returns a generator of xclingo.explanation.Explanation objects. If on_explanation is not None, it is called for each explanation.

        Args:
            on_explanation (Callable, optional): callable that will be called for each Explanation, it must receive Explanation as a parameter. Defaults to None.

        Yields:
            Explation: a tree-like object that represents an explanation.
        """
        n_limit = int(self.n_solutions)  # 0 = unlimited
        n_explained = 0
        opt_syms = None  # atoms from the last improving model (optimization only)

        with self.control.solve(yield_=True) as handle:
            for m in handle:
                if m.cost:
                    # Optimization program: save atoms from the current (best) model.
                    # Model objects are invalidated when iteration advances, so we capture
                    # the symbol list now and explain the final (optimal) model after the loop.
                    opt_syms = list(m.symbols(atoms=True))
                else:
                    # Plain SAT: explain immediately while the model is still live.
                    expls = self.explainer.explain(m, context=self._explainer_context)
                    if on_explanation is None:
                        yield expls
                    else:
                        on_explanation(expls)
                    n_explained += 1
                    if n_limit and n_explained >= n_limit:
                        handle.cancel()
                        break

        # For optimization programs, explain only the last (proven-optimal) model.
        if opt_syms is not None:
            expls = self.explainer.explain(_FrozenModel(opt_syms), context=self._explainer_context)
            if on_explanation is None:
                yield expls
            else:
                on_explanation(expls)

    def _default_output(self):
        output = ''
        n = 0
        for answer in self.explain():
            n = 1
            output += f'Answer {n}\n'
            output += '\n'.join([expl.ascii_tree() for expl in answer])
            output += '\n'
        return output