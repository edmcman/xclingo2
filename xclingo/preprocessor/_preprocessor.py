from clingo.symbol import Number
from ._utils import (
    translate_show_all,
    translate_trace,
    translate_trace_all,
    translate_mute,
    is_xclingo_label,
    is_xclingo_show_trace,
    is_choice_rule,
    is_label_rule,
    is_xclingo_mute,
    is_constraint,
    is_disyunctive_head,
)
from clingo import ast
from clingo.ast import ASTSequence


def _make_vars_safe(node, counter):
    """Replace anonymous variables (_) with fresh named variables (_Xcl0, _Xcl1, ...).

    When xclingo copies body literals into the head tuple (for _xclingo_sup /
    _xclingo_fbody), anonymous variables become unsafe because they appear in
    the head without being bound in the body of the transformed rule.  Replacing
    them with named variables that are shared between head and body fixes this.
    """
    if node.ast_type == ast.ASTType.Variable:
        if node.name == "_":
            name = f"_Xcl{next(counter)}"
            return ast.Variable(node.location, name)
        return node

    if node.ast_type == ast.ASTType.SymbolicTerm:
        return node

    # Reconstruct node with transformed children.
    kwargs = {}
    for key in node.child_keys:
        child = getattr(node, key, None)
        if child is None:
            kwargs[key] = None
        elif isinstance(child, ASTSequence) or isinstance(child, list):
            kwargs[key] = [_make_vars_safe(item, counter) for item in child]
        elif hasattr(child, "ast_type"):
            kwargs[key] = _make_vars_safe(child, counter)
        else:
            kwargs[key] = child
    return node.update(**kwargs)


def _make_rule_safe(rule_ast):
    """Make anonymous variables safe for xclingo by renaming them selectively.

    Only renames _ in the head atom and in positive SymbolicAtom body literals
    (the ones that propagates() copies into the head tuple).  Renaming _ in
    negated literals or aggregates would create unsafe variables that only
    appear in negated body literals.
    """
    counter = iter(range(100000))

    # Rename _ in head
    new_head = _make_vars_safe(rule_ast.head, counter)

    # Rename _ only in positive SymbolicAtom body literals
    new_body = []
    for lit in rule_ast.body:
        if (
            lit.ast_type == ast.ASTType.Literal
            and lit.sign == ast.Sign.NoSign
            and lit.atom.ast_type == ast.ASTType.SymbolicAtom
        ):
            new_body.append(_make_vars_safe(lit, counter))
        else:
            new_body.append(lit)

    return rule_ast.update(head=new_head, body=new_body)


class Preprocessor:
    def __init__(self):
        self._rule_count = 1
        self._last_trace_rule = None
        self._translation = ""

    def increment_rule_count(self):
        n = self._rule_count
        self._rule_count += 1
        return n

    @staticmethod
    def translate_annotations(program):
        return translate_trace_all(translate_show_all(translate_trace(translate_mute(program))))

    def propagates(self, lit_list):
        for lit in lit_list:
            if lit.sign == ast.Sign.NoSign and lit.atom.ast_type == ast.ASTType.SymbolicAtom:
                yield lit

    def sup_body(self, lit_list):
        loc = ast.Location(
            ast.Position("", 0, 0),
            ast.Position("", 0, 0),
        )
        for lit in lit_list:
            if lit.ast_type == ast.ASTType.Literal:
                if lit.atom.ast_type == ast.ASTType.SymbolicAtom:
                    yield ast.Literal(
                        loc,
                        lit.sign,
                        ast.SymbolicAtom(
                            ast.Function(
                                loc,
                                "_xclingo_model",
                                [lit.atom.symbol],
                                False,
                            )
                        ),
                    )

                elif lit.atom.ast_type == ast.ASTType.BodyAggregate:
                    yield ast.Literal(
                        loc,
                        lit.sign,
                        ast.BodyAggregate(
                            loc,
                            left_guard=lit.atom.left_guard,
                            function=lit.atom.function,
                            elements=[
                                ast.BodyAggregateElement(
                                    terms=list(self.sup_body(e.terms)),
                                    condition=list(self.sup_body(e.condition)),
                                )
                                for e in lit.atom.elements
                            ],
                            right_guard=lit.atom.right_guard,
                        ),
                    )

                elif lit.atom.ast_type == ast.ASTType.Aggregate:
                    def _wrap_cond_lit_sup(e):
                        inner = e.literal
                        if (inner.ast_type == ast.ASTType.Literal
                                and inner.sign == ast.Sign.NoSign
                                and inner.atom.ast_type == ast.ASTType.SymbolicAtom):
                            inner = ast.Literal(loc, inner.sign, ast.SymbolicAtom(
                                ast.Function(loc, "_xclingo_model", [inner.atom.symbol], False)))
                        return ast.ConditionalLiteral(loc, inner, list(self.sup_body(e.condition)))
                    yield ast.Literal(
                        loc,
                        lit.sign,
                        ast.Aggregate(
                            loc,
                            left_guard=lit.atom.left_guard,
                            elements=[_wrap_cond_lit_sup(e) for e in lit.atom.elements],
                            right_guard=lit.atom.right_guard,
                        ),
                    )

                else:
                    yield lit

            else:
                yield lit

    def sup_head(self, rule_id, rule_ast):
        loc = ast.Location(
            ast.Position("", 0, 0),
            ast.Position("", 0, 0),
        )
        head = ast.Literal(
            loc,
            ast.Sign.NoSign,
            ast.SymbolicAtom(
                ast.Function(
                    loc,
                    "_xclingo_sup",
                    [
                        ast.SymbolicTerm(loc, Number(rule_id)),
                        rule_ast.head.atom,
                        ast.Function(loc, "", list(self.propagates(rule_ast.body)), False),  # tuple
                    ],
                    False,
                ),
            ),
        )
        return head

    def support_rule(self, rule_id, rule_ast):
        loc = ast.Location(
            ast.Position("", 0, 0),
            ast.Position("", 0, 0),
        )
        head = self.sup_head(rule_id, rule_ast)
        body = list(self.sup_body(rule_ast.body))

        return ast.Rule(loc, head, body)

    def fbody_head(self, rule_id, rule_ast):
        loc = ast.Location(
            ast.Position("", 0, 0),
            ast.Position("", 0, 0),
        )
        head = ast.Literal(
            loc,
            ast.Sign.NoSign,
            ast.SymbolicAtom(
                ast.Function(
                    loc,
                    "_xclingo_fbody",
                    [
                        ast.SymbolicTerm(loc, Number(rule_id)),
                        rule_ast.head.atom,
                        ast.Function(loc, "", list(self.propagates(rule_ast.body)), False),  # tuple
                    ],
                    False,
                ),
            ),
        )
        return head

    def fbody_body(self, lit_list):
        loc = ast.Location(
            ast.Position("", 0, 0),
            ast.Position("", 0, 0),
        )
        for lit in lit_list:
            if lit.ast_type == ast.ASTType.Literal:
                if lit.atom.ast_type == ast.ASTType.SymbolicAtom:
                    if lit.sign == ast.Sign.NoSign:
                        yield ast.Literal(
                            loc,
                            lit.sign,
                            ast.SymbolicAtom(
                                ast.Function(
                                    loc,
                                    "_xclingo_f_atom",
                                    [lit.atom.symbol],
                                    False,
                                )
                            ),
                        )
                    else:
                        yield ast.Literal(
                            loc,
                            ast.Sign.Negation,
                            ast.SymbolicAtom(
                                ast.Function(
                                    loc,
                                    "_xclingo_model",
                                    [lit.atom.symbol],
                                    False,
                                )
                            ),
                        )

                elif lit.atom.ast_type == ast.ASTType.BodyAggregate:
                    yield ast.Literal(
                        loc,
                        lit.sign,
                        ast.BodyAggregate(
                            loc,
                            left_guard=lit.atom.left_guard,
                            function=lit.atom.function,
                            elements=[
                                ast.BodyAggregateElement(
                                    terms=list(self.fbody_body(e.terms)),
                                    condition=list(self.fbody_body(e.condition)),
                                )
                                for e in lit.atom.elements
                            ],
                            right_guard=lit.atom.right_guard,
                        ),
                    )

                elif lit.atom.ast_type == ast.ASTType.Aggregate:
                    def _wrap_cond_lit_fbody(e):
                        inner = e.literal
                        if (inner.ast_type == ast.ASTType.Literal
                                and inner.sign == ast.Sign.NoSign
                                and inner.atom.ast_type == ast.ASTType.SymbolicAtom):
                            inner = ast.Literal(loc, inner.sign, ast.SymbolicAtom(
                                ast.Function(loc, "_xclingo_f_atom", [inner.atom.symbol], False)))
                        elif (inner.ast_type == ast.ASTType.Literal
                                and inner.sign != ast.Sign.NoSign
                                and inner.atom.ast_type == ast.ASTType.SymbolicAtom):
                            inner = ast.Literal(loc, ast.Sign.Negation, ast.SymbolicAtom(
                                ast.Function(loc, "_xclingo_model", [inner.atom.symbol], False)))
                        return ast.ConditionalLiteral(loc, inner, list(self.fbody_body(e.condition)))
                    yield ast.Literal(
                        loc,
                        lit.sign,
                        ast.Aggregate(
                            loc,
                            left_guard=lit.atom.left_guard,
                            elements=[_wrap_cond_lit_fbody(e) for e in lit.atom.elements],
                            right_guard=lit.atom.right_guard,
                        ),
                    )

                else:
                    yield lit
            else:
                yield lit

    def fbody_rule(self, rule_id, rule_ast):
        loc = ast.Location(
            ast.Position("", 0, 0),
            ast.Position("", 0, 0),
        )
        head = self.fbody_head(rule_id, rule_ast)
        body = list(self.fbody_body(rule_ast.body))
        return ast.Rule(loc, head, body)

    def label_rule(self, rule_id, label_rule_ast, rule_body):
        loc = ast.Location(
            ast.Position("", 0, 0),
            ast.Position("", 0, 0),
        )
        head_var = ast.Variable(loc, "Head")
        head = ast.Literal(
            loc,
            label_rule_ast.head.sign,
            ast.SymbolicAtom(
                ast.Function(
                    loc,
                    label_rule_ast.head.atom.symbol.name,
                    [head_var, label_rule_ast.head.atom.symbol.arguments[1]],
                    False,
                )
            ),
        )
        body = [
            ast.Literal(
                loc,
                ast.Sign.NoSign,
                ast.SymbolicAtom(
                    ast.Function(
                        loc,
                        "_xclingo_f",
                        [
                            ast.SymbolicTerm(loc, Number(rule_id)),
                            head_var,
                            ast.Function(
                                loc,
                                "",
                                list(self.propagates(rule_body)),
                                False,
                            ),
                        ],
                        False,
                    )
                ),
            )
        ]
        rule = ast.Rule(loc, head, body)
        return rule

    def label_atom(self, rule_ast):
        loc = ast.Location(
            ast.Position("", 0, 0),
            ast.Position("", 0, 0),
        )
        fatom = ast.Literal(
            loc,
            ast.Sign.NoSign,
            ast.SymbolicAtom(
                ast.Function(
                    loc,
                    "_xclingo_intree",
                    [rule_ast.head.atom.symbol.arguments[0]],
                    False,
                )
            ),
        )
        body = [fatom] + list(self.sup_body(rule_ast.body))
        rule = ast.Rule(loc, rule_ast.head, body)
        return rule

    def show_trace(self, rule_ast):
        loc = ast.Location(
            ast.Position("", 0, 0),
            ast.Position("", 0, 0),
        )
        literal_head = ast.Literal(
            loc,
            ast.Sign.NoSign,
            ast.SymbolicAtom(rule_ast.head.atom.symbol.arguments[0]),
        )
        rule = ast.Rule(
            loc, rule_ast.head, list(self.sup_body([literal_head] + list(rule_ast.body)))
        )
        return rule

    def mute(self, rule_ast):
        loc = ast.Location(
            ast.Position("", 0, 0),
            ast.Position("", 0, 0),
        )
        literal_head = ast.Literal(
            loc,
            ast.Sign.NoSign,
            ast.SymbolicAtom(rule_ast.head.atom.symbol.arguments[0]),
        )
        rule = ast.Rule(
            loc, rule_ast.head, list(self.sup_body([literal_head] + list(rule_ast.body)))
        )
        return rule

    def add_to_translation(self, a):
        self._translation += f"{a}\n"

    def add_comment_to_translation(self, a):
        self._translation += f"% {a}\n"

    def translate_rule(self, rule_ast):
        self.add_comment_to_translation(rule_ast)
        if rule_ast.ast_type == ast.ASTType.Rule and not is_constraint(rule_ast):
            rule_ast = _make_rule_safe(rule_ast)
            if is_xclingo_label(rule_ast):
                if is_label_rule(rule_ast):
                    self._last_trace_rule = rule_ast
                    return
                self.add_to_translation(self.label_atom(rule_ast))
            elif is_xclingo_show_trace(rule_ast):
                self.add_to_translation(self.show_trace(rule_ast))
                pass
            elif is_xclingo_mute(rule_ast):
                self.add_to_translation(self.mute(rule_ast))
            else:
                rule_id = self.increment_rule_count()
                if is_choice_rule(rule_ast) or is_disyunctive_head(rule_ast):
                    for cond_lit in rule_ast.head.elements:
                        false_rule = ast.Rule(
                            ast.Location(
                                ast.Position("", 0, 0),
                                ast.Position("", 0, 0),
                            ),
                            cond_lit.literal,
                            list(cond_lit.condition) + list(rule_ast.body),
                        )
                        self.add_to_translation(self.support_rule(rule_id, false_rule))
                        self.add_to_translation(self.fbody_rule(rule_id, false_rule))
                        if self._last_trace_rule is not None:
                            self.add_to_translation(
                                self.label_rule(rule_id, self._last_trace_rule, false_rule.body)
                            )
                    if self._last_trace_rule is not None:
                        self._last_trace_rule = None
                else:  # Other cases
                    self.add_to_translation(self.support_rule(rule_id, rule_ast))
                    self.add_to_translation(self.fbody_rule(rule_id, rule_ast))
                    if self._last_trace_rule is not None:
                        self.add_to_translation(
                            self.label_rule(rule_id, self._last_trace_rule, rule_ast.body)
                        )
                        self._last_trace_rule = None

    def translate_program(self, program, name=""):
        self._translation += "%" * 8 + name + "%" * 8 + "\n"
        ast.parse_string(
            Preprocessor.translate_annotations(program),
            lambda ast: self.translate_rule(ast),
        )

    def get_translation(self):
        return self._translation
