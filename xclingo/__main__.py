from xclingo import Explainer as Explainer
from xclingo import XclingoControl
from xclingo import __version__ as xclingo_version
from argparse import ArgumentParser, FileType
import os
import re
import sys

_INCLUDE_RE = re.compile(r'^#include\s+"([^"]+)"\s*\.\s*$')

def expand_includes(text, base_dir, visited=None):
    """Recursively expand #include directives, preserving comments and annotations."""
    if visited is None:
        visited = set()
    lines = text.split('\n')
    result = []
    for line in lines:
        m = _INCLUDE_RE.match(line)
        if m:
            inc_path = os.path.normpath(os.path.join(base_dir, m.group(1)))
            if inc_path not in visited:
                visited.add(inc_path)
                with open(inc_path) as f:
                    inc_text = f.read()
                result.append(expand_includes(inc_text, os.path.dirname(inc_path), visited))
        else:
            result.append(line)
    return '\n'.join(result)

def check_options():
    # Handles arguments of xclingo
    parser = ArgumentParser(description='Tool for explaining (and debugging) ASP programs', prog='xclingo')
    parser.add_argument('--version', action='version',
                        version='xclingo {version}'.format(version=xclingo_version),
                        help='Prints the version and exists.')
    optional_group = parser.add_mutually_exclusive_group()
    optional_group.add_argument('--only-translate', action='store_true',
                        help="Prints the internal translation and exits.")
    optional_group.add_argument('--only-translate-annotations', action='store_true',
                        help="Prints the internal translation and exits.")
    optional_group.add_argument('--only-explanation-atoms', action='store_true',
                        help="Prints the atoms used by the explainer to build the explanations.")
    parser.add_argument('--auto-tracing', type=str, choices=["none", "facts", "all"], default="none",
                        help="Automatically creates traces for the rules of the program. Default: none.")
    parser.add_argument('-n', nargs=2, default=(1,1), type=int, help="Number of answer sets and number of desired explanations.")
    parser.add_argument('--only-last', action='store_true',
                        help="Only explain the last answer set (e.g., the optimal model).")
    parser.add_argument('--show-trace', action='append', metavar='ATOM', default=[],
                        help="Add a show_trace annotation for ATOM (e.g. 'sameClass(4,2).'). May be repeated.")
    parser.add_argument('infiles', nargs='+', type=FileType('r'), default=sys.stdin, help="ASP program")
    return parser.parse_known_args()

def read_files(files):
    return "\n".join([file.read() for file in files])

def read_files_expanded(files):
    """Read all files and recursively expand #include directives."""
    parts = []
    for f in files:
        path = f.name
        text = f.read()
        base_dir = os.path.dirname(os.path.abspath(path)) if path else '.'
        parts.append(expand_includes(text, base_dir))
    return '\n'.join(parts)

def inject_show_traces(program, atoms):
    """Prepend %!show_trace directives for CLI-specified atoms."""
    if not atoms:
        return program
    lines = '\n'.join(f'%!show_trace {a if a.endswith(".") else a + "."}' for a in atoms)
    return lines + '\n' + program

def translate(program, auto_trace):
    explainer = Explainer(auto_trace=auto_trace)
    explainer.add('base', [], program)
    explainer._translate_program()
    translation =  explainer._preprocessor.get_translation()
    translation += explainer._getExplainerLP(auto_trace=auto_trace)
    return translation

def print_explanation_atoms(xControl: XclingoControl):
    n = 0
    for xmodel in xControl.get_xclingo_models():
        n += 1
        print(f'Answer {n}')
        print(xmodel)

def print_text_explanations(xControl: XclingoControl):
    n = 0
    for answer in xControl.explain():
        n += 1
        print(f'Answer {1}')
        for expl in answer:
            print(expl.ascii_tree())



def main():
    args, clingo_flags = check_options()

    program = inject_show_traces(read_files_expanded(args.infiles), args.show_trace)

    if args.only_translate_annotations:
        from xclingo.preprocessor import Preprocessor
        print(Preprocessor.translate_annotations(program))
        return 0

    if args.only_translate:
        print(translate(program, args.auto_tracing))
        return 0

    only_last = args.only_last or args.n[0] == -1
    n_solutions = '0' if args.n[0] == -1 else str(args.n[0])
    xControl = XclingoControl(
        n_solutions=n_solutions,
        n_explanations=str(args.n[1]),
        auto_trace=args.auto_tracing,
        clingo_flags=clingo_flags,
        only_last=only_last,
    )

    xControl.add("base", [], program)

    xControl.ground()

    if args.only_explanation_atoms:
        print_explanation_atoms(xControl)
    else:
        print_text_explanations(xControl)

if __name__ == '__main__':
    main()
