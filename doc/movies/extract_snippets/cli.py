import argparse
from pathlib import Path


def build_parser() -> argparse.ArgumentParser:
    """
    build parser

    :return: Argument parser
    """
    DESCRIPTION = "Extract snippet in coq file (.v) generate by alectryon."
    parser = argparse.ArgumentParser(DESCRIPTION)

    INPUT_FILES_HELP = "coq file '.v'"
    parser.add_argument("input",
                        type=Path,
                        help=INPUT_FILES_HELP)

    OUPUT_DIR_HELP = "output directory"
    parser.add_argument("-o", "--output-dir",
                        default=Path("."),
                        type=Path,
                        help=OUPUT_DIR_HELP)

    DUMP_LATEX_HELP = "dump latex complete file (usefull to debug)"
    parser.add_argument("-d", "--dump-complete-latex",
                        action="store_true",
                        help=DUMP_LATEX_HELP)

    DUMP_LATEX_DIR_HELP = "directory to dump complete latex" \
                          "file (please active flag '--dump-complete-latex')"
    parser.add_argument("-D", "--dump-complete-latex-dir",
                        type=Path,
                        default=Path("."),
                        help=DUMP_LATEX_DIR_HELP)

    # serapi (copy from alectryon.cli)
    SUBP_HELP = "Pass arguments to the SerAPI process"
    subp = parser.add_argument_group("Subprocess arguments", SUBP_HELP)

    SERTOP_ARGS_HELP = "Pass a single argument to SerAPI (e.g. -Q dir,lib)."
    subp.add_argument("--sertop-arg", dest="sertop_args",
                      action="append", default=[],
                      metavar="SERAPI_ARG",
                      help=SERTOP_ARGS_HELP)

    I_HELP = "Pass -I DIR to the SerAPI subprocess."
    subp.add_argument("-I", "--ml-include-path", dest="coq_args_I",
                      metavar="DIR", nargs=1, action="append",
                      default=[], help=I_HELP)

    Q_HELP = "Pass -Q DIR COQDIR to the SerAPI subprocess."
    subp.add_argument("-Q", "--load-path", dest="coq_args_Q",
                      metavar=("DIR", "COQDIR"), nargs=2, action="append",
                      default=[], help=Q_HELP)

    R_HELP = "Pass -R DIR COQDIR to the SerAPI subprocess."
    subp.add_argument("-R", "--rec-load-path", dest="coq_args_R",
                      metavar=("DIR", "COQDIR"), nargs=2, action="append",
                      default=[], help=R_HELP)

    EXPECT_UNEXPECTED_HELP = "Ignore unexpected output from SerAPI"
    parser.add_argument("--expect-unexpected", action="store_true",
                        default=False, help=EXPECT_UNEXPECTED_HELP)

    return parser


def post_process_arguments(args: argparse.Namespace) -> argparse.Namespace:
    """
    post process sertop arguments

    :param args: args parsed
    :return: new name space
    """
    for dirpath in args.coq_args_I:
        args.sertop_args.extend(("-I", dirpath))
    for pair in args.coq_args_R:
        args.sertop_args.extend(("-R", ",".join(pair)))
    for pair in args.coq_args_Q:
        args.sertop_args.extend(("-Q", ",".join(pair)))

    return args


def parse_args() -> argparse.Namespace:
    """
    parse argument

    :return: Namespace structure
    """
    args = build_parser().parse_args()
    return post_process_arguments(args)


EXTENSION_LATEX = ".tex"


def get_path_latex(output_dir: Path, name: str):
    return output_dir / (name + EXTENSION_LATEX)


def make_latex_file(content: str, path: Path):
    path.parent.mkdir(parents=True, exist_ok=True)
    with open(path, 'w') as file:
        file.write(content)


def main():
    from .Extractor import SnippetExtractor
    from .docutils import CoqToLatexReader, register_docutils
    args = parse_args()
    input_name = args.input.stem
    output_dir = args.output_dir / input_name

    # make latex
    print(f"Convert '{args.input}' to latex.")
    register_docutils(args.sertop_args)
    reader = CoqToLatexReader(args.input)
    print("Extract snippets.")
    snippet_extractor = SnippetExtractor(reader)

    # dump latex to debug
    if args.dump_complete_latex:
        path_latex = get_path_latex(args.dump_complete_latex_dir,
                                    input_name)
        print(f"Make complete latex file {path_latex}.")
        make_latex_file(reader.content_latex, path_latex)

    # write snippets files
    for snippet in snippet_extractor.extract():
        path = get_path_latex(output_dir, snippet.name)
        print(f"extract snippet '{snippet.name}', dump file {path}.")
        make_latex_file(str(snippet), path)
