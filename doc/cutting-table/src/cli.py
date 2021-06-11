import argparse
from pathlib import Path

def build_parser() -> argparse.ArgumentParser:
    """
    build parser

    :return: Argument parser
    """
    DESCRIPTION = ""  # TODO
    parser = argparse.ArgumentParser(DESCRIPTION)

    INPUT_FILES_HELP = "coq files '.v'"
    parser.add_argument("inputs", nargs='+',
                        type=Path,
                        help=INPUT_FILES_HELP)

    OUPUT_DIR_HELP = "output directory"
    parser.add_argument("-o", "--output-dir",
                        default=Path("."),
                        type=Path,
                        help=OUPUT_DIR_HELP)

    REBUILD_HELP = "rebuild files (WIP)"  # FIXME
    parser.add_argument("-r", "--rebuild",
                        default="store_true",
                        help=REBUILD_HELP)

    THREAD_HELP = "set number of maximum workers (WIP)"  # FIXME
    parser.add_argument("-t", "--threads",
                        default=None,
                        type=int,
                        help=THREAD_HELP)

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


LATEX_EXTENSION = ".tex"


def main():
    from .annotate import coq_file_to_annotated, annotate_to_latex
    from .snippet import Snippet
    args = parse_args()

    for coq_file in args.inputs:
        annotated = coq_file_to_annotated(coq_file, args.sertop_args)
        for name, annotate_json in Snippet(annotated).snippets.items():
            path_latex: Path = args.output_dir / coq_file.stem / (name + LATEX_EXTENSION)

            print(f"From file \"{coq_file}\" with snippet \"{name}\", create latex file: {path_latex}.")
            path_latex.parent.mkdir(exist_ok=True)
            annotate_to_latex(annotate_json, path_latex)
