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


def make_latex(input_file: Path, sertop_args):
    from .Extractor import SnippetExtractor
    from .docutils import CoqToLatexReader, register_docutils
    print(f"Convert '{input_file}' to latex.")
    register_docutils(sertop_args)
    reader = CoqToLatexReader(input_file)
    print("Extract snippets.")
    return SnippetExtractor(reader), reader


def copy_asset(output_dir: Path, dir_name='assets'):
    from alectryon.cli import copy_assets
    from alectryon.latex import ASSETS
    from shutil import copy

    STY = ASSETS.ALECTRYON_STY + ASSETS.PYGMENTS_STY
    assets = [(ASSETS.PATH, asset) for asset in STY]

    output_dir = output_dir / dir_name
    output_dir.mkdir(exist_ok=True)

    copy_assets(None, assets, copy, output_dir)
    print(f"copy assets {STY} in {output_dir}")


def main():
    args = parse_args()
    input_name = args.input.stem
    output_dir = args.output_dir / input_name

    snippet_extractor, reader = make_latex(args.input, args.sertop_args)

    # dump latex to debug
    if args.dump_complete_latex:
        path_latex = get_path_latex(args.dump_complete_latex_dir,
                                    input_name)
        print(f"Make complete latex file {path_latex}.")
        make_latex_file(reader.content_latex, path_latex)

    # write snippets files
    snippets = snippet_extractor.extract()
    for snippet in snippets:
        path = get_path_latex(output_dir, snippet.name)
        print(f"extract snippet '{snippet.name}', dump file {path}.")
        make_latex_file(str(snippet), path)

    if snippets:
        copy_asset(args.output_dir)
