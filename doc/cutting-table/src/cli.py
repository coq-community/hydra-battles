import argparse
from pathlib import Path


def build_parser() -> argparse.ArgumentParser:
    """
    build parser

    :return: Argument parser
    """
    DESCRIPTION = "Extract snippet in latex file generate by alectryon."
    parser = argparse.ArgumentParser(DESCRIPTION)

    INPUT_FILES_HELP = "latex file '.tex'"
    parser.add_argument("input",
                        type=Path,
                        help=INPUT_FILES_HELP)

    OUPUT_DIR_HELP = "output directory"
    parser.add_argument("-o", "--output-dir",
                        default=Path("."),
                        type=Path,
                        help=OUPUT_DIR_HELP)
    return parser


def parse_args() -> argparse.Namespace:
    """
    parse argument

    :return: Namespace structure
    """
    return build_parser().parse_args()


def main():
    from .extract import extract_snippets
    args = parse_args()
    list_snippets = extract_snippets(args.input)
    output_dir = args.output_dir
    if list_snippets and not output_dir.exists():
        print(f"Directory {output_dir} not exist, create it.")
        output_dir.mkdir()

    for snippet in list_snippets:
        print(f"extract snippet '{snippet.name}', dump file {snippet.get_path(output_dir)}.")
        snippet.write(output_dir)
