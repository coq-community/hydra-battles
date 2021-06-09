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

    return parser


def parse_args() -> argparse.Namespace:
    """
    parse argument

    :return: Namespace structure
    """
    return build_parser().parse_args()
