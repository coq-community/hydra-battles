from pathlib import Path

from alectryon.cli import build_parser, \
    post_process_arguments, \
    process_pipelines

COQ_EXTENSION = ".v"
JSON_EXTENSION = ".io.json"

R_FLAG = "-R ../../theories/ordinals hydras"  # FIXME


def _alectryon_wrapper_json(input_file: Path, output_file: Path) -> None:
    """
    call alectryon script

    :param output_file: output file name
    """

    options = f"{input_file} --frontend coq --backend json -o {output_file} " \
              f"{R_FLAG}"

    parser = build_parser()
    args = post_process_arguments(parser, parser.parse_args(options.split()))

    process_pipelines(args)


def coq_to_json(output_dir: Path, coq_file_path: Path) -> Path:
    """
    convert coq '.v' file to 'io.json' file.

    :param output_dir: output directory to make new directory with name of coq file
    :param coq_file_path: coq file to convert
    :return: path of json file
    """
    name = coq_file_path.stem
    path_dir = output_dir / name
    path_dir.mkdir(exist_ok=True)

    json_file_path = path_dir / (name + JSON_EXTENSION)

    _alectryon_wrapper_json(coq_file_path, json_file_path)

    return json_file_path
