from pathlib import Path

COQ_EXTENSION = ".v"
JSON_EXTENSION = ".io.json"


def get_annotate_json(json_path: Path) -> dict:
    """
    get annotate json with alectryon

    :param json_path: path of json file to read
    :return: json annotate json
    """
    from alectryon.json import annotated_of_json
    import json

    with open(json_path, "r") as read_file:
        return annotated_of_json(json.load(read_file, strict=False))


def _alectryon_wrapper_json(input_file: Path, output_file: Path):
    """
    call alectryon script

    :param output_file: output file name
    :return:
    """
    from alectryon.cli import build_parser, \
        post_process_arguments, \
        process_pipelines

    options = f"{input_file} --frontend coq --backend json -o {output_file}"

    parser = build_parser()
    args = post_process_arguments(parser,
                                  parser.parse_args(options.split()))

    process_pipelines(args)


def coq_to_json(output_dir: Path, coq_file_path: Path) -> Path:
    name = coq_file_path.stem
    path_dir = output_dir / name
    path_dir.mkdir(exist_ok=True)

    json_file_path = path_dir / (name + JSON_EXTENSION)

    _alectryon_wrapper_json(coq_file_path, json_file_path)

    return json_file_path
