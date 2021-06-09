from pathlib import Path
from alectryon.json import annotated_of_json
import json


def get_annotate_json(json_path: Path):
    """
    get annotate json with alectryon

    :param json_path: path of json file to read
    :return: json annotate json
    """

    with open(json_path, "r") as read_file:
        return annotated_of_json(json.load(read_file, strict=False))
