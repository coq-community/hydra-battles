#!/usr/bin/env python3
from src.cli import parse_args
from src.json import coq_to_json, json_to_latex, get_annotate_json
from src.snippet import Snippet

LATEX_EXTENSION = ".tex"

if __name__ == '__main__':
    args = parse_args()
    for coq_file in args.inputs:
        json_path = coq_to_json(args.output_dir, coq_file)
        directory = json_path.parent
        annotate_json = get_annotate_json(json_path)
        snippets = Snippet(annotate_json).snippets
        for name, annotate_json in snippets.items():
            path = directory / (name + LATEX_EXTENSION)
            json_to_latex(annotate_json, path)
            print(f"create latex file: {path}")
