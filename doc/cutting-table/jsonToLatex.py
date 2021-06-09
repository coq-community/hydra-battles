#!/usr/bin/env python3
from src import parse_args
from src.io_json import coq_to_json, get_annotate_json


def latex_of_movie(movie):
    from alectryon.json import annotated_of_json
    from alectryon.latex import LatexGenerator
    from alectryon.pygments import highlight_latex
    annotated = annotated_of_json(movie)
    for ltx in LatexGenerator(highlight_latex).gen(annotated):
        print(ltx)


if __name__ == '__main__':
    args = parse_args()
    for coq_file in args.inputs:
        json_path = coq_to_json(args.output_dir, coq_file)
        json = get_annotate_json(json_path)
        print("------")
        print(json)
        print("------")
    # main()
