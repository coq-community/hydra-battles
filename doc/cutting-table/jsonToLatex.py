#!/usr/bin/env python3
from src.cli import parse_args
from src.json import coq_to_json
from src.snippet import Snippet

if __name__ == '__main__':
    args = parse_args()
    for coq_file in args.inputs:
        json_path = coq_to_json(args.output_dir, coq_file)
        snippets = Snippet(json_path).snippets
        print(snippets)
    # main()
