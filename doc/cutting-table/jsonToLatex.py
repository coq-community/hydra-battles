#!/usr/bin/env python3
import json
import sys
from os.path import join, dirname
from pprint import pprint
movie_file = sys.argv[1]

root = join(dirname(__file__), "..")
sys.path.insert(0, root)
sys.path.insert(0, '/Users/casteranpierre/alectryon')

with open(movie_file, "r") as read_file:
    movie =json.load(read_file, strict=False)

# data =  movie[0] 

def latex_of_movie():
    from alectryon.json import annotated_of_json
    from alectryon.latex import LatexGenerator
    from alectryon.pygments import highlight_latex
    annotated = annotated_of_json(movie)
    for ltx in LatexGenerator(highlight_latex).gen(annotated):
      #   print("<latex>")
        print(ltx)
      #   print("</latex>")

def main():
    latex_of_movie()

if __name__ == '__main__':
    main()       
