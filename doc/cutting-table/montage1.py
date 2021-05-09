#!/usr/bin/env python3
import json
import sys
from os.path import join, dirname
from pprint import pprint

root = join(dirname(__file__), "..")
sys.path.insert(0, root)
sys.path.insert(0, '/Users/casteranpierre/alectryon')

# import alectryon.core
# alectryon.core.DEBUG = True

def api_annotate():
    from alectryon.core import annotate
    annotated = annotate(["Check 1."], ("-Q", "{},logical_name".format(root)))
    pprint(annotated)

def annotated_to_json():
    from alectryon.core import annotate
    from alectryon.json import json_of_annotated
    annotated = annotate([r"Goal True /\ True. split. ", "all: eauto."],
                         ("-Q", "{},logical_name".format(root)))
    print(json.dumps(json_of_annotated(annotated)))

#Todo  get JS  as an argument on the command line

JS = """
[[{
            "_type": "sentence",
            "contents": "Inductive Hydra : Set :=\n|  node :  Hydrae -> Hydra\nwith Hydrae : Set :=\n| hnil : Hydrae\n| hcons : Hydra -> Hydrae -> Hydrae.",
            "messages": [],
            "goals": []
        }]]
"""


# print(JS) # type of JS ?


def latex_of_movie():
    from alectryon.json import annotated_of_json
    from alectryon.latex import LatexGenerator
    from alectryon.pygments import highlight_latex
    annotated = annotated_of_json(json.loads(JS, strict=False))
    for ltx in LatexGenerator(highlight_latex).gen(annotated):
      #  print("<latex>")
        print(ltx)
      #  print("</latex>")

def main():
#    api_annotate()
    latex_of_movie()

if __name__ == '__main__':
    main()
