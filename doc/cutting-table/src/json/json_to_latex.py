from pathlib import Path

from alectryon.latex import LatexGenerator
from alectryon.pygments import highlight_latex

LATEX_GENERATOR = LatexGenerator(highlight_latex)


def json_to_latex(annotated_json: dict, path: Path) -> None:
    """
    transform a json to latex

    :param annotated_json: json to transform
    """
    with open(path, 'w') as file:
        for ltx in LATEX_GENERATOR.gen(annotated_json):
            file.write(ltx)
