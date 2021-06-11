from typing import List

from alectryon.core import annotate
from pathlib import Path

annotated_t = List[List]


def coq_file_to_annotated(path_coq_file: Path, sertop_args=()) -> annotated_t:
    """
    annotate file coq file

    :param path_coq_file: path of coq file to use ('.v' file)
    :return: annotate content
    """
    with open(path_coq_file, 'r') as file:
        return annotate([file.read()], sertop_args)


LATEX_GENERATOR = None


def _get_latex_generator():
    """
    getter latex generator (lazy)
    :return: latex generator
    """
    global LATEX_GENERATOR
    if LATEX_GENERATOR is None:
        from alectryon.latex import LatexGenerator
        from alectryon.pygments import highlight_latex
        LATEX_GENERATOR = LatexGenerator(highlight_latex)
    return LATEX_GENERATOR


def annotate_to_latex(annotated_content: annotated_t, latex_file: Path):
    """
    transform annotated content to latex file

    :param annotated_content: annotated content to convert
    :param latex_file: path of latex file to product
    """
    with open(latex_file, 'w') as file:
        for ltx in _get_latex_generator().gen(annotated_content):
            file.write(str(ltx))
