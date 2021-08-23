from pathlib import Path

from .Reader import Reader


LATEX_TAG_BEGIN_FORMAT = "\\begin{{{tag}}}"
LATEX_TAG_END_FORMAT = "\\end{{{tag}}}"

def register_docutils(sertop_args):
    """
    setup docutils
    :param sertop_args: sertop arguments to used
    :return:
    """
    import alectryon.docutils
    alectryon.docutils.AlectryonTransform.SERTOP_ARGS = sertop_args
    alectryon.docutils.LONG_LINE_THRESHOLD = 88
    alectryon.docutils.setup()


def coq_rst_to_latex(source: str) -> str:
    """
    convert coq content to latex (please setup doctutils with register_docutils before)
    (function inspired by `_gen_docutils` in alectryon cli)
    :param source: source to convert
    :return: Exit code (int) and output (str).
    """
    from docutils.core import publish_string
    from docutils.readers.standalone import Reader
    from alectryon.cli import _gen_docutils
    from alectryon.docutils import LuaLatexWriter, RSTCoqParser as Parser

    settings_overrides = {
        'traceback': True,
        'embed_stylesheet': False,
        'stylesheet_path': None,
        'stylesheet_dirs': [],
        'alectryon_banner': False,
        'alectryon_vernums': False,
        'input_encoding': 'utf-8',
        'output_encoding': 'utf-8',
        'exit_status_level': 3,
    }

    output, _pub, exit_code = \
        _gen_docutils(source, None,
                      Parser, Reader, LuaLatexWriter,
                      settings_overrides)

    return exit_code, output

class CoqToLatexReader(Reader):
    DOCUMENT_BEGIN = LATEX_TAG_BEGIN_FORMAT.format(tag="document")
    DOCUMENT_END = LATEX_TAG_END_FORMAT.format(tag="document")

    def __init__(self, path_coq: Path):
        with open(path_coq, 'r') as file:
            self.content_coq = file.read()
        self.exit_code, self.content_latex = coq_rst_to_latex(self.content_coq)

    def __iter__(self):
        start = False
        for num, line in enumerate(self.content_latex.split('\n'), 1):
            if line == self.DOCUMENT_BEGIN:
                start = True
            elif line == self.DOCUMENT_END:
                return
            elif start:
                yield num, line + "\n"
