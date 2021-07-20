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
    from alectryon.docutils import setup, AlectryonTransform
    AlectryonTransform.SERTOP_ARGS = sertop_args
    setup()


def coq_rst_to_latex(source: str) -> str:
    """
    convert coq content to latex (please setup doctutils with register_docutils before)
    (function inspired by `_gen_docutils` in alectryon cli)
    :param source: source to conver
    :return:
    """
    from alectryon.docutils import LatexWriter
    from docutils.core import publish_string
    from alectryon.docutils import \
        RSTCoqParser as Parser, \
        RSTCoqStandaloneReader as Reader

    settings_overrides = {
        'traceback': True,
        'embed_stylesheet': False,
        'stylesheet_path': None,
        'stylesheet_dirs': [],
        'alectryon_banner': False,
        'alectryon_vernums': False,
        'input_encoding': 'utf-8',
        'output_encoding': 'utf-8',
    }

    parser = Parser()
    return publish_string(
        source=source.encode("utf-8"),
        reader=Reader(parser), reader_name=None,
        parser=parser, parser_name=None,
        writer=LatexWriter(), writer_name=None,
        settings=None, settings_spec=None,
        settings_overrides=settings_overrides, config_section=None,
        enable_exit_status=True).decode("utf-8")


class CoqToLatexReader(Reader):
    DOCUMENT_BEGIN = LATEX_TAG_BEGIN_FORMAT.format(tag="document")
    DOCUMENT_END = LATEX_TAG_END_FORMAT.format(tag="document")

    def __init__(self, path_coq: Path):
        with open(path_coq, 'r') as file:
            self.content_coq = file.read()
        self.content_latex = coq_rst_to_latex(self.content_coq)

    def __iter__(self):
        start = False
        for num, line in enumerate(self.content_latex.split('\n'), 1):
            if line == self.DOCUMENT_BEGIN:
                start = True
            elif line == self.DOCUMENT_END:
                return
            elif start:
                yield num, line + "\n"
