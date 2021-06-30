import re


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


PATTERN_BODY = re.compile(r"\\begin\{document\}(.+)\\end\{document\}")
BEGIN_DOC = r"\begin{document}"
END_DOC = r"\end{document}"
def coq_rst_to_latex_snippet(source: str):
    latex_source = coq_rst_to_latex(source)
    start_index = latex_source.find(BEGIN_DOC) + len(BEGIN_DOC)
    end_index = latex_source.find(END_DOC, start_index)
    return latex_source[start_index:end_index]
