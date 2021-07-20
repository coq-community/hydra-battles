from typing import List

from .docutils import LATEX_TAG_BEGIN_FORMAT, LATEX_TAG_END_FORMAT
from .snippetExceptions import SnippetException


class Snippet:
    BEGIN_TEMPLATE = LATEX_TAG_BEGIN_FORMAT
    END_TEMPLATE = LATEX_TAG_END_FORMAT
    INDENT = "  "

    def __init__(self, name: str, tags=[]):
        self.__name = name
        self.content = ""
        self._add_tags(self.BEGIN_TEMPLATE, tags)
        self.open = True

    @property
    def name(self) -> str:
        """
        name of snippet
        :return: str
        """
        return self.__name

    def add_content(self, content_to_add: str) -> None:
        """
        add new line to content

        :param content_to_add: content added
        :return: None
        """
        if self.is_close():
            raise SnippetException(f"Snippet {self.name} already closed.")
        self.content += content_to_add

    def _add_tags(self, template: str, tags: List[str], reverse: bool = False):
        indent_func = lambda i: self.INDENT * i
        if reverse:
            max_i = len(tags) - 1
            indent_func = lambda i: self.INDENT * (max_i - i)
            tags = reversed(tags)

        self.content += "\n".join(indent_func(i) + template.format(tag=tag) for i, tag in enumerate(tags)) + "\n"

    def close(self, tags: List[str]) -> None:
        """
        close snippet
        """
        self._add_tags(self.END_TEMPLATE, tags, reverse=True)
        self.open = False

    def is_close(self) -> bool:
        """
        True if Snippet is closed
        :return: bool
        """
        return not self.open

    def __str__(self) -> str:
        return self.content
