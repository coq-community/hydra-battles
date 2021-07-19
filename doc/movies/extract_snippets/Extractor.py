import re
from typing import AnyStr, Iterable, List, Match

from .Reader import Reader
from .Snippet import Snippet
from .snippetExceptions import \
    SnippetAlreadyCloseException, \
    SnippetAlreadyExistException, \
    SnippetNotBeginException, \
    SnippetNotEndWarning

BEGIN_STATE = "begin"
END_STATE = "end"
STATES_GROUP = fr"({BEGIN_STATE}|{END_STATE})"
NAME_GROUP = r"(\w+)"

LATEX_TAG_PATTERN = re.compile(rf"\s*\\{STATES_GROUP}(\[.*\])?{{{NAME_GROUP}}}(.*)")  # "\s*(\[.*])\\(begin|end){(\w+)}"
SNIPPET_PATTERN = re.compile(rf".*\\PY{{c}}{{\(\*\~*{STATES_GROUP}\~+snippet\~+{NAME_GROUP}\~*\*\)}}")


class SnippetExtractor:
    def __init__(self, reader: Reader):
        self.reader = reader
        self.__snippet_open = {}
        self.__snippet_close = []
        self.stack_tag = []

    @staticmethod
    def _list_names(snippets: Iterable[Snippet]) -> Iterable[str]:
        """
        get list of name sinppets
        :param snippets: list of snipepts
        :return: itterable
        """
        return map(lambda snippet: snippet.name, snippets)

    def _match_tag(self, match: Match[AnyStr], line_num: int) -> None:
        statement, _, tag, after = match.groups()
        if statement == BEGIN_STATE:
            self.stack_tag.append(tag)
            match = LATEX_TAG_PATTERN.match(after)
            if match is not None:
                self._match_tag(match, line_num)

        else:
            last_tag = self.stack_tag.pop()
            if last_tag != tag:
                raise Exception(f"tag '{tag}' close before '{last_tag}' at line {line_num}.")

    def _open_snippet(self, snippet_name: str, line_number: int) -> None:
        """
        check if new snippet not already exist
        and open snippet

        :param snippet_name: name to check
        :param line_number: line number found this name
        :raise: SnippetAlreadyExistException if already open or close
        """
        # check
        if snippet_name in self._list_names(self.__snippet_close) or \
            snippet_name in self._list_names(self.__snippet_open.values()):
            raise SnippetAlreadyExistException(snippet_name, line_number)

        # add snippet in open dict
        self.__snippet_open[snippet_name] = Snippet(snippet_name, self.stack_tag)

    def _close_snippet(self, snippet_name: str, line_number: int) -> None:
        """
        check if snippet not already closed or
                 snippet close in open snippets
        and close snippet

        :param snippet_name: name to check
        :param line_number: line number found this name
        :raise: SnippetAlreadyCloseException if exist in close
        :raise: SnippetNotExistException if not in open
        """
        # check
        if snippet_name in self._list_names(self.__snippet_close):
            raise SnippetAlreadyCloseException(snippet_name, line_number)

        elif snippet_name not in self._list_names(self.__snippet_open.values()):
            raise SnippetNotBeginException(snippet_name, line_number)

        # move snippet open dict to close list
        snippet = self.__snippet_open.pop(snippet_name)
        snippet.close(self.stack_tag)
        self.__snippet_close.append(snippet)

    def _match_snippet(self, match: Match[AnyStr], line_num: int):
        """
        call if match snippet, to open or close snippet

        :param statement:
        :param snippet_name:
        :param line_num:
        :return:
        """
        statement, snippet_name = match.groups()
        if statement == BEGIN_STATE:
            self._open_snippet(snippet_name, line_num)
        else:  # end state
            self._close_snippet(snippet_name, line_num)

    def _add_snippets_open(self, line: str):
        for snippet in self.__snippet_open.values():
            snippet.add_content(line)

    def extract(self) -> List[Snippet]:
        """
        run extract snippets
        :return: snippets
        """

        for num, line in self.reader:
            match = LATEX_TAG_PATTERN.match(line)
            if match is not None:
                self._match_tag(match, line_num=num)

            else:
                match = SNIPPET_PATTERN.match(line)
                if match is not None:
                    self._match_snippet(match, line_num=num)
                    continue

            self._add_snippets_open(line)

        # warning if all snippet not closed
        if self.__snippet_open:
            raise SnippetNotEndWarning(*self.__snippet_open.values())

        return self.snippets

    @property
    def snippets(self):
        return self.__snippet_close
