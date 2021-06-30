from typing import Dict, Iterable, List
from .Snippet import Snippet


class SnippetException(Exception):
    def __init__(self, prelude: str, line_number: int = None):
        if line_number is None:
            super().__init__(prelude)
        else:
            super().__init__(f"{prelude}, at line {line_number}.")


class SnippetAlreadyExistException(SnippetException):
    """
    Raise in snippet if 2 snippet with same name in file.
    """

    def __init__(self, name_snippet: str, line_number: int):
        super().__init__(f"Snippet \"{name_snippet}\" already exist", line_number)

    @staticmethod
    def check(name: str, line_number: int, open_snippets: Dict[str, Snippet], close_snippets: List[Snippet]) -> None:
        """
        check if new snippet not already exist

        :param name: name to check
        :param line_number: line number found this name
        :param open_snippets: snippets already open
        :param close_snippets: snippet already closed
        :raise: SnippetAlreadyExistException if already open or close
        """
        list_names = set(open_snippets.keys()) | set(map(lambda x: x.name, close_snippets))
        if name in list_names:
            raise SnippetAlreadyExistException(name, line_number)


class SnippetAlreadyCloseException(SnippetException):
    """
    Raise if snippet is already close.
    """

    def __init__(self, name_snippet: str, line_number: int):
        super().__init__(f"Snippet \"{name_snippet}\" already close", line_number)

    @staticmethod
    def check(name: str, line_number: int, close_snippets: List[Snippet]) -> None:
        """
        check if snippet not already closed

        :param name: name to check
        :param line_number: line number found this name
        :param close_snippets: snippet already closed
        :raise: SnippetAlreadyCloseException if exist in close
        """
        list_names = set(map(lambda x: x.name, close_snippets))
        if name in list_names:
            raise SnippetAlreadyCloseException(name, line_number)


class SnippetNotBeginException(SnippetException):
    """
    Raise if snippet not exist.
    """

    def __init__(self, name_snippet: str, line_number: int):
        super().__init__(f"Snippet \"{name_snippet}\" not begin (cannot be closed)", line_number)

    @staticmethod
    def check(name: str, line_number: int, open_snippets: Dict[str, Snippet]) -> None:
        """
        check if snippet close in open snippets

        :param name: name to check
        :param line_number: line number found this name
        :param open_snippets: snippets already open
        :raise: SnippetNotExistException if not in open
        """
        list_names = set(open_snippets.keys())
        if name not in list_names:
            raise SnippetNotBeginException(name, line_number)


class SnippetNotEndException(SnippetException):
    """
    Raise if snippet is have not end.
    """

    def __init__(self, *snippets: Iterable[Snippet]):
        names = ",".join(snippet.name for snippet in snippets)
        super().__init__(f"Snippets \"{names}\" never close")
