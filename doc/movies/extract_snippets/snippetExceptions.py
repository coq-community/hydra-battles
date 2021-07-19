from typing import Iterable



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


class SnippetAlreadyCloseException(SnippetException):
    """
    Raise if snippet is already close.
    """

    def __init__(self, name_snippet: str, line_number: int):
        super().__init__(f"Snippet \"{name_snippet}\" already close", line_number)


class SnippetNotBeginException(SnippetException):
    """
    Raise if snippet not exist.
    """

    def __init__(self, name_snippet: str, line_number: int):
        super().__init__(f"Snippet \"{name_snippet}\" not begin (cannot be closed)", line_number)


class SnippetNotEndWarning(Warning):
    """
    Raise if snippet is have not end.
    """

    def __init__(self, *snippets: Iterable['Snippet']):
        names = ",".join(snippet.name for snippet in snippets)
        super().__init__(f"Snippets \"{names}\" never close")
