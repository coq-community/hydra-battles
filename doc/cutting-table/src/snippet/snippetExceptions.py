from pathlib import Path
from typing import List


class SnippetException(Exception):
    pass


class SnippetAlreadyExistException(SnippetException):
    """
    Raise in snippet if 2 snippet with same name in file.
    """

    def __init__(self, name_snippet: str):
        super().__init__(f"snippet \"{name_snippet}\" already exist")


class SnippetAlreadyCloseException(SnippetException):
    """
    Raise if snippet is already close.
    """

    def __init__(self, name_snippet: str):
        super().__init__(f"snippet \"{name_snippet}\" already close")


class SnippetNotExistException(SnippetException):
    """
    Raise if snippet not exist.
    """

    def __init__(self, name_snippet: str):
        super().__init__(f"snippet \"{name_snippet}\" not exist (cannot be close).")


class SnippetNotEndException(SnippetException):
    """
    Raise if snippet is have not end.
    """

    def __init__(self, names: List[str]):
        super().__init__(f"snippet \"{','.join(names)}\" never close")
