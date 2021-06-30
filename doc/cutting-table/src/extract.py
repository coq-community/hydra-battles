from pathlib import Path
from typing import Dict, List
import re
from .Snippet import Snippet
from .snippetExceptions import \
    SnippetNotBeginException, \
    SnippetAlreadyCloseException, \
    SnippetAlreadyExistException, \
    SnippetNotEndException


def get_reader(path: Path) -> str:
    """
    reader who yield lines

    :param path: path of file to read
    :return: line read
    """
    with open(path, 'r') as file:
        yield from enumerate(file, 1)


def add_all_snippets(content: str, snippets: Dict[str, Snippet]) -> None:
    """
    add content to all snippet

    :param content: content to add
    :param snippets: snippet used
    """
    for snippet in snippets.values():
        snippet.add_content(content)


# snippet pattern
BEGIN_STATE = "begin"
END_STATE = "end"
SNIPPET_PATTERN = re.compile(rf"\s*\(\*\s*({BEGIN_STATE}|{END_STATE})\s+snippet\s+(\w+)\s*\*\)")


def extract_snippets(path: Path) -> List[Snippet]:
    """
    parse latex file and return a list of snippet
    :param path: path of file to extract snippets
    :return: list of snippets
    """
    reader = get_reader(path)
    open_snippets = {}
    close_snippets = []
    for num, line in reader:
        if (match := SNIPPET_PATTERN.match(line)) is not None:
            state, name = match.groups()
            if state == BEGIN_STATE:
                SnippetAlreadyExistException.check(name, num, open_snippets, close_snippets)
                open_snippets[name] = Snippet(name)
            else:  # end state
                SnippetAlreadyCloseException.check(name, num, close_snippets)
                SnippetNotBeginException.check(name, num, open_snippets)
                close_snippets.append(open_snippets.pop(name))
            continue
        add_all_snippets(line, open_snippets)

    if open_snippets:
        raise SnippetNotEndException(open_snippets.values())

    return close_snippets
