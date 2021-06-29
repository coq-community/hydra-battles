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


def add_to_snippets(content: str, snippets: Dict[str, Snippet]) -> None:
    """
    add content to all snippet

    :param content: content to add
    :param snippets: snippet used
    """
    for snippet in snippets.values():
        snippet.add_content(content)


# text pattern
BEGIN_STATE = "begin"
END_STATE = "end"
TEXT_PATTERN = re.compile(rf"\s*\\({BEGIN_STATE}|{END_STATE})\{{txt}}")

# snippet pattern
SNIPPET_PATTERN = re.compile(rf".*\\PY{{c}}{{\(\*\~+({BEGIN_STATE}|{END_STATE})\~+snippet\~+(\w+)\~+\*\)}}")

BEGIN_ALECTRYON = "\\begin{alectryon}\n"
END_ALECTRYON = "\\end{alectryon}\n"

def extract_snippets_text(reader, begin_line: str,
                          open_snippets: Dict[str, Snippet], close_snippets: List[Snippet]) -> str:
    """
    This function is call by extract snippet if we are in text part.
    This function open new snippets found, or close it.
    This function end when text part is closed.

    :param reader: reader used
    :param begin_line: begin line used
    :param open_snippets: snippet not end
    :param close_snippets: snippet already end
    :return: content to add
    """
    content = BEGIN_ALECTRYON + begin_line  # TODO found other method
    for num, line in reader:
        # match open or close snippet
        if (match := SNIPPET_PATTERN.match(line)) is not None:
            state, name = match.groups()
            if state == BEGIN_STATE:
                SnippetAlreadyExistException.check(name, num, open_snippets, close_snippets)
                open_snippets[name] = Snippet(name)
            else:
                SnippetAlreadyCloseException.check(name, num, close_snippets)
                SnippetNotBeginException.check(name, num, open_snippets)
                open_snippets[name].add_content(END_ALECTRYON)
                close_snippets.append(open_snippets.pop(name))
            continue

        # add line to content
        content += line

        # match end of text
        if (match := TEXT_PATTERN.match(line)) is not None \
            and match.group(1) == END_STATE:
            return content
    raise Exception("not end to finish file")


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
        if (match := TEXT_PATTERN.match(line)) is not None:
            if match.group(1) == END_STATE:
                raise Exception(fr"error parsing match \"\end{{text}}\" in line {num} but no begin")
            line = extract_snippets_text(reader, line, open_snippets, close_snippets)

        add_to_snippets(line, open_snippets)

    if len(open_snippets) != 0:
        raise SnippetNotEndException(list(open_snippets.values()))

    return close_snippets
