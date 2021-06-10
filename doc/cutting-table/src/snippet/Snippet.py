from typing import Dict, Optional, Tuple
from alectryon.core import Text
import re

from .snippetExceptions import SnippetNotExistException, \
    SnippetAlreadyCloseException, \
    SnippetAlreadyExistException, \
    SnippetNotEndException


class Snippet:
    """
    find snippet and make annotate structure for all snippet find.

    Use run to compute snippet
    and snippets to get new structures
    """
    BEGIN_STATE = "begin"
    END_STATE = "end"
    PATTERN = re.compile(rf"\(\*\s*({BEGIN_STATE}|{END_STATE})\s+snippet\s+(\w+)\s*\*\)")

    def __init__(self, annotate_json):
        self.annotate = annotate_json
        self.next = None
        self.__in_process = {}
        self.__finish = None

    def run(self) -> None:
        """
        find all snippet and make dictionary
        """
        if self.__finish is not None:
            return
        self.__finish = {}

        for elm in self.annotate[0]: # FIXME an recursive approch can fix this problem / But check how json to latex work (and do testing)
            self.__update(elm)

        snippet_not_close = list(self.__in_process.keys())
        if snippet_not_close:
            raise SnippetNotEndException(snippet_not_close)

    def __update(self, element) -> None:
        """
        add element to al snippets
        update all snippets

        :param element: element to add
        """
        if isinstance(element, Text):
            self.__update_with_text(element)
            return

        else:
            for key in self.__in_process.keys():
                self.__in_process[key].append(element)


    def __update_with_text(self, text: Text):
        dict_match, string = self.list_pattern(text.contents)
        names_already_update = set()
        for name, (begin, end) in dict_match.items():
            if (name in list(self.__finish)) or (begin is not None and name in list(self.__in_process)):
                raise SnippetAlreadyExistException(name)
            elif name in list(self.__finish) and end is not None:
                raise SnippetAlreadyCloseException(name)
            elif begin is None and end is not None and not name in list(self.__in_process):
                raise SnippetNotExistException(name)
            elif begin is not None:
                self.__in_process[name] = []

            start_i = (begin, 0)[begin is None]
            end_i = (end, -1)[end is None]

            text = Text(string[start_i:end_i])
            self.__in_process[name].append(text)

            if end is not None:
                self.__finish[name] = [self.__in_process.pop(name)]
            else:  # construct list of name already have snippet
                names_already_update.add(name)

        # update other snippet
        text = Text(string)
        to_update = set(self.__in_process.keys()) - names_already_update
        for key in to_update:
            self.__in_process[key].append(text)

    @staticmethod
    def list_pattern(string: str) -> Tuple[Dict[str, Tuple[Optional[int], Optional[int]]], str]:
        """
        list pattern found.

        :param string: string to finds patterns
        :return {name: (index_begin, index_end)}, new string
        """

        dict_name = {}
        while (match := Snippet.PATTERN.search(string)) is not None:
            state, name = match.groups()
            index_start = match.start()
            string = string[:match.start()] + string[match.end():]
            if state == Snippet.BEGIN_STATE:
                if name in list(dict_name.keys()):
                    raise SnippetAlreadyExistException(name)

                dict_name[name] = (index_start, None)
            else:
                index_begin, index_end = dict_name.get(name, (None, None))
                if index_end is not None:
                    raise SnippetAlreadyExistException(name)

                dict_name[name] = (index_begin, index_start)

        return dict_name, string

    @property
    def snippets(self) -> dict:
        """
        get all snippet

        :return: dictionary with all snippet
        """
        if self.__finish is None:
            self.run()
        return self.__finish

    def get_snippet(self, name: str):
        """
        getter snippet

        :param name:  name of snippet to get
        :return: annotate json
        """
        return self.snippets[name]
