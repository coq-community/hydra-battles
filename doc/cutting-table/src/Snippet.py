from pathlib import Path


class Snippet:
    LATEX_EXTENSION = ".tex"

    def __init__(self, name: str):
        self.__name = name
        self.content = ""

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
        self.content += content_to_add

    def __str__(self) -> str:
        return self.content
