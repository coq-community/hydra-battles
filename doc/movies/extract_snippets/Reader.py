from typing import Tuple
from abc import abstractmethod


class Reader:
    """
    Read line by line
    """

    @abstractmethod
    def __iter__(self) -> Tuple[int, str]:
        """
    return tuple with line number and line
    :yield:
    """
        pass
