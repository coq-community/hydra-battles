The current Makefile assumes the included snippets come from the compilation by `make pdf` of the all documentation. This is certanily very inefficient, in particular after a checkout from master.

Todo: Once the set of included snippets is definitively fixed, copy them into this directory and change the `inputsnippets` command in `paper.tex`(remove the `../movies/snippets/`prefix).