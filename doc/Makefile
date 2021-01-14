all:  hydras.pdf

hydras.pdf: hydras.tex part-hydras.tex chapter-powers.tex chapter-primrec.tex thebib.bib  coqmacros.tex epsilon0.jpg
	lualatex hydras.tex; makeindex hydras.idx; lualatex hydras.tex; bibtex hydras; lualatex hydras.tex 


