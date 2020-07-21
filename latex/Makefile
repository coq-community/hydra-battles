all:  hydras.pdf

hydras.pdf: hydras.tex thebib.bib  chapter-introduction.tex	chapter-ordinals.tex chapter-hydras.tex	 \
chapter-ks.tex chapter-schutte.tex chapter-large-sets.tex \
chapter-termination.tex coqmacros.tex epsilon0.jpg
	lualatex hydras.tex; makeindex hydras.idx; lualatex hydras.tex; bibtex hydras; lualatex hydras.tex 


