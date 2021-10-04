snippets := \
	Schutte/Ex42a Schutte/Ex42b Schutte/Ex42c Schutte/Ex42d Schutte/Ex42e \
	Hprime/HprimeDef E0/Ex42 Pow/evalPow17LetIn

snippets_tex := $(patsubst %,snippets/%.tex,$(snippets))
snippet_dirs := $(dir $(snippets_tex))

default: paper.pdf

export coq_root := ../../theories
export snippets_root := ./snippets

include ../movies/config.mk
style := --pygments-style alectryon
alectryon += $(style)

include ../movies/targets.mk

assets/:
	$(PYTHON) $(driver) --frontend coq --backend assets --output-directory $@ $(style) -

paper.pdf: paper.tex ../thebib.bib assets/ $(snippet_dirs)
	@rm -f $(filter-out $(snippets_tex),$(shell find snippets/ -type f))
	pdflatex paper; bibtex paper; pdflatex paper; pdflatex paper

clean:
	latexmk -c
	rm -fr snippets
