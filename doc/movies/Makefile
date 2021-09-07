PYTHON ?= python3

export coq_root := ../../theories
export snippets_root := ./snippets
assets_root := $(snippets_root)/assets

default: all

targets.mk:
	@$(PYTHON) gen_targets.py "$(coq_root)" "$(snippets_root)" > "$@"

include targets.mk

coq_flags := -R $(coq_root)/ordinals hydras -R $(coq_root)/additions additions -R $(coq_root)/gaia gaia_hydras

alectryon_flags := --frontend coq --backend snippets-hydras $(coq_flags)

alectryon = $(PYTHON) ./driver.py $(alectryon_flags) --output-directory "$@"

.PHONY: all clean targets.mk

all: $(targets)
	@$(PYTHON) ./driver.py --frontend coq --backend assets --output-directory $(assets_root) -

clean:
	rm -fr $(snippets_root)
