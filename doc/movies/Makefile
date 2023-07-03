export coq_root := ../../theories
export snippets_root := ./snippets
assets_root := $(snippets_root)/assets

include config.mk

default: all

targets.mk: gen_targets.py
	@$(PYTHON) gen_targets.py "$(coq_root)" "$(snippets_root)" > "$@"

include targets.mk

.PHONY: all clean

all: $(targets)
	@$(PYTHON) ./driver.py --frontend coq --backend assets --output-directory $(assets_root) -

clean:
	rm -fr $(snippets_root) 
	rm -f targets.mk
