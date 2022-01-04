PYTHON ?= python3

coq_flags := \
	-R $(coq_root)/ordinals hydras \
	-R $(coq_root)/additions additions \
	-R $(coq_root)/gaia gaia_hydras

alectryon_flags := \
	--frontend coq --backend snippets-hydras $(coq_flags)

driver := $(dir $(lastword $(MAKEFILE_LIST)))/driver.py

alectryon = \
	$(PYTHON) $(driver) $(alectryon_flags) --output-directory "$@"
