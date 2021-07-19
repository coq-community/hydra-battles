
### Naive Makefile
##################

INPUT_DIR=../../theories/ordinals
OPTIONS= -R ${INPUT_DIR} hydras
vpath %.v ${INPUT_DIR}/Hydra
vpath %.v ${INPUT_DIR}/Ackermann
vpath %.v ${INPUT_DIR}/MoreAck
vpath %.v ${INPUT_DIR}/Schutte
vpath %.v ${INPUT_DIR}/Epsilon0
vpath %.v ${INPUT_DIR}/Gamma0
vpath %.v ${INPUT_DIR}/OrdinalNotations
vpath %.v ${INPUT_DIR}/Prelude
vpath %.v ${INPUT_DIR}/solutions_exercises

COQ_FILES = Ack.v               \
	    AckNotPR.v          \
	    primRec.v           \
	    PrimRecExamples.v   \
	    F_alpha.v           \
	    F_omega.v           \
	    Hydra_Definitions.v \
	    Hydra_Theorems.v    \
	    Hydra_Examples.v    \
	    Hydra_Lemmas.v      \

TEX_FILE = $(COQ_FILES:.v=.tex)

SNIPPET_OUTPUT = ./snippets/

.PHONY: all
all: $(TEX_FILE)


.PHONY: clean
clean:
	@${RM} ${TEX_FILE}
	@${RM} -r ${SNIPPET_OUTPUT}

%.tex : %.v
	@python3 extract_snippets.py $< -o ${SNIPPET_OUTPUT} -d ${OPTIONS}
