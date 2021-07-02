
### Naive Makefile
##################

INPUT_DIR=../../theories/ordinals/
OPTIONS= -R ${INPUT_DIR} hydras
HYDRA_DIR= ${INPUT_DIR}Hydra
vpath %.v ${INPUT_DIR}Ackermann
vpath %.v ${INPUT_DIR}MoreAck
vpath %.v ${INPUT_DIR}Schutte
vpath %.v ${INPUT_DIR}Epsilon0
vpath %.v ${INPUT_DIR}Gamma0
vpath %.v ${INPUT_DIR}OrdinalNotations
vpath %.v ${INPUT_DIR}Prelude
vpath %.v ${INPUT_DIR}solutions_exercises

FILES = Ack.tex \
	AckNotPR.tex \
	primRec.tex \
	PrimRecExamples.tex \
	F_alpha.tex \
	F_omega.tex \
	Hydra_Definitions.tex \
	Hydra_Theorems.tex \
	Hydra_Examples.tex \
	Hydra_Lemmas.tex \
	Issue_Program.tex


all: $(FILES)

complete_latex/Issue_Program.tex: Issue_Program.v


%.tex : %.v
	python extract_snippets.py $< -d ${OPTIONS}

