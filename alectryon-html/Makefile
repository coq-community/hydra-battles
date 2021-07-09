
### Naive Makefile
##################

OPTIONS=  --frontend coqdoc --output-directory . -R ../theories/ordinals hydras
INPUTDIR=../theories/ordinals
vpath %.v ${INPUTDIR}/Hydra
vpath %.v ${INPUTDIR}/Ackermann
vpath %.v ${INPUTDIR}/MoreAck
vpath %.v ${INPUTDIR}/Schutte
vpath %.v ${INPUTDIR}/Epsilon0
vpath %.v ${INPUTDIR}/Gamma0
vpath %.v ${INPUTDIR}/OrdinalNotations
vpath %.v ${INPUTDIR}/Prelude
vpath %.v ${INPUTDIR}/solutions_exercises

FILES= Ack.html\
       AckNotPR.html \
       F_alpha.html \
       F_omega.html \
       Hydra_Definitions.html \
       Hydra_Examples.html \
       Hydra_Lemmas.html \
       Hydra_Theorems.html \
       PrimRecExamples.html \
       primRec.html \


all: $(FILES)


clean:
	@$(RM) -f $(FILES)


%.html : %.v
	@alectryon.py $(OPTIONS) $<

.PHONY: all clean
