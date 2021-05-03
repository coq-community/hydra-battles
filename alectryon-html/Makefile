
### Naive Makefile
##################

OPTIONS=  --frontend coqdoc --output-directory . -R ../theories/ordinals hydras
INPUTDIR=../theories/ordinals
vpath %.v ../theories/ordinals/Hydra
vpath %.v ../theories/ordinals/Ackermann
vpath %.v ../theories/ordinals/MoreAck
vpath %.v ../theories/ordinals/Schutte
vpath %.v ../theories/ordinals/Epsilon0
vpath %.v ../theories/ordinals/Gamma0
vpath %.v ../theories/ordinals/OrdinalNotations
vpath %.v ../theories/ordinals/Prelude
vpath %.v ../theories/ordinals/solutions_exercises


all: Ack.html AckNotPR.html primRec.html PrimRecExamples.html F_alpha.html \
    F_omega.html Hydra_Definitions.html Hydra_Theorems.html \
    Hydra_Examples.html Hydra_Lemmas.html

%.html : %.v
	alectryon.py  $(OPTIONS) $<

