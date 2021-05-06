
### Naive Makefile
##################

OPTIONS=  --frontend coq  --backend json --output-directory . -R ../theories/ordinals hydras
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


all: Ack.json AckNotPR.json primRec.json PrimRecExamples.json F_alpha.json \
    F_omega.json Hydra_Definitions.json Hydra_Theorems.json \
    Hydra_Examples.json Hydra_Lemmas.json

%.json : %.v
	alectryon.py  $(OPTIONS) $<

