
### Naive Makefile
##################

OPTIONS=  --frontend coq  --backend json --output-directory . -R ../../theories/ordinals hydras
INPUTDIR=../../theories/ordinals
vpath %.v ../../theories/ordinals/Hydra
vpath %.v ../../theories/ordinals/Ackermann
vpath %.v ../../theories/ordinals/MoreAck
vpath %.v ../../theories/ordinals/Schutte
vpath %.v ../../theories/ordinals/Epsilon0
vpath %.v ../../theories/ordinals/Gamma0
vpath %.v ../../theories/ordinals/OrdinalNotations
vpath %.v ../../theories/ordinals/Prelude
vpath %.v ../../theories/ordinals/solutions_exercises


all: Ack.io.json AckNotPR.io.json primRec.io.json PrimRecExamples.io.json F_alpha.io.json \
    F_omega.io.json Hydra_Definitions.io.json Hydra_Theorems.io.json \
    Hydra_Examples.io.json Hydra_Lemmas.io.json \
    Issue_Program.io.json

Issue_Program.io.json: Issue_Program.v


%.io.json : %.v
	alectryon.py  $(OPTIONS) $<

