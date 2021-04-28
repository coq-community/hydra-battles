
### Naive Makefile
##################

OPTIONS=  --output-directory . -R ../theories/ordinals hydras
INPUTDIR=../theories/ordinals

all: Ack.html AckNotPR.html primRec.html PrimRecExamples.html F_alpha.html F_omega.html 

Ack.html: $(INPUTDIR)/MoreAck/Ack.v
	alectryon.py  $(OPTIONS) $<

AckNotPR.html: $(INPUTDIR)/MoreAck/AckNotPR.v
	alectryon.py  $(OPTIONS) $<

primRec.html: $(INPUTDIR)/Ackermann/primRec.v
	alectryon.py  $(OPTIONS) $<

PrimRecExamples.html: $(INPUTDIR)/MoreAck/PrimRecExamples.v
	alectryon.py  $(OPTIONS) $<

F_alpha.html: $(INPUTDIR)/Epsilon0/F_alpha.v
	alectryon.py  $(OPTIONS) $<


F_omega.html: $(INPUTDIR)/solutions_exercises/F_omega.v
	alectryon.py  $(OPTIONS) $<
