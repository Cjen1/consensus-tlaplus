
.PHONY: test
test: multipaxos

.PHONY: multipaxos
multipaxos:
	tlc2 MultiPaxos/MC.tla
