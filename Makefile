
.PHONY: test
test: test-multipaxos

.PHONY: multipaxos
test-multipaxos:
	tlc2 MultiPaxos/MC.tla

test-paxos:
	tlc2 Paxos/MC.tla

