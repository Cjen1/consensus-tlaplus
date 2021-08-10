
.PHONY: test
test: MultiPaxos.tla
	tlc2 MC.tla
