
.PHONY: test
test: test-logpaxos test-paxos

.PHONY: test-logpaxos
test-logpaxos:
	tlc2 LogPaxos/MC.tla

.PHONY: test-paxos
test-paxos:
	tlc2 Paxos/MC.tla

