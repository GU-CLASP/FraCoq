default:: FraCoq2.v

Bank.hs: BankParser.hs FraCaS-treebank/src/FraCaSBankI.gf
	nix-shell --run "ghc BankParser -e main  >$@"

FraCaSBank.v: Gf2Coq.awk FraCaS-treebank/src/FraCaSBankI.gf
	gawk -f $^ >$@

test:: Tests
	./Tests

Tests: Bank.hs Tests.hs MS.hs Logic.hs LogicB.hs
	nix-shell --run "ghc --make Tests"

clean:
	rm -f *.hi *.o Bank.hs

FraToCoq: Bank.hs FraToCoq.hs MS.hs Logic.hs LogicB.hs
	nix-shell --run "ghc --make FraToCoq"

FraCoq2.v: FraToCoq
	./FraToCoq  >$@
