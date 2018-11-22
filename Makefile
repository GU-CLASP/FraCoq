default:: results

Bank.hs: AnswerTypes.hs BankParser.hs FraCaS-treebank/src/FraCaSBankI.gf
	nix-shell --run "ghc BankParser -e main  >$@"

FraCaSBank.v: Gf2Coq.awk FraCaS-treebank/src/FraCaSBankI.gf
	gawk -f $^ >$@

results:: verify.txt ResultParser.hs
	nix-shell --run "runhaskell ResultParser.hs Proofs.v Section*.v"

verify.txt: Proofs.v MS.v FraCoq2.v
	coqc Section2.v Proofs.v > $@

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
