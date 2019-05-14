default:: results

Bank.hs: AnswerTypes.hs BankParser.hs FraCaS-treebank/src/FraCaSBankI.gf
	nix-shell --run "ghc BankParser -e main  >$@"

FraCaSBank.v: Gf2Coq.awk FraCaS-treebank/src/FraCaSBankI.gf
	gawk -f $^ >$@

results:: verify1.txt verify2.txt verify3.txt verify4.txt verify5.txt verify6.txt verify8.txt verify9.txt  ResultParser.hs
	nix-shell --run "runhaskell ResultParser.hs Section?.v"

verify%.txt: Section%.v MS.v Formulas.v
	coqc Section$*.v > $@

test:: Tests
	./Tests

Tests: Bank.hs Tests.hs MS.hs Logic.hs LogicB.hs
	nix-shell --run "ghc --make Tests"

clean:
	rm -f *.hi *.o Bank.hs

FraToCoq: Bank.hs FraToCoq.hs MS.hs Logic.hs LogicB.hs
	nix-shell --run "ghc --make FraToCoq"

Formulas.v: FraToCoq
	./FraToCoq  >$@
