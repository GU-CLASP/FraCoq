default:: FraCoq2.v

Bank.hs: BankParser.hs FraCaS-treebank/src/FraCaSBankI.gf
	ghc BankParser -e main  >$@

FraCaSBank.v: Gf2Coq.awk FraCaS-treebank/src/FraCaSBankI.gf
	gawk -f $^ >$@

test: Bank.hs
	ghc Tests -e main

clean:
	rm -f *.hi *.o Bank.hs


FraCoq2.v: BankParser.hs FraCaS-treebank/src/FraCaSBankI.gf FraToCoq.hs
	ghc FraToCoq -e main  >$@
