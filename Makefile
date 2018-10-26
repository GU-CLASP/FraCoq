default:: FraCoq2.v

Bank.hs: BankParser.hs FraCaS-treebank/src/FraCaSBankI.gf
	ghc BankParser -e main  >$@

FraCaSBank.v: Gf2Coq.awk FraCaS-treebank/src/FraCaSBankI.gf
	gawk -f $^ >$@

test: Bank.hs
	ghc Tests -e main


clean:
	rm -f *.hi *.o Bank.hs

FraToCoq: Bank.hs FraToCoq.hs MS.hs Logic.hs
	ghc --make FraToCoq

FraCoq2.v: FraToCoq
	./FraToCoq  >$@
