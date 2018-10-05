Bank.hs: BankParser.hs FraCaS-treebank/src/FraCaSBankI.gf
	ghci BankParser -e main  >$@

FraCaSBank.v: Gf2Coq.awk FraCaS-treebank/src/FraCaSBankI.gf
	gawk -f $^ >$@

