all: latte

latte: 
	cabal install --installdir=. --overwrite-policy=always