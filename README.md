kompilacja: make, lub bezpośrednie uruchomienie cabal install z odpowiednimi argumentami
do kompilacji wymagany jest cabal do kompilacji języka haskell (które jest obecny na maszynie students)
używane paczki są opisane w ./Latte.cabal

uruchomienie: jak w treści, dla dołączonego test np: ./latc_x86_64 lattests/good/core001.lat
program wypisze wtedy ERROR\n z powodem błędu lub OK\n jeśli kod został zaakceptowany. Kompilacja nie została jeszcze zaimplementowana

Sprawdzane są wszystkie podane rozszerzenia poza metodami wirtualnymi tzn tablice, klasy z dziedziczeniem
