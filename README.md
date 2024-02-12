kompilacja: make, lub bezpośrednie uruchomienie cabal install z odpowiednimi argumentami
do kompilacji wymagany jest cabal do kompilacji języka haskell (które jest obecny na maszynie students)
używane paczki są opisane w ./Latte.cabal

uruchomienie: jak w treści, dla dołączonego testu np: ./latc_x86_64 lattests/good/core/core001.lat
program wypisze wtedy "ERROR\n" z powodem błędu lub "OK\n" jeśli kod został zaakceptowany.

Rozszerzenia:
- tablice
- klasy z dziedziczeniem
- odśmiecanie
- częściowa optymalizacja alokacji rejestrów: zmienne w bloku nie zajmują miejsca poza nim, używane są caller-save rejestry do liczenia wyrażeń
