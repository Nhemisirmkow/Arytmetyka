(*Zadanie Arytmetyka*)
(*Autor: Marcin Michorzewski*)
(*Referent: Arek Roussau*)
(*Tworzymy strukturę spójną ze specyfikacją sygnatury*)
(*w pliku Arytmetyka.mli*)


(*Definiujemy pojęcie wartości - jest to para liczb    *)
(*rzeczywistych (do których zaliczamy -oo i +oo) (a, b)*)
(*takich, że wartość liczby może być:                  *)
(*>z przedziału [a; b] dla a<=b (przy czym -oo i +oo są*)
(*odpowiednio najmniejszą i największą liczbą          *)
(*rzeczywistą),                                        *)
(*>z sumy przedziałów (-oo; b] i [a; +oo), dla a>b i   *)
(*a, b różnych od -oo i +oo,                           *)
(*>a = b = nan, gdy nie istnieje wartość, którą nasza  *)
(*liczba może przyjąć                                  *)
(*      Ponadto w [a; b] a =/= +oo i b =/= -oo         *)
type wartosc = float * float


(*KONSTRUKTORY*)

(*funkcja pomocnicza popraw (x), która poprawia (-.0.) *)
(*na 0. (na wszelki wypadek)                           *)

let popraw x =
  if x = (-.0.)
  then abs_float x
  else
    x

(*funkcja pomocnicza neg (f), która będzie oceniała,   *)
(*czy dany element zawarty w funkcji f można porównać  *)
(*zastosowanie: prawdafalsz =: x = x (tu falsz dla     *)
(* x = nan)                                            *)

let neg prawdafalsz =
  if prawdafalsz = true
  then false
  else
    true

let wartosc_od_do x y = 
  let x1 = popraw x
  in
    let y1 = popraw y
    in 
      ((x1, y1) : wartosc)
let wartosc_dokladna x = 
  wartosc_od_do x x
let wartosc_dokladnosc x p = 
  wartosc_od_do (x -. ((p /. 100.) *. (abs_float x))) (x +. ((p /. 100.) *. (abs_float x)))


(*SELEKTORY*)
    

let in_wartosc (w : wartosc) (x : float) =  
  if fst w <= snd w                                     (*gdy x = [a; b]*)
  then (fst w <= x && x <= snd w)
  else                                     (*gdy x = [-oo; b] U [a; +oo]*)
    (x >= fst w || x <= snd w)

let min_wartosc (x : wartosc) =
  if fst x <= snd x                                (*gdy x = [a; b] to a*)
  then fst x 
  else
    if (fst x > snd x)              (*gdy x = [-oo; b] U [a; +oo] to -oo*)
    then neg_infinity
    else
      nan                                           (*gdy x = [nan; nan]*)

let max_wartosc (x : wartosc) =
  if fst x <= snd x                                (*gdy x = [a; b] to b*)
  then snd x 
  else
    if (fst x > snd x)              (*gdy x = [-oo; b] U [a; +oo] to +oo*)
    then infinity
    else
     nan                                             (*gdy x = [nan;nan]*)

(*średnia wartość dla [-oo; +oo] jest nan zaś dla :    *)
(*> a = -oo i b =/= +oo jest -oo                       *)
(*> b = +oo i a =/= -oo jest +oo                       *)
(*> a i b różnych od -oo i +oo (a+b)/2                 *)
(*gdzie a, b to odpowiednio min_wartosc i max_wartosc x*)

let sr_wartosc (x : wartosc) =
  (min_wartosc x +. max_wartosc x) /. 2.


(*MODYFIKATORY*)


(*plus (a, b) da nam:                                  *)
(*> [-oo; +oo], gdy a, b są sumami 2 przedziałów       *)
(*> [-oo; +oo], gdy co najmniej jedno z a, b jest sumą *)
(*  dwóch przedziałów, a drugie ma długość co najmniej *)
(*  tak długą jak luka pierwszego                      *)
(*> [(fst a +. fst b);(snd a +. snd b)] dla pozostałych*)

let plus (a : wartosc) (b : wartosc) =
  let c = (((fst a +. fst b), (snd a +. snd b)) : wartosc)
  in
    if (snd a < fst a && snd b < fst b) 
    then ((neg_infinity, infinity) : wartosc) 
    else 
      if ((snd a < fst a || snd b < fst b) && snd c >= fst c) 
      then ((neg_infinity, infinity) : wartosc) 
      else
	  c

(*minus (a, b) jest tym samym co dodanie wartości      *)
(*przeciwnych do wartości zbioru b                     *)

let minus (a : wartosc) (b : wartosc) =
  plus a ((popraw (-.(snd b)), popraw (-.(fst b))) : wartosc)

(*funkcja pomocnicza laczenie, która łączy zbiory      *)
(*postaci [a; b], gdzie a <= b lub a = b = nan         *)
(*dodatkowy przypadek, gdy drugi argument jest zbiorem *)
(*będącym sumą dwóch spójnych podzbiorów. Wówczas to co*)
(*dokleimy na pewno bedzie się stykało z naszym zbiorem*)
(*z jakiejś strony i być może rozciągnie tę sumę dwóch *)
(*zbiorów o jakieś dodatkowe elementy, bo to co dokleim*)
(*będzie jakimś jednoprzedziałowym zbiorem z co najmnie*)
(*jedną nieskończonością                               *)
 
let laczenie (a : wartosc) (b : wartosc) =
  if neg (fst a = fst a)              (*gdy a = [nan; nan]*)
  then b
  else
    if neg (fst b = fst b)            (*gdy b = [nan; nan]*)
    then a
    else        
      if fst b > snd b  (*gdy b jest sumą dwóch zbiorów*)
      then 
	if fst a <= snd b
	then
	  if snd a >= fst b
	  then ((neg_infinity, infinity) : wartosc)
	  else
	    ((fst b, max (snd a) (snd b)) : wartosc)
	else
	  ((min (fst a) (fst b), snd b) : wartosc)
      else
	let r1 = min_wartosc a
	in
          let r2 = max_wartosc a
          in
            let r3 = min_wartosc b
            in
              let r4 = max_wartosc b
              in
                if r2 < r3  (*wszystko z a < wszystko z b*)
		then ((r3, r2) : wartosc)
		else
                  if r4 < r1 (*wszystko z b < wszystko z a*)
	          then ((r1, r4) : wartosc)
	          else
	            ((min r1 r3, max r2 r4) : wartosc)

(*funkcja pomocnicza wynik, która dla pary float'ów a,b*)
(*zwraca iloczyn a*b, przy czym, jeżeli a lub b = 0 zaś*)
(*drugi z argumentów = +/-oo, to wynik też jest 0, nie *)
(*nan, wszakże 0 razy cokolwiek z definicji to 0...    *)

let wynik a b =
  if (a = 0. && abs_float b = infinity) || (b = 0. && abs_float a = infinity)
  then 0.
  else
    popraw (a *. b)

(*funkcja pomocnicza razy_spojne, która wykonuje razy  *)
(*na zbiorach postaci [a; b], gdzie a <= b bez a = b = *)
(* = nan                                               *)

let razy_spojne (a : wartosc) (b : wartosc) = 
  let r1 = wynik (min_wartosc a) (min_wartosc b)
  in
    let r2 = wynik (min_wartosc a) (max_wartosc b) 
    in
      let r3 = wynik (max_wartosc a)  (min_wartosc b) 
      in
	let r4 = wynik (max_wartosc a) (max_wartosc b) 
	in
	  ((min r1 (min r2 (min r3 r4)), max r1 (max r2 (max r3 r4))) : wartosc)

(*razy (a, b) daje nam:                                *)
(*> [nan; nan] gdy co a lub b = [nan;nan]              *)
(*> razy_spojne (a,b) gdy a i b nie są sumami 2 przedz.*)
(*> razy_spojne (r1, b) U razy_spojne (r2, b) gdy      *)
(*  a = r1 U r2 i r1, r2, b nie są sumą dwóch          *)
(*> razy_spojne (r3, a) U razy_spojne (r4, a), gdy     *)
(*  b = r3 U r4 i a, r3, r4 nie są sumą dwóch          *)
(*> razy_spojne (r1, r3) U razy_spojne (r1, r4) U      *)
(*  U razy_spojne (r2, r3) U razy_spojne (r2, r4), gdy *)
(*  a = r1 U r2 i b = r3 U r4 i r1, r2, r3, r4 nie są  *)
(*  sumą dwóch przedziałów                             *)

let razy (a : wartosc) (b : wartosc) =
  if (neg (fst a = fst a) || neg (fst b = fst b))
  then ((nan, nan) : wartosc)  (*gdy a lub b jest pusty*)
  else
    if (fst a <= snd a && fst b <= snd b)
    then razy_spojne a b
    else
      if (fst a > snd a)
      then
	let r1 = ((neg_infinity, snd a) : wartosc)
	in
	  let r2 = ((fst a, infinity) : wartosc)
	  in
	    if (fst b <= snd b)
	    then laczenie (razy_spojne r1 b) (razy_spojne r2 b)
	    else
	      let r3 = ((neg_infinity, snd b) : wartosc)
	      in
		let r4 = ((fst b, infinity) : wartosc)
		in
		  laczenie (razy_spojne r1 r3) (laczenie (razy_spojne r1 r4) (laczenie (razy_spojne r2 r3) (razy_spojne r2 r4)))
	else
	  let r3 = ((neg_infinity, snd b) : wartosc)
	  in
	    let r4 = ((fst b, infinity) : wartosc)
	    in
	      laczenie (razy_spojne r3 a) (razy_spojne r4 a)

(*podzielic (a, b) =                                   *)
(*> [nan; nan], gdy b = [0; 0] lub b = [nan; nan] lub  *)
(*  a = [nan; nan]                                     *)
(*> [0; 0], gdy a = [0; 0] i b nie pusty i b =/= [0; 0]*)
(*> [-oo; +oo], gdy a != [0; 0] i a nie pusty, zaś     *)
(*  b = [-oo; +oo]                                     *)
(*> razy ([-oo, 1/x], a), gdy a =/= [0;0] i nie pusty i*)
(*  b =/=[0;0] i b nie pusty i b = [x; 0] (dla x = -oo *)
(*  1/x = +0.0)                                        *)
(*> razy ([1/y; 1/x], a), gdy a = [v; t] i v i t=/= nan*)
(*  oraz v i t naraz nie są = 0, b = [x; y] i x =/= -oo*)
(*  i (x i y) =/= nan i (x i y naraz nie są = 0)       *)

let podzielic (a : wartosc) (b : wartosc) =
  if (((fst b = 0.0 && snd b = 0.0) || neg (fst a = fst a)) || neg (fst b = fst b))
  then razy ((nan, nan) : wartosc) a
  else
    if (fst a = 0.0 && snd a = 0.0)
    then ((0., 0.) : wartosc)
    else
      if (fst b = neg_infinity)
      then
	 if snd b = 0.0
	 then razy ((neg_infinity, 0.) : wartosc) a
	 else
	   if snd b = infinity
	   then razy ((neg_infinity, infinity) : wartosc) a
	   else
	     razy (((1.0 /. snd b), 0.) : wartosc) a
      else
        if snd b = 0.0
	then razy ((neg_infinity, (1. /. fst b)) : wartosc) a
	else
	  if fst b = 0.0
	  then razy(((1. /. snd b), infinity) : wartosc) a
	  else
	    razy (((1. /. snd b), (1. /. fst b)) : wartosc) a
