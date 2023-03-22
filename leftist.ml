(*Autor: Michał Maszkowski
Code Reviewer: Mateusz Perlik*)


  (* kolejka jako drzewo lewicowe o własności kopca typu min*)
type 'a queue = Null | Node of ('a queue * 'a * int * 'a queue);;
  (*Pusta albo Niepusta (lewe poddrzewo, wartość (priorytet), 
				odległość od korzenia do skrajnie prawego liścia (włącznie), prawe poddrzewo)*)


  (*funkcja zwracająca pustą kolejkę priorytetową*)
let empty = Null;;


  (*funkcja zwracająca true dla pustej kolejki i false w przeciwnym przypadku*)
let is_empty q =
	match q with
		| Null -> true
		| _ -> false;;


  (*funkcja pomocnicza zwracająca odległość od korzenia do skrajnie prawego liścia (włącznie)*)
let rpath q = 
	match q with
		| Null -> 0
		| Node (_, _, h, _) -> h;;


  (* funkcja łącząca kolejkę q1 z kolejką q2 (zwraca kolejkę)*)
let join q1 q2 =
	let rec aux_join q1 q2 = (*rekurencyjna funkcja pomocnicza*)
		match q1 with 
			| Null -> q2
			| Node (l1, v1, _, r1) -> match q2 with
				| Null -> q1
				| Node (_, v2, _, _) ->
					if v1 > v2 then (*sprowadzam wszystko do przypaadku, że v1 <= v2*)
						aux_join q2 q1
					else (
						let tym = aux_join q2 r1 in (*jedno z poddrzew wynikowego drzewa*)
						if (rpath l1) < (rpath tym)
							then Node (tym, v1, (rpath l1) + 1, l1) (*zamieniam kolejność poddrzew*)
						else 
							Node (l1, v1, (rpath tym) + 1, tym)) (*'stabilna' kolejność poddrzew*)
	in
	aux_join q1 q2;;


  (*funkcja pomocnicza tworząca z elementu kolejkę z tym elementem*)
let create v = 
	Node (Null, v, 1, Null);;


  (*funkcja zwracając kolejkę powstałą z dołączenia elementu v do kolejki q*)
let add v q = join q (create v);;

  (*Wyjątek podnoszony przez funkcję delete_min q kiedy kolejka q jest pusta*)
exception Empty;;


  (*funkcja podnosząca wyjątek Empty dla pustej kolejki i zwracająca parę (v, q') dla niepustej kolejki,
gdzie v to minimalny element kolejki q, a q' to q bez v*)
let delete_min q =
	match q with
		| Null -> raise (Empty)
		| Node (l1, v1, _, r1) -> (v1, (join l1 r1));;

(*
testy: 
let a = create 5;;
let b = create 7;;
let c = create 10;;
let d = join a b;;
let e = join d c;;
let f = join d e;;
let g = snd (delete_min (snd (delete_min d)));;
is_empty g;; (*true*)
delete_min g;; (*Empty*)

*)

(*gdyby aux_join bylo za pomocą większej liczby podfunkcji zrobione,
to nie byłoby ładniej, bo trzebaby sztucznie dookreslic funkcje value i subtree 
na kolejkach pustych i bylyby to funkcje bardzo podobne do rpath:

let join q1 q2 =
  let rec aux_join q1 q2 = 
    if (is_empty q1) || (is_empty q2) then (
      if (is_empty q1) then q2 
      else q1)
    else (
      let v1 = (value q1) in
      if v1 > (value q2) then
        aux_join q2 q1
      else
        let tym = aux_join q2 (subtree q1 "r") in
        let l1 = subtree q1 "l" in
        if (rpath l1) < (rpath tym)
        then Node (tym, v1, (rpath l1) + 1, l1)
        else 
          Node (l1, v1, (rpath tym) + 1, tym)) 
)
in
aux_join q1 q2;;*);;