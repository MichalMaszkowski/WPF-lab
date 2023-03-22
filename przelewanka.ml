(* Autor: Michał Maszkowski
Code Review: Michał Maszkowski *)

(* Gotowa implementacja pMap z poprzedniego zadania (okrojona): *) 

type ('k, 'v) map =
  | Empty
  | Node of ('k, 'v) map * 'k * 'v * ('k, 'v) map * int

type ('k, 'v) t =
  {
    cmp : 'k -> 'k -> int;
    map : ('k, 'v) map;
  }

let height = function
  | Node (_, _, _, _, h) -> h
  | Empty -> 0

let make l k v r = Node (l, k, v, r, max (height l) (height r) + 1)

let bal l k v r =
  let hl = height l in
  let hr = height r in
  if hl > hr + 2 then
    match l with
    | Node (ll, lk, lv, lr, _) ->
        if height ll >= height lr then make ll lk lv (make lr k v r)
        else
          (match lr with
           | Node (lrl, lrk, lrv, lrr, _) ->
               make (make ll lk lv lrl) lrk lrv (make lrr k v r)
           | Empty -> assert false)
    | Empty -> assert false
  else if hr > hl + 2 then
    match r with
    | Node (rl, rk, rv, rr, _) ->
        if height rr >= height rl then make (make l k v rl) rk rv rr
        else
          (match rl with
           | Node (rll, rlk, rlv, rlr, _) ->
               make (make l k v rll) rlk rlv (make rlr rk rv rr)
           | Empty -> assert false)
    | Empty -> assert false
  else Node (l, k, v, r, max hl hr + 1) 

let create cmp = { cmp = cmp; map = Empty } 

let add x d { cmp = cmp; map = map } =
  let rec loop = function
    | Node (l, k, v, r, h) ->
        let c = cmp x k in
        if c = 0 then Node (l, x, d, r, h)
        else if c < 0 then
          let nl = loop l in
          bal nl k v r
        else
          let nr = loop r in
          bal l k v nr
    | Empty -> Node (Empty, x, d, Empty, 1) in
  { cmp = cmp; map = loop map }

let find x { cmp = cmp; map = map } =
  let rec loop = function
    | Node (l, k, v, r, _) ->
        let c = cmp x k in
        if c < 0 then loop l
        else if c > 0 then loop r
        else v
    | Empty -> raise Not_found in
  loop map
    
    


(* Przelewanka: *)

(* zwraca true jesli istnieje i takie ze (xi, yi) należy do [t] i 
   ((xi = yi) lub (yi = 0); zwraca false w przeciwnym przypadku - wtedy nie 
   jest możliwe uzyskanie żądanego stanu, bo każda z operacji na szklankach
   w wyniku daje co najmniej jedna pustą lub co najmniej jedną pełną szklankę
   a początkowo wszystkie szklanki są puste, zatem na końcu co najmniej jedna
   musi być pusta lub pełna *)
let test1 t =
  let przejrzyj = (fun acc (x, y) -> (acc || (x = y) || (y = 0))) in
  Array.fold_left przejrzyj false t;;

(* zwraca true jeśli w tablicy [t] która jest postaci 
   [(x1, y1), (x2, y2), ..., (xn, yn)] zachodzi: a = (nwd x1, x2, ..., xn),
   b = nwd (y1, y2, ..., yn); a dzieli b) 
   zwraca false w przeciwnym przypadku - wtedy nie jest możliwe uzyskanie 
   żądanego stanu, bo początkowo wszystkie objętości są podzielne przez a, 
   wtedy żadna z operacji na szklankach nie zmienia podzielności 
   objętości wody w szklankach przez a, zatem wszystkie objętości końcowe muszą 
   być podzielne przez a, czyli b musi się dzielić przez a *)
let test2 t =
(* zwraca najwiekszy wspolny dzielnik [a] i [b] *)
  let nwd a b =
    let rec pom m n =
      if (m = 0) then n 
      else pom (n mod m) m
    in
    if (a <= b) then pom a b else pom b a
  in
  let przejrzyj = fun (k, l) (x, y) -> (nwd k x, nwd l y) in
  let (a, b) = Array.fold_left przejrzyj (0, 0) t in
  ((b mod a) = 0);;

(* funkcja tworząca i przeglądająca graf możliwych stanów objetości szklanek *)
let przejrzyj t =
  let dl = Array.length t in
  
  (* kolejka do BFS *)
  let q = Queue.create () in
  
  (* węzeł wynikowy - żądany stan *)
  let przepisz = fun i -> snd (t.(i)) in
  let zadany = Array.init dl przepisz in
  
  (* rozpatrzone stany zapisuję w pMapie [odwiedzone], 
     w ktorej kluczami sa stany a dowiazaniami jest liczba potrzebnych 
     ruchow potrzebnych do osiagniecia danego stanu
     compare porownuje tablice (porzadkuje liniowo - dla tablic 
     o tej samej dlugosci leksykograficznie) *)
  let odwiedzone = ref (create compare) in
  
  (* globalny 'przełącznik' pilnujący, żeby zakończyć obliczenia 
     od razu po znalezieniu wyniku *)
  let wynik = ref (-1) in
  
  
  (* inicjalizacja struktur stanem początkowym - wszystkie szklanki puste *)
  let start = Array.make dl 0 in
  odwiedzone := add start 0 (!odwiedzone);
  Queue.add (start, 0) q;

  
  (* analizuje czy dany [stan] byl odwiedzony, jesli tak to nic sie nie dzieje,
     a jesli nie to dodaje parę ([stan], [r]) do kolejki [q] 
     i do [odwiedzonych] z dowiazaniem [r] *)
  let analizuj stan r = 
    (* sprawdzam czy [stan] jest w [odwiedzonych], jesli nie ma to [tym] = -1 *)
    let tym = try (find stan !odwiedzone) with Not_found -> (-1) in
    if (-1 = tym) then (
      if ((compare stan zadany) = 0) then 
        wynik := r
      else (
        Queue.add (stan, r) q;
        odwiedzone := add stan r (!odwiedzone)))
    else ()
  in

  (* przejście pomiędzy stanami polegające na napełnieniu [i]tej szklanki *)
  let napelnij staryStan i r =
    let nowyStan = Array.copy staryStan in
    (* w tablicy [t] znajduję max pojemność [i]tej szklanki*)
    let maxPoj = fst t.(i) in
    if (nowyStan.(i) = maxPoj) then ()
    else (
      nowyStan.(i) <- fst t.(i);
      analizuj nowyStan (r + 1))
  in

  (* przejście pomiędzy stanami polegające na opróżnieniu [i]tej szklanki *)
  let wylej staryStan i r =
    let nowyStan = Array.copy staryStan in 
    if (nowyStan.(i) = 0) then ()
    else (
      nowyStan.(i) <- 0;
      analizuj nowyStan (r + 1))
  in

  (* przejście pomiędzy stanami polegające na przelaniu wody 
  z [i]tej szklanki do [j]tej szklanki *)
  let przelej staryStan i j r =
    if (i = j) then ()
    else
      (let nowyStan = Array.copy staryStan in
       (* przelana zostanie mniejsza z wartości: 
       objętość nie wody w szklance [j]tej; objętość wody w szklance [i]tej *)
       let ileMiejsca = fst t.(j) - staryStan.(j) in
       let roznica = min ileMiejsca staryStan.(i) in
       if (roznica = 0) then ()
       else (
         nowyStan.(i) <- staryStan.(i) - roznica;
         nowyStan.(j) <- staryStan.(j) + roznica;
         analizuj nowyStan (r + 1)))
  in
  
  (* sprawdzam czy nie jest zadany stan startowy *)
  if (start = zadany) then 0
  else (
    (* tutaj tworzę i przechodzę kolejne węzły grafu stanów 
    dopóki nie otrzymam zadanego stanu *)
    while (-1 = !wynik) do
      if Queue.is_empty q then
        wynik := (-1)
      else ( 
        let (aktStan, r) = Queue.take q in
        (* rozpatruję akcje na każdej szklance *)
        for i = 0 to (dl - 1) do
          napelnij aktStan i r;
          wylej aktStan i r;
          for j = 0 to (dl - 1) do przelej aktStan i j r done
        done)
    done;
    !wynik)

(* usuwa z tablicy szklanki o pojemnosci 0 (zwraca nowa tablice) *)
let oczysc t =
  let zlicz =
    fun acc (x, _) -> if (x > 0) then (acc + 1) else acc
  in
  let dlugosc' = Array.fold_left zlicz 0 t in
  let nowa = Array.make dlugosc' (0, 0) in
  let i = ref 0 in
  let przepisz = fun (x, y) -> if (x > 0) then 
      (nowa.(!i) <- (x, y);
       i := (!i + 1))
    else () 
  in
  Array.iter przepisz t;
  nowa;;

let przelewanka t =
  let t' = oczysc t in
  if ((Array.length t') = 0) then 0
  else (
    if ((test1 t') && (test2 t')) then 
      przejrzyj t'
    else -1);;

(* przechodzi testy z:
https://gitlab.com/MIMUW-wpf/testy-przelewanka/-/tree/master/tests
*)