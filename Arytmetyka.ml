(* Autor: Michał Maszkowski 421428
CodeReviewer: Arkadiusz Kobus 429321 *)

let min a b = 
	if (a <> a) then b 
 	else (if (b <> b) 
		then a 
 	else (if (a <= b)  
		then a 
		else b))

let max a b = 
	if (a <> a) then b 
 	else (if (b <> b) 
		then a 
 	else (if (a < b)  
		then b 
		else a))

type wartosc = {negatyw: bool; l: float; p: float}
(* assert: l<=p
jesli !negatyw to zakres od l do p wlacznie
jesli negatyw to wszystko poza tym zakresem (dopelnienie)
jesli negatyw to (l i p sa ograniczone) and (l < p) *)

(*funkcja pomocnicza - abs dla floatów*)
let bezwzgl x = if (x >= 0.) then x else (0. -. x)

let wartosc_dokladnosc x p = 
	{negatyw = false; l = (x -. (bezwzgl (x *. p /. 100.))); p = (x +. (bezwzgl (x *. p /. 100.)))}
(* assert: x <= y *)

let wartosc_od_do x y = 
	{negatyw = false; l = x; p = y}

let wartosc_dokladna x = 
	{negatyw = false; l = x; p = x}


let in_wartosc w x = 
	if (w.negatyw = false)
		then (if ((x >= w.l) && (x <= w.p)) then true else false)
		else (if ((x <= w.l) || (x >= w.p)) then true else false)

let min_wartosc w = 
	if (w.negatyw = false) 
		then w.l 
		else neg_infinity

let max_wartosc w = 
	if (w.negatyw = false) 
		then w.p 
		else infinity

let sr_wartosc w = 
	if ((min_wartosc w) = neg_infinity) 
		then (if ((max_wartosc w) = infinity) then nan else neg_infinity)
		else (if ((max_wartosc w) = infinity) then infinity else ((w.l +. w.p) /. 2.))


(* funkcja pomocnicza rozdzielająca dopełnienie na dwa składowe zakresy
assert: w.negatyw = true *)
let rozdziel w = 
	({negatyw = false; l = neg_infinity; p = w.l}, {negatyw = false; l = w.p; p = infinity})

(* funkcja pomocnicza złączająca dwa zakresy w dopełnienie 
- zakresy maja co najmniej jeden kraniec nie ograniczony
assert: (w1.negatyw=false and w2.negatyw=false) and ((w1.l=neg_infinity and w2.p=infinity) or (w1.p=infinity and w2.l=neg_infinity)) *)
let zlacz w1 w2 =
	(* assert: (w1.negatyw=false and w1.l=neg_infinity) and (w2.negatyw=false and w2.p=infinity)*)
	let pom_zlacz w1 w2 = 
		if (w1.p < w2.l) 
			then {negatyw = true; l = w1.p; p =w2.l} 
			else {negatyw = false; l = neg_infinity; p = infinity}
	in
	if ((w1.l=neg_infinity) && (w2.p=infinity)) 
		then (pom_zlacz w1 w2)
		else (pom_zlacz w2 w1)

let plus w1 w2 =
	let rec pom_plus w1 w2 =
		if ((w1.negatyw = false) && (w2.negatyw = false))
			then ({negatyw = false; l = (w1.l +. w2.l); p = (w1.p +. w2.p)})
		else (if ((w1.negatyw = true) && (w2.negatyw=false))
			then (zlacz (pom_plus (fst (rozdziel w1)) w2) (pom_plus (snd (rozdziel w1)) w2))
		else (if ((w1.negatyw = false) && (w2.negatyw=true))
			then (pom_plus w2 w1)
		else ({negatyw = false; l = neg_infinity; p = infinity})))
	in (pom_plus w1 w2)
(*
1. przedzial plus przedzial
2. dopelnienie plus przedzial
3. przedzial plus dopelnienie
4. dopelnienie plus dopelnienie
*)


(*funkcja pomocnicza zwracajaca dla danego przedziału przedział elementów przeciwnych*)
let odwrotnosc w = 
	{negatyw = w.negatyw; l = 0. -. (w.p); p = 0. -. (w.l)}

(*a-b=a+(-b)*)
let minus w1 w2 =
	(plus w1 (odwrotnosc w2))


let razy w1 w2 = 
	let rec pom_razy w1 w2 =
		if ((w1.negatyw = false) && (w2.negatyw = false)) then
			(let tym1 = (min (min (w1.l *. w2.l) (w1.l *. w2.p)) (min (w1.p *. w2.l) (w1.p *. w2.p))) in
			let tym2 = (max (max (w1.l *. w2.l) (w1.l *. w2.p)) (max (w1.p *. w2.l) (w1.p *. w2.p))) in
			({negatyw = false; l = tym1; p = tym2}))
		else (if ((w1.negatyw = true) && (w2.negatyw = false)) 
			then (zlacz (pom_razy (fst (rozdziel w1)) w2) (pom_razy (snd (rozdziel w1)) w2))
		else (if ((w1.negatyw = false) && (w2.negatyw = true))
			then (pom_razy w2 w1)
		else (if (((w1.l < 0.) && (w1.p> 0.)) && ((w2.l < 0.) && (w2.p > 0.)))
			then ({negatyw = true; l = (max (w1.p *. w2.l) (w1.l *. w2.p)); p = (min (w1.p *. w2.p) (w1.l *. w2.l))})
			else ({negatyw = false; l = neg_infinity; p = infinity}))
	)) in
	if (((w2.l = 0.) && (w2.p = 0.)) || ((w1.l = 0.) && (w1.p = 0.)))
				then ({negatyw = false; l = 0.; p = 0.})
				else (pom_razy w1 w2)
(*
1. przedzial razy przedzial
2. dopelnienie razy przedzial
3. przedzial razy dopelnienie
4. dopelnienie razy dopelnienie
	a) dopełnienie przedziału po obu stronach zera razy dopełnienie przedziału po obu stronach zera
	b) reszta przypadkow
*)


(*funkcja pomocnicza kontrolująca sytuację z zerami*)
let norm w = 
	if ((w.negatyw = false) && (w.p = 0.)) 
		then ({negatyw = false; l = w.l; p = (0. *. (0. -. 1.))})
	else (if ((w.negatyw = false) && (w.l = 0.)) 
		then ({negatyw = false; l = 0.; p = w.p})
		else w)

let podzielic w1 w2 = 
	let rec pom_podziel w1 w2 =
        let w1 = norm w1 in
		let w2 = norm w2 in
		if ((w1.negatyw = false) && (w2.negatyw = false)) then (
			if ((w2.l >= 0.) || (w2.p <= 0.)) then (
				let tym1 = (min (min (w1.l /. w2.l) (w1.l /. w2.p)) (min (w1.p /. w2.l) (w1.p /. w2.p))) in
				let tym2 = (max (max (w1.l /. w2.l) (w1.l /. w2.p)) (max (w1.p /. w2.l) (w1.p /. w2.p))) in
				({negatyw = false; l = tym1; p = tym2}))
			else ( let tym1 = ({negatyw = false; l = w2.l; p = (0. *. (0. -. 1.))}) in
				let tym2 = ({negatyw = false; l = 0.; p = w2.p}) in
				(zlacz (pom_podziel w1 tym1) (pom_podziel w1 tym2))))
		else (if ((w1.negatyw = true) && (w2.negatyw = false)) then (
			if ((w2.l >= 0.) || (w2.p <= 0.)) then
				(zlacz (pom_podziel (fst (rozdziel w1)) w2) (pom_podziel (snd (rozdziel w1)) w2))
			else (if ((w1.l <= 0.) && (w1.p >= 0.)) then (
				let tym1 = max (w1.p /. w2.l) (w1.l /. w2.p) in
				let tym2 = min (w1.p /. w2.p) (w1.l /. w2.l) in
				if (tym1 >= tym2) then ({negatyw = false; l = neg_infinity; p = infinity}) else ({negatyw = true; l = tym1; p = tym2})) 
				else ({negatyw = false; l = neg_infinity; p = infinity})))
		else (if ((w1.negatyw = false) && (w2.negatyw = true)) then (
			if ((w2.l <= 0.) && (w2.p >= 0.)) then (
				let tym1 = (min (min (w1.l /. w2.l) (w1.l /. w2.p)) (min (w1.p /. w2.l) (w1.p /. w2.p))) in
				let tym2 = (max (max (w1.l /. w2.l) (w1.l /. w2.p)) (max (w1.p /. w2.l) (w1.p /. w2.p))) in
				({negatyw = false; l = tym1; p = tym2}))
			else (if (w1.p <= 0.) then (
				let tym1 = max (w1.l /. w2.l) (w1.p /. w2.l) in
				let tym2 = min (w1.l /. w2.p) (w1.p /. w2.p) in
				if (tym1 >= tym2) then ({negatyw = false; l = neg_infinity; p = infinity})
					else ({negatyw = true; l = tym1; p = tym2}))
			else (if (w1.l >= 0.) then (
				let tym1 = max (w1.l /. w2.p) (w1.p /. w2.p) in
				let tym2 = min (w1.l /. w2.l) (w1.p /. w2.l) in
				if (tym1 >= tym2) then ({negatyw = false; l = neg_infinity; p = infinity})
					else ({negatyw = true; l = tym1; p = tym2}))
			else ({negatyw = false; l = neg_infinity; p = infinity}))))
		else (if (((w1.l < 0.) && (w1.p > 0.)) && ((w2.l < 0.) && (w2.p > 0.)))
			then (zlacz (pom_podziel (fst (rozdziel w1)) w2) (pom_podziel (snd (rozdziel w1)) w2))
			else ({negatyw = false; l = neg_infinity; p = infinity}))))
	in 
	if ((w2.l = 0.) && (w2.p = 0.)) 
		then raise (Failure "Dzielenie przez 0") 
		else (pom_podziel w1 w2)
(* 
1. przedział przez przedział
	a) przez przedział z jednej strony zera
	b) przez przedział z obu stron zera
2. dopełnienie przez przedział
	a) przez przedział z jednej strony zera
	b) przez przedział z obu stron zera
3. przedział przez dopełnienie
	a) przez dopełnienie przedziału po obu stronach zera
	b) przez dopełnienie przedziału po jednej stronie zera
		- przedzial po lewej stronie zera
		- przedzial po prawej stronie zera
		- przedzial po obu stronach zera
4. dopełnienie przez dopełnienie
	a) dopełnienie przedziału po obu stronach zera przez dopełnienie przedziału po obu stronach zera
	b) reszta
*)