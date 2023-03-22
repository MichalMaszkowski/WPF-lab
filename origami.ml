(* Autor : Michał Maszkowski
Code Reviewer: Tomasz Głąb *)


(* Punkt [x, y] na płaszczyźnie o wspołrzędnych <x, y> 
w układzie kartezjańskim *)

type point = float * float



(* Typ reprezentujący poskładaną kartkę: funkcja zwracająca 
ile razy kartkę przebije szpilka wbita w danym punkcie *)

type kartka = point -> int



(* [prostokat p1 p2] zwraca [kartkę] reprezentującą kartkę w kształcie 
domkniętego prostokąta o bokach równoległych do osi układu współrzędnych 
i lewym dolnym rogu [p1] a prawym górnym [p2]. Punkt [p1] musi być nieostro 
na lewo i w dół od punktu [p2]. Gdy w kartkę tę wbije się szpilkę wewnątrz
(lub na krawędziach) prostokąta, kartka zostanie przebita 1 raz,
w pozostałych przypadkach 0 razy *)

let prostokat (p1 : point) (p2 : point) : kartka= function 
    (x, y) ->
      let (x1, y1) = p1
      and (x2, y2) = p2 in
      if ((x1 <= x) && (x <= x2) && (y1 <= y) && (y <= y2)) then 1 
      else 0



(* [kolko p r] zwraca [kartkę], reprezentującą kartkę o kształcie domkniętego 
koła o środku w punkcie [p] i promieniu [r] *)

let kolko (p : point) r : kartka = function 
    (x, y) ->
      let (px, py) = p in
      if (((px -. x) *. (px -. x) +. (py -. y) *. (py -. y)) <= (r *. r)) then 1
      else 0



(* Funkcja pomocnicza dla funkcji "zloz" [strona p1 p2 p] informuje o tym,
po ktorej stronie wektora p1p2 jest punkt p - jesli na prostej na przedluzeniu 
wektora to zwraca 0., jesli po lewej to zwraca floata > 0., 
jesli po prawej to zwraca floata < 0. (iloczyn wektorowy między p1p2 a p1p) *)

let strona p1 p2 p =
  let (x1, y1) = p1
  and (x2, y2) = p2
  and (px, py) = p in
  (* iloczyn wektorowy wektora p1p2 i p1p *)
  (x2 -. x1) *. (py -. y1) -. (y2 -. y1) *. (px -. x1)



(* funkcja [odbicieSymetryczne p1 p2 p] zwracająca punkt p' = (px', py') 
  będący odbiciem symetrycznym p względem prostej p1p2 
 (* tu się dzieje geometria: *) *)
 
let odbicieSymetryczne p1 p2 p = 
  let (x1, y1) = p1
  and (x2, y2) = p2
  and (px, py) = p in

  (* jeśli prosta p1p2 jest równologła do osi y *)
  if (x1 = x2) then (2. *. x1 -. px, py)
  else (
  
    (* jeśli prosta p1p2 jest równologła do osi x *)
    if (y1 = y2) then (px, 2. *. y1 -. py)
    else (
      (* prosta y = a1 *. x +. b1 to prosta p1p2*)
      let a1 = (y1 -. y2) /. (x1 -. x2) in
      let b1 = y1 -. a1 *. x1 in

      (* prosta y = a2 *. x +. b2 to prosta prostopadła do prostej p1p2 
      przechodzaca przez punkt p *)
      let a2 = 0. -. 1. /. a1 in
      let b2 = py -. a2 *. px in

      (* przeciecie tych dwoch prostych jest w p3 = (x3, y3) *)
      let x3 = (b2 -. b1) /. (a1 -. a2) in
      let y3 = a1 *. x3 +. b1 in
      
      (* *wynik* *)
      let px' = 2. *. x3 -. px in
      let py' = 2. *. y3 -. py in 
      (px', py')))



(* funkcja [zloz p1 p2 k] składa kartkę [k] wzdłuż prostej przechodzącej przez
punkty [p1] i [p2]. assert (p1 <> p2). Papier jest składany w ten sposób, 
że z prawej strony prostej (patrząc w kierunku od [p1] do [p2]) jest przekładany
na lewą. Wynikiem funkcji jest złożona kartka. Jej przebicie po prawej stronie 
  prostej powinno więc zwrócić 0. Przebicie dokładnie na prostej powinno zwrócić 
tyle samo, co przebicie kartki przed złożeniem. Po stronie lewej -
           tyle co przed złożeniem plus przebicie rozłożonej kartki w punkcie,
który nałożył się na punkt przebicia. *)

let zloz (p1 : point) (p2 : point) (k : kartka) : kartka = function 
    (p : point) ->
      let s = strona p1 p2 p in
      if (s = 0.) then
        k p
      else (
        if (s < 0.) then
          0
        else (
          let p' = odbicieSymetryczne p1 p2 p in
        (* *wynik* *)
          k p + k p'))



(* [skladaj [(p1_1,p2_1);...;(p1_n,p2_n)] k = 
zloz p1_n p2_n (zloz ... (zloz p1_1 p2_1 k)...)]
czyli wynikiem jest złożenie kartki [k] kolejno 
wzdłuż wszystkich prostych z listy *) 

let skladaj l k =
  let pom_zloz a (p1, p2) = zloz p1 p2 a in
  List.fold_left pom_zloz k l;;

(* przetestowałem na testach udostępnionych na: 
https://gitlab.com/MIMUW-wpf/testy-origami/-/blob/master/tests/agluszak.ml
https://gitlab.com/MIMUW-wpf/testy-origami/-/blob/master/tests/GH_Mucosolvan.ml
https://gitlab.com/MIMUW-wpf/testy-origami/-/blob/master/tests/GH_Nhemisirmkow_test2.ml
https://gitlab.com/MIMUW-wpf/testy-origami/-/blob/master/tests/GH_kmichael08.ml
https://gitlab.com/MIMUW-wpf/testy-origami/-/blob/master/tests/z_tkanas.ml
i działa na nich wszystkich

na tym: 
https://gitlab.com/MIMUW-wpf/testy-origami/-/blob/master/tests/GH_Nhemisirmkow_test.ml
nie działa test63 a w teście 88 jest truncation error
na tym:
https://gitlab.com/MIMUW-wpf/testy-origami/-/blob/master/tests/mgienieczko.ml
nie działają asercje z linii 104, 259, 292, 356, 395, 418 (pierwsza to na pewno truncation error)
na tym:
https://gitlab.com/MIMUW-wpf/testy-origami/-/blob/master/tests/z_GH_amharc.ml
wywraca się na linii 41

reszta z tych 3 testow działa
*) 