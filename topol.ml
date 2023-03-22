(* Autor: Michał Maszkowski
Code Reviewer: Igor Kamiński *)



(* wyjatek rzucany przez [topol] gdy zaleznosci sa cykliczne *)
exception Cykliczne



let topol lista = 
  
  (* STRUKTURY POMOCNICZE: *) 
  
  (* licznik różnych elementów *)
  let licznik = ref 0 in 
  
  (* wstępny guess co do liczby elementów *)
  let guess = List.length lista in 
  
  (* kolejka na kolejne elementy do wstawiania do wyniku *)
  let kolejka = Queue.create () in
  
  (* tablice hashujące: *) 
  (* dana [lista] par przepisana do postaci tablicy hashującej *)
  let potomkowie = Hashtbl.create guess in
  
  (* tablica wszystkich elementów z odpowiadającymi im stopniami wejściowymi *)
  let stopnie = Hashtbl.create guess in
  
  
  
  (* WSTĘPNE PRZYGOTOWANIE STRUKTUR POMOCNICZYCH: *)
  
  (* funkcja przegladająca jedną parę z danej [listy]*)
  let przejrzyjPare (e, l) =
    if not(Hashtbl.mem stopnie e) then (
      licznik := !licznik + 1;
      Hashtbl.add stopnie e 0;
      Hashtbl.add potomkowie e l)
    else Hashtbl.replace potomkowie e (l @ (Hashtbl.find potomkowie e));
    
    (* funkcja przeglądająca jeden element z [l] *)
    let przejrzyjSasiada el =
      if not(Hashtbl.mem stopnie el) then (
        licznik := !licznik + 1;
        Hashtbl.add stopnie el 1;
        Hashtbl.add potomkowie el [])
      else
        Hashtbl.replace stopnie el (1 + (Hashtbl.find stopnie el))
    in
    
    (* przeglądam wszytskie elementy z listy sąsiadów [l] *)
    List.iter przejrzyjSasiada l
  in
  
  (* przeglądam wszystkie elementy z danej [listy] *)
  List.iter przejrzyjPare lista;
  
  
  (* wstawiam do kolejki wszystkie elementy "do których nie wchodzą" inne *)
  let f = fun e st x -> if (st = 0) then (Queue.add e kolejka) else () in
  Hashtbl.fold f stopnie ();
  
  
  
  (* SORTOWANIE TOPOLOGICZNE: *)
  
  (* lista-wynik (prawie) *)
  let prawieWynik = ref [] in
  
  (* [ignorujwierzcholek e] zmniejsza stopień elementom "do których wychodzi" 
     [e]. Te którym stopień spadnie do 0 wstawiam do [kolejki] *)
  let ignorujWierzcholek e =
      (* lista potomków [e] *)
    let potomE = Hashtbl.find potomkowie e in
      (* funkcja zmniejszająca stopień elementu (z listy [potomE]) *)
    let zmniejsz el =
      if (Hashtbl.find stopnie el = 1) then Queue.add el kolejka 
      else Hashtbl.replace stopnie el ((Hashtbl.find stopnie el) - 1)
    in
    (* zmniejszam stopnie potomków [e] *)
    List.iter zmniejsz potomE
  in
  
  (* wyciągam w topologicznym porzadku elementy z [kolejki] i wstawiam
     do [prawieWyniku]. Do [kolejki] dodaje, te elementy które się zwalniają.
  Tak do opustoszenia [kolejki] *)
  while not(Queue.is_empty kolejka) do
    let aktualny = Queue.take kolejka in
    ignorujWierzcholek aktualny;
    (* tu się odwraca kolejność w [prawieWyniku]*)
    prawieWynik := aktualny :: (!prawieWynik)
  done;



  (* OUTPUT: *)

  (* sprawdzam czy w prawieWynikowej liście jest odpowiednio dużo elementów
     jeśli tak to odwracam tą listę, jeśli nie to znaczy że jest cykl *)
  if List.length (!prawieWynik) = !licznik then List.rev (!prawieWynik)
  else raise Cykliczne;;

(* testy z https://gitlab.com/MIMUW-wpf/testy-topol/-/tree/master/tests *)