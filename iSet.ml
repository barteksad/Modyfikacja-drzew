(* ------------------------------------------------------------ *)
(* AUTOR : BARTEK SADLEJ*)
(* ------------------------------------------------------------ *)



(* FNKCJA PORÓWNUJĄCA PRZEDZIAŁY NIE DOKŁADNIE*)
(* 0  - równość oznaczające, że przecięcie x y nie jest zbiorem pustym *)
(* -1 -  max(x) < min(y) *)
(* +1 -  min(x) > max (y)*)
let cmp_przedzialy (x_pocz,x_kon) (y_pocz,y_kon) =
    if x_kon  < y_pocz then -1 else
    if x_pocz > y_kon  then  1 else
                               0;;
let strict_compare x (y_pocz,y_kon) =
  if x>y_kon 
    then 1
  else if x<y_pocz
    then -1
  else 0;;


(* Sprawdza jak wygląda przecięcie x y *)
(* 0 - x cały w y *)
(* -1 x wystaje z lewej strony y *)
(* 1 x wystaje z prawej strony yv*)
(* 2 - y cały w x *)
let intersection (x_pocz,x_kon) (y_pocz,y_kon) = 
    if y_pocz>=x_pocz && y_kon<=x_kon
      then 2
    else if y_pocz<=x_pocz && y_kon>=x_kon
      then 0
    else if x_pocz<y_pocz 
      then -1
    else 1;;

(* Type set- krotka int*int *)
type set =
  | Empty
  | Node of set * (int*int) *  set * int 

type t =
  {
    cmp : int*int -> int*int -> int;
    set : set;
  }

(* nie zmienione *)
let height = function
  | Node(_, _, _, h) -> h
  | Empty -> 0

(* nie zmienione *)
let make l k r = Node (l, k, r, max (height l) (height r) + 1)

(* nie zmienione *)
let bal l k r =
  let hl = height l in
  let hr = height r in
  if hl > hr + 2 then
    match l with
    | Node (ll, lk, lr, _) ->
        if height ll >= height lr then make ll lk (make lr k r)
        else
          (match lr with
          | Node (lrl, lrk, lrr, _) ->
              make (make ll lk lrl) lrk (make lrr k r)
          | Empty -> assert false)
    | Empty -> assert false
  else if hr > hl + 2 then
    match r with
    | Node (rl, rk, rr, _) ->
        if height rr >= height rl then make (make l k rl) rk rr
        else
          (match rl with
          | Node (rll, rlk, rlr, _) ->
              make (make l k rll) rlk (make rlr rk rr)
          | Empty -> assert false)
    | Empty -> assert false
  else Node (l, k, r, max hl hr + 1)

(* nie zmienione *)
let rec min_elt = function
  | Node (Empty, k, _, _) -> k
  | Node (l, _, _, _) -> min_elt l
  | Empty -> raise Not_found

(* nie zmienione *)
let rec remove_min_elt = function
  | Node (Empty, _, r, _) -> r
  | Node (l, k, r, _) -> bal (remove_min_elt l) k r
  | Empty -> invalid_arg "PSet.remove_min_elt"

(* nie zmienione *)
let merge t1 t2 =
  match t1, t2 with
  | Empty, _ -> t2
  | _, Empty -> t1
  | _ ->
      let k = min_elt t2 in
      bal t1 k (remove_min_elt t2)

(* nie zmienione *)
let create cmp = { cmp = cmp; set = Empty }

(* compare zmienione na cmp_przedzialy *)
let empty = { cmp = cmp_przedzialy; set = Empty }

(* nie zmienione *)
let is_empty x = 
  x.set = Empty

(* ten sam kod co mem, tylko zamiast true/false zwracamy konkretny element lub (1,-1) jeśli nie znaleziono*)
(* bierze tylko szukay element i set *)(* ZŁOŻONOŚĆ: log n - najgorszy przypadek- wysokość jednego drzewa = 1*)

(* ZŁOŻONOŚĆ: log n - wyszukanie w poprawnym drzewie avl *)
let mem_przedzial_zawierajacy x set = 
  let rec loop = function
    | Node (l, k, r, _) ->
        let c = cmp_przedzialy x k in
        if c = 0 
            then k 
        else
          loop (if c < 0 then l else r)
    | Empty -> (1,-1) in
  loop set

(* funkcja sprawdzająca, czy set jest poprawnym drzewem AVL, w tym przypadku lheight +-2 = rheight *)
let is_valid x = 
  match x with
  | Node(l, k, r, h) ->
    let left_height = height l in
    let right_height = height r in
    abs (left_height - right_height) < 3
  | Empty -> true;;


(* funkcja pomocnicza do dodawania i usuwania elementów *)
(* wywołuje ball dopóki is_valid nie zwróci true *)
(* Funkcja zwraca poprawne drzewo, ponieważ ball za każdym wywołaniem *)
(* poprawia różnice wysokości pomiędzy prawym i lewym poddrzewem o 1 *)

(* ZŁOŻONOŚĆ: log n - najgorszy przypadek- wysokość jednego drzewa = 1, drugiego log n, *)
(* wywołuje ball (log n) -2 razy, a ball działa w czasie stałym*)
let rec napraw x = 
    if is_valid x 
        then x 
    else
    match x with
    | Node(l,k,r,h) -> napraw (bal l k r)
    | Empty -> Empty;;



(* Funkcja wywoływana przez join  gdy wiadomo, że zdodawany przedział pokrywa się z conajwyżej jednym w drzewie *)
(* Czyli podczas liczenia split, lub łącząc drzewa w add_one po split *)

(* Złożoność - log n - dodawanie elementu do poprawnego drzewa avl *)
let rec add_one_SPECIAL cmp x = function
  | Node (l, k, r, h) ->
      let c = cmp x k in
      if c = 0 then Node (l, x, r, h)
      else if c < 0 then
        let nl = add_one_SPECIAL cmp x l in
        bal nl k r
      else
        let nr = add_one_SPECIAL cmp x r in
        bal l k nr
  | Empty -> Node (Empty, x, Empty, 1)

(* Oryginalny join, zmienione tylko dodawanie *)
(* Złożoność - log n - tak jak oryginalny join, add_one_SPECIAL też log n *)
let rec join cmp l v r =
  match (l, r) with
    (Empty, _) -> add_one_SPECIAL cmp v r
  | (_, Empty) -> add_one_SPECIAL cmp v l
  | (Node(ll, lv, lr, lh), Node(rl, rv, rr, rh)) ->
      if lh > rh + 2 then bal ll lv (join cmp lr v r) else
      if rh > lh + 2 then bal (join cmp l v rl) rv rr else
      make l v r

(* TYM SPLITEM MOŻNA ZASTĄPIĆ SPLIT1 w ADD i REMOVE *)
(* KOSZT ZAMORTYZOWANY TEN SAM, TESTY DZIAŁAJĄ 30% SZYBCIEJ *)
(* PO PROSTU OGRANICZA TROCHĘ WYWOŁANIA REKURENCYJNE ZWYKŁEGO SPLIT *)
(* ALE JEST DUŻO BARDZIEJ SKOMPLIKOWANA WIĘĆ ZOSTAWIAM ZWYKŁY SPLIT1 *)
(* ŻEBY KOŻYSTAĆ Z GOTOWYCH ROZWIĄZAŃ *)

(* ZMIENIONY SPLIT, funkcja pomocnicza*)
(* Bierze przedział [a,b] i set, zwraca lewe poddrzewo gdzie wszystkie elementy <a i prawe, gdzie wysztkie elementy > b*)
(* let split_pom x { cmp = cmp; set = set } =
  let rec loop x = function
      Empty ->
        (Empty, false, Empty)
    | Node (l, v, r, _) ->
        let c = cmp x v in
        if c = 0
          then
            let how_intersect = intersection v x in
            if how_intersect = 2
              then (l, true, r)
            else if how_intersect =  0 
              then
              let (all_smaller_l,_,all_smaller_r) = loop x l in
              let (all_greater_l,_,all_greater_r) = loop x r in
              let new_left =
              if all_smaller_l = Empty then
              if all_smaller_r = Empty then Empty
                  else
                    napraw all_smaller_r 
                else
                  napraw( merge all_smaller_l all_smaller_r)
                in
              let new_right =
              if all_greater_l = Empty then
              if all_greater_r = Empty then Empty
                  else
                    napraw all_greater_r 
                else
                  napraw( merge all_greater_l all_greater_r)
                in
              (new_left,false,new_right)
            else if how_intersect = 1
              then 
              let (all_smaller_l,_,all_smaller_r) = loop x l in
              let new_left =
              if all_smaller_l = Empty then
              if all_smaller_r = Empty then Empty
                  else
                    napraw all_smaller_r 
                else
                  napraw ( merge all_smaller_l all_smaller_r)
                in
                (new_left,false,r)
            else 
              let (all_greater_l,_,all_greater_r) = loop x r in
              let new_right =
              if all_greater_l = Empty then
              if all_greater_r = Empty then Empty
                  else
                    napraw all_greater_r 
                else
                  napraw( merge all_greater_l all_greater_r)
                in
                (l,false,new_right)

        else if c < 0 then
          let (ll, pres, rl) = loop x l in (ll, pres, join cmp rl v r)
        else
          let (lr, pres, rr) = loop x r in (join cmp l v lr, pres, rr)
  in
  let setl, pres, setr = loop x set in
  { cmp = cmp; set = setl }, pres, { cmp = cmp; set = setr } *)



(* oryginalny split, tu używany jako funkcja pomocnicza do mojego split *)
let split1 x { cmp = cmp; set = set } =
  let x = (x,x) in
  let rec loop x = function
      Empty ->
        (Empty, false, Empty)
    | Node (l, v, r, _) ->
        let c = cmp x v in
        if c = 0 then (l, true, r)
        else if c < 0 then
          let (ll, pres, rl) = loop x l in (ll, pres, join cmp rl v r)
        else
          let (lr, pres, rr) = loop x r in (join cmp l v lr, pres, rr)
  in
  let setl, pres, setr = loop x set in
  { cmp = cmp; set = setl }, pres, { cmp = cmp; set = setr }


let split_just_lower x { cmp = cmp; set = set } =
  let x = (x,x) in
  let rec loop x = function
      Empty ->
        (Empty, false, Empty)
    | Node (l, v, r, _) ->
        let c = cmp x v in
        if c = 0 then (l, true, r)
        else if c < 0 then
          let (ll, pres, rl) = loop x l in (ll, pres, Empty)
        else
          let (lr, pres, rr) = loop x r in (join cmp l v lr, pres, rr)
  in
  let setl, _, _ = loop x set in
  { cmp = cmp; set = setl }

let split_jush_higher x { cmp = cmp; set = set } =
  let x = (x,x) in
  let rec loop x = function
      Empty ->
        (Empty, false, Empty)
    | Node (l, v, r, _) ->
        let c = cmp x v in
        if c = 0 then (l, true, r)
        else if c < 0 then
          let (ll, pres, rl) = loop x l in (ll, pres, join cmp rl v r)
        else
          let (lr, pres, rr) = loop x r in (Empty, pres, rr)
  in
  let _, _, setr = loop x set in
  { cmp = cmp; set = setr }
(* DODAWANIE *)
(* Dla add [a,b] do set wywołujemy split1 od a i split b od a żeby dostać same większe i same mniejsze*)
(* łączymy je wstawiając [a,b] w środek i naprawiając drzewo funkcją napraw *)
(* ZŁOŻONOŚĆ - 2x split w czasie stała razy log n + log n na naprawe*)
let add_one cmp x set = 
    match set with
    | Node(l, k, r, h) ->
    (
        let (pocz_x,kon_x) = x in
        let pocz_x_temp = 
          if pocz_x = min_int
            then min_int + 1
          else pocz_x
        in
        let kon_x_temp = 
          if kon_x = max_int
            then max_int - 1
          else kon_x
        in

        let dolny = mem_przedzial_zawierajacy (pocz_x_temp-1,pocz_x_temp-1) set in
        let gorny = mem_przedzial_zawierajacy (kon_x_temp+1,kon_x_temp+1) set in

        let zmieniony_x = 
        match dolny,gorny with
        | (1,-1), (1,-1) -> x
        | (a,b) , (1,-1) -> (a,kon_x)
        | (1,-1), (c,d)  -> (pocz_x,d)
        | (a,b) , (c,d)  -> (a,d)
        in
        
        (* TO JEST SZYBSZE ALE BARDZIEJ SKOMPLIKOWANE *)

        (* let same_mniejsze,_, same_wieksze = split_pom (pocz_x-1,kon_x+1) { cmp = cmp_przedzialy; set = set } in *)

        (* ------------- *)

        (* TO JEST WOLNIEJSZE ALE MNIEJ SKOMPLIKOWANE *)

        let same_mniejsze= split_just_lower (pocz_x_temp-1) { cmp = cmp_przedzialy; set = set } in
        let same_wieksze  = split_jush_higher (kon_x_temp+1) { cmp = cmp_przedzialy; set = set }
        in
        (* ------------- *)


        let nowe = join cmp_przedzialy same_mniejsze.set zmieniony_x same_wieksze.set
        in

        napraw nowe
    )
    | Empty -> Node (Empty, x, Empty, 1);;

let add x { cmp = cmp; set = set } =
  { cmp = cmp; set = add_one cmp x set }


let split x { cmp = cmp; set = set } = 
  let l, pres, r = split1 x { cmp = cmp; set = set } in
  if pres = false
    then l, pres, r
  else
    let (dolny_pocz,dolny_kon) = mem_przedzial_zawierajacy (x-1,x-1) set in
    let (gorny_pocz,gorny_kon) = mem_przedzial_zawierajacy (x+1,x+1) set in
    let l = 
      if dolny_pocz = 1 && dolny_kon = -1
        then l
      else
        add (dolny_pocz,x-1) l in
    let r = 
      if gorny_pocz = 1 && gorny_kon = -1
        then r
      else
      add (x+1,gorny_kon) r in
    l, pres, r;;


let remove x { cmp = cmp; set = set } =
    let wyn = 
    match set with
    | Node (l, k, r, _) ->(
        let (pocz_x,kon_x) = x in
        let (dolny_pocz,temp1) = mem_przedzial_zawierajacy (pocz_x,pocz_x) set in
        let (temp2,gorny_kon) = mem_przedzial_zawierajacy (kon_x,kon_x) set in

        (* TO JEST SZYBSZE ALE BARDZIEJ SKOMPLIKOWANE *)

        (* let same_mniejsze,_, same_wieksze = split_pom (pocz_x-1,kon_x+1) { cmp = cmp_przedzialy; set = set } in *)

        (* ------------- *)

        (* TO JEST WOLNIEJSZE ALE MNIEJ SKOMPLIKOWANE *)

        let same_mniejsze= split_just_lower (pocz_x) { cmp = cmp_przedzialy; set = set } in
        let same_wieksze  = split_jush_higher (kon_x) { cmp = cmp_przedzialy; set = set }
        in
        (* ------------- *)


        let same_mniejsze =
        if pocz_x - 1 >= dolny_pocz && (dolny_pocz!= 1 || temp1 != -1) then
            add (dolny_pocz,pocz_x-1) same_mniejsze
          else
          same_mniejsze in
        let same_wieksze = 
          if kon_x + 1 <= gorny_kon &&  (temp2 != 1 || gorny_kon != -1) then
            add (kon_x+1,gorny_kon) same_wieksze
          else
          same_wieksze in
        if is_empty same_mniejsze then
        if is_empty same_wieksze then Empty
        else
          merge same_mniejsze.set same_wieksze.set
        else
          merge same_mniejsze.set same_wieksze.set
    )
    | Empty -> Empty
    in
  { cmp = cmp; set = wyn }

(* Wystarczy z x zrobić jednoelementowy przedział i działa *)
let mem x { cmp = cmp; set = set } =
  let x = (x,x) in
  let rec loop = function
    | Node (l, k, r, _) ->
        let c = cmp x k in
        c = 0 || loop (if c < 0 then l else r)
    | Empty -> false in
  loop set

(* zwraca przedzial [a,b], jeżeli x \in [a,b], lub  Brak  *)

let iter f { set = set } =
  let rec loop = function
    | Empty -> ()
    | Node (l, k, r, _) -> loop l; f k; loop r in
  loop set

let fold f { cmp = cmp; set = set } acc =
  let rec loop acc = function
    | Empty -> acc
    | Node (l, k, r, _) ->
          loop (f k (loop acc l)) r in
  loop acc set

let elements { set = set } = 
  let rec loop acc = function
      Empty -> acc
    | Node(l, k, r, _) -> loop (k :: loop acc r) l in
  loop [] set

let rec count_nodes = function
  | Empty -> 0
  | Node(l, k, r, _) ->
    snd k - fst k + 1 + count_nodes l + count_nodes r;;

let below x { cmp = cmp; set = set } =
  let x = (x,x) in
  let rec loop = function
  | Empty -> 0
  | Node(l, k, r, _) ->
    let c = cmp x k in
      if c = -1
        then loop l
      else if c = 0
        then
          let wyn_temp = count_nodes l 
          in
          if wyn_temp < 0 
            then wyn_temp
          else
          let temp = fst x - fst k
          in
            if temp < 0 
              then max_int
            else
              temp + 1 + wyn_temp
      else
      let temp = snd k - fst k
          in
            if temp < 0 
              then max_int
            else
              temp + 1 + count_nodes l + loop r
  in
  let wyn = loop set
  in
  if wyn < 0 
    then max_int
  else
    wyn;;

