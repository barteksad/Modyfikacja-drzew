(* ------------------------------------------------------------ *)
(* AUTOR : BARTEK SADLEJ *)
(* CODE_REVIEW : MARYSIA ŚMIGIELSKA *)
(* ------------------------------------------------------------ *)

(* każde odwołanie do n w opisywanych złożonościach odnosi się do n-liczba elementów w drzewie (przedziałów) *)


(* FNKCJA PORÓWNUJĄCA PRZEDZIAŁY NIE DOKŁADNIE*)
(* 0  - równość oznaczające, że przecięcie x y nie jest zbiorem pustym *)
(* -1 -  max(x) < min(y) *)
(* +1 -  min(x) > max (y)*)
let cmp_przedzialy (x_pocz,x_kon) (y_pocz,y_kon) =
    if x_kon  < y_pocz then -1 else
    if x_pocz > y_kon  then  1 else
                               0;;


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

(* Type set- krotka int*int  i liczba elementów mniejszych od min(przechowywany_przedział) *)
type set =
  | Empty
  | Node of set * (int*int) *  set * int * int

type t =
  {
    cmp : int*int -> int*int -> int;
    set : set;
  }

(* nie zmienione *)
let height = function
  | Node(_, _, _, h,_) -> h
  | Empty -> 0

(* Zwraca ilośc mniejszych elementów od k przy wywoływaniu make *)
let rec get_lower = function
  | Node(_, value, r, _,lw) ->
      let g = (snd value - fst value + 1 +  lw) + (get_lower r)
        in if g <= 0
          then max_int
        else 
          g
  | Empty -> 0

(* nie zmienione *)
let make l k r = Node (l, k, r, max (height l) (height r) + 1,get_lower l)

(* nie zmienione *)
let bal l k r =
  let hl = height l in
  let hr = height r in
  if hl > hr + 2 then
    match l with
    | Node (ll, lk, lr, _,_) ->
        if height ll >= height lr then make ll lk (make lr k r)
        else
          (match lr with
          | Node (lrl, lrk, lrr, _,_) ->
              make (make ll lk lrl) lrk (make lrr k r) 
          | Empty -> assert false)
    | Empty -> assert false
  else if hr > hl + 2 then
    match r with
    | Node (rl, rk, rr, _,_) ->
        if height rr >= height rl then make (make l k rl) rk rr
        else
          (match rl with
          | Node (rll, rlk, rlr, _,_) ->
              make (make l k rll) rlk (make rlr rk rr)
          | Empty -> assert false)
    | Empty -> assert false
  else Node (l, k, r, max hl hr + 1,get_lower l)

(* nie zmienione *)
let rec min_elt = function
  | Node (Empty, k, _, _,_) -> k
  | Node (l, _, _, _,_) -> min_elt l
  | Empty -> raise Not_found

(* Usuwa minimalny element i aktualizuje liczbe przechowywanych elementów w poddrzewach w każdym węźle *)
(* ZŁOŻONOŚĆ: log n - wyszukujemy dany element i wracamy tą samą ścierzką *)
let remove_min_elt set_ = 
  let rec pom = function
  | Node (Empty, k, r, _,_) -> (r,snd k - fst k + 1)
  | Node (l, k, r, h,lw1) -> (
    let (l2,min_val) = pom l in
    match l2 with
    | Node (l3, k2, r2, h2, lw2)  -> (bal (Node(l3,k2,r2,h2,lw2-min_val)) k r,min_val)
    | Empty -> (bal Empty k r,min_val) 
    )
  | Empty -> invalid_arg "ISet.remove_min_elt"

  in (fst (pom set_));;

(* nie zmienione *)
(* warunek na wejściu, wszystkie przedziały w t1 < przedziałów t2 *)
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
  x.set = Empty;;


(* ten sam kod co mem, tylko zamiast true/false zwracamy konkretny element lub (1,-1) jeśli nie znaleziono*)
(* bierze tylko szukay element i set *)
(* ZŁOŻONOŚĆ: log n - wyszukanie w poprawnym drzewie avl *)
let mem_przedzial_zawierajacy x set = 
  let rec loop = function
    | Node (l, k, r, _,_) ->
        let c = cmp_przedzialy x k in
        if c = 0 
            then k 
        else
          loop (if c < 0 then l else r)
    | Empty -> (1,-1) in
  loop set

(* funkcja sprawdzająca, czy set jest poprawnym drzewem AVL, w tym przypadku lheight +-2 = rheight *)
(* ZŁOŻONOŚĆ : stała - sprawdzamy tylko wartość w height w l oraz r *)
let is_valid x = 
  match x with
  | Node(l, k, r, h,_) ->
    let left_height = height l in
    let right_height = height r in
    abs (left_height - right_height) < 3
  | Empty -> true;;


(* funkcja pomocnicza do dodawania i usuwania elementów *)
(* wywołuje ball dopóki is_valid nie zwróci true *)
(* Funkcja zwraca poprawne drzewo, ponieważ ball za każdym wywołaniem *)
(* poprawia różnice wysokości pomiędzy prawym i lewym poddrzewem o 1 *)

(* ZŁOŻONOŚĆ: log n - najgorszy przypadek- wysokość jednego drzewa = 1, drugiego log n, *)
(* wywołuje ball max((|log (l.height) - log(r.height)|)-2,0) razy, a ball działa w czasie stałym*)
let rec napraw x = 
    if is_valid x 
        then x 
    else
    match x with
    | Node(l,k,r,h,_) -> napraw (bal l k r)
    | Empty -> Empty;;


(* Oryginalny join, zamienione tylko add_one na bal puste 1-element drzewo*)
(* warunek na wejściu, wszystkie przedziały w l < przedziałów r, v pomiędzy  *)
(* Złożoność - log n - tak jak oryginalny join + bal *)
let rec join cmp l v r =
  match (l, r) with
  | (Empty, _) -> bal Empty v r 
  | (_, Empty) -> bal l v Empty
  | (Node(ll, lv, lr, lh,_), Node(rl, rv, rr, rh,_)) ->
      if lh > rh + 2 then bal ll lv (join cmp lr v r) else
      if rh > lh + 2 then bal (join cmp l v rl) rv rr else
      make l v r


(* oryginalny split, tu używany jako funkcja pomocnicza do mojego split *)
let split_original x { cmp = cmp; set = set } =
  let x = (x,x) in
  let rec loop x = function
      Empty ->
        (Empty, false, Empty)
    | Node (l, v, r,_,_) ->
        let c = cmp x v in
        if c = 0 then (l, true, r)
        else if c < 0 then
          let (ll, pres, rl) = loop x l in (ll, pres, join cmp rl v r)
        else
          let (lr, pres, rr) = loop x r in (join cmp l v lr, pres, rr)
  in
  let setl, pres, setr = loop x set in
  { cmp = cmp; set = setl }, pres, { cmp = cmp; set = setr }


(* Split zwracający tylko poddrzewo zlożone z mniejszych wartości niż x, wykonuje przez to mniej operacji *)
(* bo nie łączy większych poddrzew *)
(* Złożoność: O(log n) *)
let split_just_lower x { cmp = cmp; set = set } =
  let x = (x,x) in
  let rec loop x = function
      Empty ->
        (Empty, false, Empty)
    | Node (l, v, r,_,_) ->
        let c = cmp x v in
        if c = 0 then (l, true, r)
        else if c < 0 then
          let (ll, pres, _) = loop x l in (ll, pres, Empty)
        else
          let (lr, pres, _) = loop x r in (join cmp l v lr, pres, Empty)
  in
  let setl, _, _ = loop x set in
  { cmp = cmp; set = setl }


(* Split zwracający tylko poddrzewo zlożone z większych wartości niż x, wykonuje przez to mniej operacji *)
(* bo nie łączy mniejszych poddrzew *)
(* Złożoność: O(log n) *)
let split_just_higher x { cmp = cmp; set = set } =
  let x = (x,x) in
  let rec loop x = function
      Empty ->
        (Empty, false, Empty)
    | Node (l, v, r,_,_) ->
        let c = cmp x v in
        if c = 0 then (l, true, r)
        else if c < 0 then
          let (_, pres, rl) = loop x l in (Empty, pres, join cmp rl v r)
        else
          let (_, pres, rr) = loop x r in (Empty, pres, rr)
  in
  let _, _, setr = loop x set in
  { cmp = cmp; set = setr }


(* DODAWANIE *)
(* Dla add [a,b] do set wywołujemy Wywołuje split_just_higher & split_just_lower dostając wszystkie przedziały ściśle mniejsze i większe od x*)
(* łączymy je wstawiając [a,b] w środek i naprawiając drzewo funkcją napraw *)
(* ZŁOŻONOŚĆ -  split w czasie O(log n) + log n na naprawe*)
let add_one cmp x set = 
    match set with
    | Node(l, k, r, h,_) ->
    (

        (* if-y zapewniające działanie dla max_int, min_int *)
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
        (* --- *)

        let dolny = mem_przedzial_zawierajacy (pocz_x_temp-1,pocz_x_temp-1) set in
        let gorny = mem_przedzial_zawierajacy (kon_x_temp+1,kon_x_temp+1) set in

        let zmieniony_x = 
        match dolny,gorny with
        | (1,-1), (1,-1) -> x
        | (a,b) , (1,-1) -> (a,kon_x)
        | (1,-1), (c,d)  -> (pocz_x,d)
        | (a,b) , (c,d)  -> (a,d)
        in
       
        let same_mniejsze= split_just_lower (pocz_x_temp-1) { cmp = cmp_przedzialy; set = set } in
        let same_wieksze  = split_just_higher (kon_x_temp+1) { cmp = cmp_przedzialy; set = set }
        in


        let nowe = join cmp_przedzialy same_mniejsze.set zmieniony_x same_wieksze.set
        in

        napraw nowe
    )
    | Empty -> Node (Empty, x, Empty, 1,0);;

let add x { cmp = cmp; set = set } =
  { cmp = cmp; set = add_one cmp x set }


(* split odpowiadający specyfikacji iSet.mli *)
(* nowy split dodający prawe i lewe dopełnienie  [a,x-1] i [x+1,b] ,jeśli x \in [a,b] i a<=x && b>=x, do zwracanych drzew *)
(* ZłOŻONOŚĆ: O(log n) na split i O(log n) na add *)
let split x { cmp = cmp; set = set } = 
  let l, pres, r = split_original x { cmp = cmp; set = set } in
  if pres = false
    then l, pres, r
  else
    let (dolny_pocz,dolny_kon) = mem_przedzial_zawierajacy (x-1,x-1) set in
    let (gorny_pocz,gorny_kon) = mem_przedzial_zawierajacy (x+1,x+1) set in
    let l = 
      if dolny_pocz = 1 && dolny_kon = -1
        then l.set
      else
        add_one cmp (dolny_pocz,x-1) l.set in
    let r = 
      if gorny_pocz = 1 && gorny_kon = -1
        then r.set
      else
      add_one cmp (x+1,gorny_kon) r.set in
    { cmp = cmp; set = l } , pres, { cmp = cmp; set = r } ;;


(* Wywołuje split_just_higher & lower dostając wszystkie przedziały ściśle mniejsze i większe od x *)
(* i ewentualnie dodaje depełnienia przedziałów w których był x ale nie usuwaliśmy całych *)
(* ZłOŻONOŚĆ: O(log n) na split i O(log n) na add *)
let remove x { cmp = cmp; set = set } =
    let wyn = 
    match set with
    | Node (l, k, r,_,_) ->(
        let (pocz_x,kon_x) = x in
        let (dolny_pocz,temp1) = mem_przedzial_zawierajacy (pocz_x,pocz_x) set in
        let (temp2,gorny_kon) = mem_przedzial_zawierajacy (kon_x,kon_x) set in

        let same_mniejsze= split_just_lower (pocz_x) { cmp = cmp_przedzialy; set = set } in
        let same_wieksze  = split_just_higher (kon_x) { cmp = cmp_przedzialy; set = set }
        in


        let same_mniejsze =
        if pocz_x - 1 >= dolny_pocz && (dolny_pocz!= 1 || temp1 != -1) then
            add_one cmp (dolny_pocz,pocz_x-1) same_mniejsze.set
          else
          same_mniejsze.set in
        let same_wieksze = 
          if kon_x + 1 <= gorny_kon &&  (temp2 != 1 || gorny_kon != -1) then
            add_one cmp (kon_x+1,gorny_kon) same_wieksze.set
          else
          same_wieksze.set in

        napraw (merge same_mniejsze same_wieksze)
    )
    | Empty -> Empty
    in
  { cmp = cmp; set = wyn }

(* Wystarczy z x zrobić jednoelementowy przedział i działa *)
let mem x { cmp = cmp; set = set } =
  let x = (x,x) in
  let rec loop = function
    | Node (l, k, r,_,_) ->
        let c = cmp x k in
        c = 0 || loop (if c < 0 then l else r)
    | Empty -> false in
  loop set


(* nie zmienione *)
let iter f { set = set } =
  let rec loop = function
    | Empty -> ()
    | Node (l, k, r,_,_) -> loop l; f k; loop r in
  loop set

(* nie zmienione *)
let fold f { cmp = cmp; set = set } acc =
  let rec loop acc = function
    | Empty -> acc
    | Node (l, k, r,_,_) ->
          loop (f k (loop acc l)) r in
  loop acc set

(* nie zmienione *)
let elements { set = set } = 
  let rec loop acc = function
      Empty -> acc
    | Node(l, k, r,_,_) -> loop (k :: loop acc r) l in
  loop [] set;;



(* Funkcja below *)
(* Każdy węzeł trzyma informacje o liczbie elementóœ mniejszych od niego- nazwijmy ją lw*)
(* Wystarczy więc znaleść przedział zawierający x, *)
(* dodając wszystkie wartości lw + liczbe elementów w przechodzonych przedziałach *)
(* oraz liczbe elementów z ostatniego przedziały <=x *)

(* ZŁOŻONOŚĆ - log n *)
(* wyszukujemy tylko przedział z x-em w poprawnym drzewie avl *)
let below x { cmp = cmp; set = set } = 
  let rec loop acc set_ = 
    match set_ with
    | Node (l, k, r, _,lw) ->
        let c = cmp_przedzialy (x,x) k in
        if c = 0 
            then (acc + lw + x - (fst k) + 1) 
        else
          if c < 0
            then
              loop acc l 
          else
            loop (acc + lw + (snd k) - (fst k) + 1 ) r

    | Empty -> acc in
  let wyn = loop 0 set 
  in

  (* if-y potrzebne żeby działało dla MAX_INT *)
  if wyn > 0
    then wyn
  else if wyn < 0
    then max_int
  else 
      try 
        if fst (min_elt set) <= x
          then max_int
        else 0
      with
      Not_found -> 0
      
        

