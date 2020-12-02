open PSet

(* TYP PRZEDZIAŁ *)
 (*oznaczający domknięty przedział [a,b] *)
type p = 
    Przedzial of int * int;;


(* FNKCJA PORÓWNUJĄCA PRZEDZIAŁY *)
(* 0  - równość oznaczające, że przecięcie t1 t2 nie jest zbiorem pustym *)
(* -1 -  max(t1) < min(t2) *)
(* +1 -  min(t1) > max (t2)*)
let cmp_przedzialy (Przedzial(t1_pocz,t1_kon)) (Przedzial(t2_pocz,t2_kon)) =
    if t1_kon  < t2_pocz then -1 else
    if t1_pocz > t2_kon  then  1 else
                               0;;


type t = p PSet.t;;  


let empty = 
    PSet.create cmp_przedzialy;;

