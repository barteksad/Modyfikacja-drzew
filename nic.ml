open PSet

let x = empty;;

let x = add (50 ,100134) x;;
let x = add (51 ,100134) x;;
let x = add (52 ,100134) x;;
let x = add (53 ,100134) x;;
let x = add (54 ,100134) x;;
let x = add (55 ,100134) x;;
let x = add (56 ,100134) x;;
let x = add (57 ,100134) x;;
let x = add (58 ,100134) x;;
let x = add (59 ,100134) x;;
let x = add (60 ,100134) x;;
let x = add (70 ,100134) x;;
let x = add (80 ,100134) x;;
let x = add (90 ,100134) x;;
let x = add (100,100134)  x;;
let x = add (510,100134)  x;;
let x = add (540,100134)  x;;
let x = add (550,100134)  x;;
let x = add (570,100134)  x;;
let x = add (580,100134)  x;;
let x = add (590,100134)  x;;
let x = add (650,100134)  x;;
let x = add (750,100134)  x;;
let x = add (751,100134)  x;;
let x = add (752,1000) x ;;
let x = add (753,1000) x ;;
let x = add (754,1000) x ;;
let x = add (755,1000) x ;;
let x = add (756,1000) x ;;
let x = add (757,1000) x ;;
let x = add (758,1000) x ;;
let x = add (759,1200) x ;;
let x = add (760,1200) x ;;
let x = add (770,1200) x ;;
let x = add (771,1200) x ;;
let x = add (772,1200) x ;;
let x = add (773,1200) x ;;
let x = add (774,1200) x ;;
let x = add (775,1200) x ;;
let x = add (776,1200) x ;;
let x = add (-777,1200)  x;;
let x = add (-778,1200)  x;;
let x = add (-779,1200)  x;;
let x = add (-780,1200)  x;;
let x = add (-781,1200)  x;;
let x = add (-782,1200)  x;;
let x = add (-783,1200)  x;;
let x = add (-784,1200)  x;;
let x = add (-785,1200)  x;;
let x = add (-786,1200)  x;;


let y = empty;;
let y = add 3 y;; 

assert (is_valid x);;
assert (is_valid y);;

(* let z = join compare x.set 2 y.set;; *)

(* (20,25) *)let same_mniejsze =
        if pocz_x - 1 >= dolny_pocz && (dolny_pocz,temp1) != (1,-1)then
            add (dolny_pocz,pocz_x-1) same_mniejsze
          else
          same_mniejsze



let good = ref 0 and bad = ref 0

let check nr warunek wartosc =
  if warunek = wartosc then
    begin
      (* Printf.printf "OK - TEST nr %d \n" nr; *)
      incr good
    end
  else
    begin
      Printf.printf "Fail: %d\n" nr;
      assert (false);
    end;;

(* open ISet;; *)

let liczba a = List.length (elements a)

(* Testy na add i remove *)

let a = empty
let a = add (17, 20) a
let a = add (5, 8) a
let a = add (1, 2) a
let a = add (10, 12) a
let a = add (28, 35) a
let a = add (22, 23) a
let a = add (40, 43) a
let a = add (37, 37) a;;

check 1 (is_empty a) false;;
check 2 (mem 29 a) true;;
check 3 (mem 21 a) false;;
check 4 (mem 38 a) false;;
check 5 (mem 37 a) true;;
(* check 6 (below 8 a = below 9 a) true;; *)
(* check 7 (below 29 a) 17;; *)
check 8 (liczba a) 8;;

let a = add (37, 42) a;;

check 9 (liczba a) 7;;
check 10 (mem 37 a) true;;
check 11 (mem 38 a) true;;
check 12 (mem 39 a) true;;
check 13 (mem 40 a) true;;
check 14 (mem 41 a) true;;
check 15 (mem 42 a) true;;
check 16 (mem 44 a) false;;
(* check 17 (below 38 a = below 39 a) false;; *)

let tmp = remove (8, 22) a;;
let tmp = add (8, 22) tmp;;

check 18 (elements tmp = elements a) false;;

(* Testy na split *)

let (l, exists, p) = split 9 a;;

check 19 exists false;;
check 20 (liczba l) 2;;
check 21 (liczba p) 5;;
check 22 (mem 10 l) false;;
check 23 (mem 9 l) false;;
check 24 (mem 8 l) true;;
check 25 (mem 1 l) true;;
check 26 (mem 9 p) false;;
check 27 (mem 10 p) true;;
check 28 (mem 17 p) true;;
check 29 (mem 29 p) true;;
check 30 (mem 24 p) false;;
check 31 (mem 38 p) true;;
check 32 ((elements l @ elements p) = elements a) true;;

let (l, exists, p) = split 21 a;;

check 33 exists false;;
check 34 ((elements l @ elements p) = elements a) true;;

let (l, exists, p) = split 15 a;;
check 35 exists false;;
check 36 ((elements l @ elements p) = elements a) true;;


let b = empty
let b = add (5, 10) b
let b = add (40, 50) b
let b = add (20, 25) b
let b = add (12, 14) b
let b = add (17, 18) b
let b = add (52, 60) b
let b = add (62, 80) b
let b = add (83, 100) b;;

check 37 (mem 41 b) true;;
check 38 (mem 11 b) false;;

let d = empty;;
let (l, ex, p) = split 0 d;;

check 39 (is_empty l) true;;
check 40 (is_empty p) true;;

let d = add (17, 30) d;;
let d = add (1, 3) d;;
let d = add (10, 10) d;;
let d = remove (11, 11) d;;
let d = add (12, 14) d;;
let d = add (32, 35) d;;
let d = add (38, 40) d;;

(* check 41 (below 36 d = below 37 d) true;; *)

let d = add (36, 37) d;;

(* check 42 (below 36 d = below 37 d) false;; *)

let d = remove (37, 37) d;;
(* check 43 (below 36 d = below 37 d) true;; *)

let d = remove (20, 21) d;;

check 44 (elements d) [(1, 3); (10, 10); (12, 14); (17, 19); (22, 30); (32, 36); (38, 40)];;

let (l, ex, p) = split 15 d;;
check 144 (elements l) [(1, 3); (10, 10); (12, 14)];;
check 145 (elements p) [(17, 19); (22, 30); (32, 36); (38, 40)];;

check 45 ((elements l @ elements p) = elements d) true;;
check 46 (liczba l, liczba p) (3, 4);;

check 47 (mem 13 l) true;;
check 48 (mem 14 l) true;;
check 49 ex false;;

let (l, ex, p) = split 25 d;;

check 50 ex true;;
check 51 (elements l) [(1, 3); (10, 10); (12, 14); (17, 19); (22, 24)];;
check 52 (elements p) [(26, 30); (32, 36); (38, 40)];;
