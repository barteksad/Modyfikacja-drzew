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