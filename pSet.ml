(*
 * PSet - Polymorphic sets
 * Copyright (C) 1996-2003 Xavier Leroy, Nicolas Cannasse, Markus Mottl
 *
 * This library is free software; you can redistribute it and/or
 * modify it under the terms of the GNU Lesser General Public
 * License as published by the Free Software Foundation; either
 * version 2.1 of the License, or (at your option) any later version,
 * with the special exception on linking described in file LICENSE.
 *
 * This library is distributed in the hope that it will be useful,
 * but WITHOUT ANY WARRANTY; without even the implied warranty of
 * MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the GNU
 * Lesser General Public License for more details.
 *
 * You should have received a copy of the GNU Lesser General Public
 * License along with this library; if not, write to the Free Software
 * Foundation, Inc., 59 Temple Place, Suite 330, Boston, MA  02111-1307  USA
 *)

type 'k set =
  | Empty
  | Node of 'k set * 'k * 'k set * int * int

type 'k t =
  {
    cmp : 'k -> 'k -> int;
    set : 'k set;
  }

let height = function
  | Node (_, _, _, h,_) -> h
  | Empty -> 0

(* FUNKCJE POMOCNICZE DO BELOW *)

(* zwraca ilość elementów mniejszych niż dany *)
let num_smaller = function
| Node(_, _, _, _, count)->count
| Empty -> 0;;


(* Po dodaniu,usunięciu aktualizujemy ilość mniejszych *)
let rec plus_minus_some x how_many = 
  if how_many = 0 then x else
  match x with
  | Empty -> Empty
  | Node(a,b,c,d,e) -> 
    let a = plus_minus_some a how_many in
    let c = plus_minus_some c how_many in
    Node(a,b,c,d,e+how_many);; 

(* ------------------------- *)

let make l k r = 
  let count = num_smaller l in
  Node (l, k, r, max (height l) (height r) + 1,count + 1);;

let bal l k r =
  let hl = height l in
  let hr = height r in
  if hl > hr + 2 then
    match l with
    | Node (ll, lk, lr, _,_) ->
        if height ll >= height lr then make ll lk (make lr k r )
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
  else 
  (* ilość mniejszych to ilość mniejszych od lewego syna + 1, bo jeszcze lewy syn *)
  let count = num_smaller l in
  Node (l, k, r, max hl hr + 1,count+1);;

let rec min_elt = function
  | Node (Empty, k, _, _,_) -> k
  | Node (l, _, _, _,_) -> min_elt l
  | Empty -> raise Not_found

let rec remove_min_elt = function
  | Node (Empty, _, r, _,_) -> plus_minus_some r (-1)
  | Node (l, k, r, _,_) -> bal (remove_min_elt l) k (plus_minus_some r (-1))
  | Empty -> invalid_arg "PSet.remove_min_elt"

let merge t1 t2 =
  match t1, t2 with
  | Empty, _ -> t2
  | _, Empty -> t1
  | _ ->
      let k = min_elt t2 in
      bal t1 k (remove_min_elt t2)

let create cmp = { cmp = cmp; set = Empty }
let empty = { cmp = compare; set = Empty }

let is_empty x = 
  x.set = Empty

let rec add_one cmp x all_count = function
  | Node (l, k, r, h,count) ->
      let c = cmp x k in
      (* count się nie zmienia jeśli ten element już jest i nie dodajemy go drugi raz *)
      if c = 0 then Node (l, x, r, h,count)
      else if c < 0 then
        let nl = add_one cmp x (count-1) l in
        bal nl k (plus_minus_some r 1)
      else
        let nr = add_one cmp x (count+1) r in
        bal l k nr
  | Empty -> Node (Empty, x, Empty, 1,all_count)

let add x { cmp = cmp; set = set } =
  { cmp = cmp; set = add_one cmp x 0 set }

let rec join cmp l v r =
  match (l, r) with
    (Empty, _) -> add_one cmp v 0 r
  | (_, Empty) -> add_one cmp v 0 l
  | (Node(ll, lv, lr, lh,_), Node(rl, rv, rr, rh,_)) ->
      if lh > rh + 2 then bal ll lv (join cmp lr v r) else
      if rh > lh + 2 then bal (join cmp l v rl) rv rr else
      make l v r 

let split x { cmp = cmp; set = set } =
  let rec loop x = function
      Empty ->
        (Empty, false, Empty)
    | Node (l, v, r, _,count) ->
        let c = cmp x v in
        if c = 0 then (l, true, r)
        else if c < 0 then
          let (ll, pres, rl) = loop x l in (ll, pres, join cmp rl v r)
        else
          let (lr, pres, rr) = loop x r in (join cmp l v lr, pres, rr)
  in
  let setl, pres, setr = loop x set in
  let how_many_deleted = num_smaller setr - num_smaller setl + 1 in
  { cmp = cmp; set = setl }, pres, { cmp = cmp; set =  plus_minus_some setr (-how_many_deleted) }

let remove x { cmp = cmp; set = set } =
  let rec loop = function
    | Node (l, k, r, _,count) ->
        let c = cmp x k in
        if c = 0 then merge l (plus_minus_some r (-1)) else
        if c < 0 then bal (loop l) k r else bal l k (loop r)
    | Empty -> Empty in
  { cmp = cmp; set = loop set }

let mem x { cmp = cmp; set = set } =
  let rec loop = function
    | Node (l, k, r, _,count) ->
        let c = cmp x k in
        c = 0 || loop (if c < 0 then l else r)
    | Empty -> false in
  loop set

let exists = mem

let iter f { set = set } =
  let rec loop = function
    | Empty -> ()
    | Node (l, k, r, _,count) -> loop l; f k; loop r in
  loop set

let fold f { cmp = cmp; set = set } acc =
  let rec loop acc = function
    | Empty -> acc
    | Node (l, k, r, _,count) ->
          loop (f k (loop acc l)) r in
  loop acc set

let elements { set = set } = 
  let rec loop acc = function
      Empty -> acc
    | Node(l, k, r, _,count) -> loop (k :: loop acc r) l in
  loop [] set
