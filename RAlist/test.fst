module Test


open FStar.List.Tot.Base
open FStar.Mul
open FStar.Tactics

(* Some util functions I couldnt find
*)

val pow : a:pos -> e:nat -> pos
let rec pow a e = match e with
    | 0 -> 1
    | x -> a * (pow a (x - 1))

val pow_distr_sums_on_e : e1:nat -> e2:nat -> a:pos -> Lemma (pow a (e1 + e2) = (pow a e1)*(pow a e2))
let rec pow_distr_sums_on_e e1 e2 a = match e2 with
  | 0 -> ()
  | x -> pow_distr_sums_on_e e1 (x - 1) a

val pow_dec_on_e : e1:nat -> e2:nat{e2 > e1} -> a:pos -> Lemma (pow a e1 <= pow a e2)
let pow_dec_on_e e1 e2 a = begin
  pow_distr_sums_on_e (e2 - e1) e1 a
end

(*  comBiTree
    comBitree is a non empty COMplete BInary TREE with the height of the tree at type level
*)
type comBiTree 'a : (x:pos) -> Type =
    | Leaf : 'a -> comBiTree 'a 1
    | Branch : 'a -> #m:pos -> comBiTree 'a m -> comBiTree 'a m ->
        comBiTree 'a (m + 1)

val treeHeight : (#x:pos) -> comBiTree 'a x ->  y:pos{y = x}
let rec treeHeight (t:comBiTree 'a 'n) = match t with
    | Leaf _ -> 1
    | Branch _ t2 _ -> 1 + treeHeight t2

val treeSize : (#x:pos) -> comBiTree 'a x ->  y:pos{y = pow2 x - 1}
let rec treeSize (t:comBiTree 'a 'n) = match t with
  | Leaf _ -> 1
  | Branch _ t1 t2 -> 1 + treeSize t1 + treeSize t2

val preorder : (#x:pos) -> (#b:Type) -> t:comBiTree b x -> l:list b
let rec preorder #x #b t = match t with
  | Leaf a -> [a]
  | Branch a t1 t2 -> a :: (preorder t1) @ preorder t2

(* Should I do a Lemma stating what preorder does? It'd look very similar to the implementation. *)

val append_len: l1:list 'a -> l2:list 'a
                -> Lemma (requires True)
                        (ensures (length ( l1 @ l2) = length l1 + length l2))
let rec append_len l1 l2 = match l1 with
    | [] -> ()
    | hd::tl -> append_len tl l2


val random_lemma : 
                 #b:Type -> 
                 x:b -> 
                 l1:list b -> 
                 l2:list b -> 
                 Lemma (length (x :: l1 @ l2) = 1 + length l1 + length l2)
let rec random_lemma #b x l1 l2 = append_len (x::l1) l2

val preorder_keeps_the_elements : #n:pos -> #b:Type -> t:comBiTree b n -> Lemma (length (preorder t) = treeSize t)
let rec preorder_keeps_the_elements #n #b t = match t with
    | Leaf _ -> ()
    | Branch x t1 t2 -> begin
      preorder_keeps_the_elements t1;
      preorder_keeps_the_elements t2;
      random_lemma x (preorder t1) (preorder t2)
    end

val preorder_has_the_root_first : 
                                #n:pos -> 
                                #b:eqtype ->
                                x:b ->
                                t1:comBiTree b n -> 
                                t2:comBiTree b n -> 
                                Lemma 
                                  (preorder (Branch x t1 t2) = 
                                    x :: ((preorder t1) @ (preorder t2)))
let preorder_has_the_root_first #n #b x t1 t2 = () 

(* raNode
   It's a non empty linked list of strictly increasing comBiTrees
   With the height of the head tree at type level.
*)
type raNode 'a : (n:pos) -> Type =
    | Last : #m:pos -> comBiTree 'a m -> raNode 'a m
    | More : #m:pos -> #k:pos{k>m} -> comBiTree 'a m -> 
        raNode 'a k -> raNode 'a m

val lenRan : #x:pos -> #b:Type -> r:raNode b x -> Tot (y:pos) (decreases r)
let rec lenRan #x #b r  = match r with
    | Last _ -> 1
    | More _ m -> 1 + lenRan m

val toList : #x:pos -> #b:Type -> r:raNode b x -> Tot (list b) (decreases r)
let rec toList #x #b r = match r with
    | Last t -> preorder t
    | More t m -> preorder t @ (toList m)

val sizeRan : #x:pos -> #b:Type -> r:raNode b x -> Tot (y:pos{y = length (toList r)}) (decreases r)
let rec sizeRan #x #b r = match r with
    | Last t -> (preorder_keeps_the_elements t; treeSize t)
    | More t m -> begin
      preorder_keeps_the_elements t;
      append_len (preorder t) (toList m);
      treeSize t + sizeRan m
    end

val headTree : #n:pos -> #b:Type -> raNode b n -> comBiTree b n 
let headTree #n #b ran = match ran with
  | Last t -> t
  | More t _ -> t

(*
val ran_is_short_helper :
                        #x:pos ->
                        #x2:pos{x2 > x} ->
                        #b:Type ->
                        t:comBiTree b x ->
                        r:raNode b x2 ->
                        Lemma ( More t r
*)
(*
val ran_is_short : 
                  #x:pos ->
                  #b:Type ->
                  r:raNode b x ->
                  Lemma (ensures sizeRan r + 1 > pow 2 (lenRan r + (x - 1))) (decreases r)
let rec ran_is_short #x #b r = match r with
  | Last t -> ()
  | More t r2 -> let k = treeHeight (headTree r2) in
  begin
    ran_is_short r2;
    pow_distr_sums_on_e (lenRan r) (x - 1) 2;
    pow_distr_sums_on_e (lenRan r2) (k - 1) 2
  end
*)
(*
starting at 1
1 4 11 26
2 4 8  16

starting at 3
7 22 53
8
*)

(* ralist
   It's a Random Access list, it can be:
     Empty
     Without the first tree repeated
     With the first tree repeated
*)
type ralist 'a = 
    | Empty : ralist 'a
    | Once : #n:pos -> raNode 'a n -> ralist 'a
    | Twice : #n:pos -> comBiTree 'a n -> raNode 'a n -> ralist 'a
        
let empty = Empty

val raToList : #b:Type -> ralist b -> list b
let raToList #b ra = match ra with
    | Empty -> []
    | Once ran -> toList ran
    | Twice t r -> preorder t @ toList r

val insert : #b:Type -> b -> ralist b -> ralist b
let insert #b a ral = match ral with
    | Empty -> Once (Last (Leaf a))
    | Once ran -> let sRan = treeHeight (headTree ran) in
    	if (1 < sRan) 
    	then Once (More (Leaf a) ran)
        else Twice (Leaf a) ran
    | Twice t ran2 -> 
      begin
        match ran2 with 
    	  | Last t2 -> Once (Last (Branch a t t2))
          | More t2 ran3 -> let newTree = Branch a t t2 in
                 if (treeHeight (headTree ran3)) > (treeHeight newTree)
                 then Once (More newTree ran3)
                 else Twice newTree ran3
      end

val helper_lemma : #b:eqtype -> x:b -> l1:list b -> l2:list b -> Lemma ((x::l1) @ l2 = x::(l1@l2))
let rec helper_lemma #b x l1 l2 = ()

val other_helper_lemma : #b:eqtype -> l1:list b -> l2:list b -> l3:list b -> Lemma ((l1@l2)@l3 = l1@(l2@l3))
let rec other_helper_lemma #b l1 l2 l3 = match l1 with
  | [] -> ()
  | hd::tl -> (helper_lemma hd tl l2; helper_lemma hd (tl@l2) l3; other_helper_lemma tl l2 l3)

val helper_fun : #b:Type -> ralist b -> bool
let helper_fun #b r = match r with
  | Empty -> true 
  | _ -> false
  
val insert_lemma : 
                 #b:eqtype -> 
                 x:b -> 
                 rl:ralist b -> 
                 Lemma (raToList (insert x rl) = x :: (raToList rl))
let insert_lemma #b x rl = match rl with
  | Empty -> ()
  | Once ran -> begin 
    match treeHeight (headTree ran) with
      | 1 -> ()
      | _ -> ()
  end
  | Twice t ran2 -> begin
    match ran2 with 
      | Last t2 -> preorder_has_the_root_first x t t2
      | More t2 ran -> let newTree = Branch x t t2 in
        if (treeHeight (headTree ran)) > (treeHeight newTree)
        then (
          preorder_has_the_root_first x t t2;
          helper_lemma x (preorder t @ preorder t2) (toList ran);
          other_helper_lemma (preorder t) (preorder t2) (toList ran)
        )
        else (
          preorder_has_the_root_first x t t2; 
          helper_lemma x (preorder t @ preorder t2) (toList ran);
          other_helper_lemma (preorder t) (preorder t2) (toList ran)
        )
  end


val lenNode : #b:Type -> #n:nat{n > 0} -> rs:raNode b n -> Tot (x:nat{x >= pow2 n - 1}) (decreases rs)
let rec lenNode #b #n ran = match ran with
  | Last t -> pow2 (treeHeight t) - 1
  | More t ran2 -> pow2 (treeHeight t) - 1 + lenNode ran2

val len : #b:Type -> ralist b -> Tot (x:nat)
let len #b ral = match ral with
  | Empty -> 0
  | Once ran -> lenNode ran
  | Twice t ran -> pow2 (treeHeight t) - 1 + lenNode ran


val head : #b:Type -> l:ralist b{len l > 0} -> b
let head #b ral = match ral with
  | Once ran -> begin match ran with
      | Last t -> begin  match t with
           | Leaf a -> a
           | Branch a _ _ -> a
           end
      | More t _ -> begin match t with
           | Leaf a -> a
           | Branch a _ _ -> a
           end
      end
  | Twice t _ -> begin match t with
      | Leaf a -> a
      | Branch a _ _ -> a
      end

val head_lemma : #b:eqtype -> x:b -> rl:ralist b{len rl > 0} -> Lemma (head (insert x rl) = x)
let head_lemma #b x rl = insert_lemma x rl


val tail : #b:Type -> #n:pos -> l:ralist b{len l = n} -> m:ralist b{len m = n - 1}
let tail #b #n ral = match ral with
  | Once ran -> begin match ran with
         | Last t -> begin match t with
                | Leaf _ -> Empty
                | Branch _ t1 t2 -> Twice t1 (Last t2)
           end
         | More t nxtRan -> begin match t with
                | Leaf _ -> Once nxtRan
                | Branch _ t1 t2 -> Twice t1 (More t2 nxtRan)
           end
    end
  | Twice t nxtRan -> begin match t with
      | Leaf a -> Once nxtRan
      | Branch _ t1 t2 -> Twice t1 (More t2 nxtRan)
    end

//val tail_lemma : #b:Type -> x:b -> rl:ralist b -> Lemma (tail (insert x rl) = rl)
//let

// fuel < 3*log2(i)
val lookupTree : #b:Type -> #m:pos -> i:nat{i < pow2 m - 1}  -> #fuel:pos{fuel = m}(*Here I'd like to state that fuel == log2(i), it's stronger*) -> comBiTree b m -> b
let rec lookupTree #b #m i #fuel t = 
  match t with
    | Leaf a -> a
    | Branch value t1 t2 -> begin
      let subTreeSize = pow2 (treeHeight t1) - 1 in
      if subTreeSize = i then value
      else begin
           if i < subTreeSize then
             lookupTree i #(fuel - 1) t1
           else
             lookupTree  (i - subTreeSize - 1) #(fuel - 1) t2
      end
    end
    

val lookupNodes : #b:Type -> #m:pos -> rn:raNode b m -> i:pos{i < sizeRan rn} -> #fuelNodes:pos{fuelNodes = m} -> b
//let rec lookupNodes

(*val len : ralist 'a -> nat
let rec len l = match l with
  | Empty -> 0
  | Once n -> lenNode n
  | Twice t1 ran -> lenNode ran + pow2 (treeHeight t1)
//val pop : #b : Type -> l:ralist b -> (b, ralist b)
*)
let testList :ralist int  = insert 1 (insert 2 (insert 0 empty))

        


(* Other Operations
   ===== ==========

  drop
  toList (easy)  -> Foldable??
  fromList (easy)
  

*)
        
        
