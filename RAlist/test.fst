module Test

open FStar.List.Tot.Base

(*  comBiTree
    comBitree is a COMplete BInary TREE with the height of the tree at type level
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

val preorder_keeps_the_elements : #n:pos -> t:comBiTree 'a n -> Lemma (length (preorder t) = treeSize t)


(* raNode
   It's a non empty linked list of strictly increasing comBiTrees
*)
type raNode 'a : (n:pos) -> Type =
    | Last : #m:pos -> comBiTree 'a m -> raNode 'a m
    | More : #m:pos -> #k:pos{k>m} -> comBiTree 'a m -> 
        raNode 'a k -> raNode 'a m



val sizeRan : #x:pos -> raNode 'a x -> y:pos{y = x}
let sizeRan (r:raNode 'a 'n) = match r with
    | Last t -> treeHeight t
    | More t _ -> treeHeight t


val headTree : #n:pos -> #b:Type -> raNode b n -> comBiTree b n 
let headTree #n #b ran = match ran with
  | Last t -> t
  | More t _ -> t


(* ralist
   It's a Random Access list, it can be:
     Empty
     Without the first tree repeated
     With the first tree repeated
*)
type ralist 'a = 
    | Empty : ralist 'a
    | Once : #n:pos -> raNode 'a n -> ralist 'a
    | Twice : #n:pos -> comBiTree 'a n -> 
        raNode 'a n -> ralist 'a
        
let empty = Empty


//val insertTreeInNode : #a:Type -> #x:nat{x>0} -> #y:nat{y>0} -> comBiTree a x -> raNode a y -> #z:nat -> ralist a z

val insert : #b:Type -> b -> ralist b -> ralist b
let insert #b a ral = match ral with
    | Empty -> Once (Last (Leaf a))
    | Once ran -> let sRan = sizeRan ran in
    	if (1 < sRan) 
    	then Once (More (Leaf a) ran)
        else Twice (Leaf a) ran
    | Twice t ran2 -> 
      begin
        match ran2 with 
    	  | Last t2 -> Once (Last (Branch a t t2))
          | More t2 ran3 -> let newTree = Branch a t t2 in
                 if (sizeRan ran3) > (treeHeight newTree)
                 then Once (More newTree ran3)
                 else Twice newTree ran3
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
        
        
