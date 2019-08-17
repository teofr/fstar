module Test


open FStar.List.Tot.Base
open FStar.Mul
open FStar.Tactics

(* Some util functions I couldnt find
*)

(* Power *)

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

(* List lemmas *)

val lemma_append_length: l1:list 'a -> l2:list 'a
                -> Lemma (requires True)
                        (ensures (length ( l1 @ l2) = length l1 + length l2))
let rec lemma_append_length l1 l2 = match l1 with
    | [] -> ()
    | hd::tl -> lemma_append_length tl l2

// Definition of @
//val helper_lemma : #b:eqtype -> x:b -> l1:list b -> l2:list b -> Lemma ((x::l1) @ l2 = x::(l1@l2))
//let rec helper_lemma #b x l1 l2 = ()

val lemma_append_assoc : #b:eqtype -> l1:list b -> l2:list b -> l3:list b -> Lemma ((l1@l2)@l3 = l1@(l2@l3))
let rec lemma_append_assoc #b l1 l2 l3 = match l1 with
  | [] -> ()
  | hd::tl -> lemma_append_assoc tl l2 l3
// Simple enough, shouldnt need it
(*val random_lemma : 
                 #b:Type -> 
                 x:b -> 
                 l1:list b -> 
                 l2:list b -> 
                 Lemma (length (x :: l1 @ l2) = 1 + length l1 + length l2)
let rec random_lemma #b x l1 l2 = lemma_append_length l1 l2
*)

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
    | Branch _ t1 t2 -> (
      assert(treeHeight t1 = treeHeight t2);
      1 + treeHeight t2
    )

val treeSize : (#x:pos) -> comBiTree 'a x ->  y:pos{y = (pow2 x) - 1}
let rec treeSize (t:comBiTree 'a 'n) = match t with
  | Leaf _ -> 1
  | Branch _ t1 t2 -> 1 + treeSize t1 + treeSize t2

val tree_size_gives_height : #b:Type -> #h1:pos -> #h2:pos -> t1:comBiTree b h1 -> t2:comBiTree b h2 -> Lemma (requires treeSize t1 = treeSize t2) (ensures h1 = h2)
let rec tree_size_gives_height #b #h1 #h2 t1 t2 = match t1 with
  | Leaf _ -> begin match t2 with
    | Leaf _ -> ()
    | Branch _ t21 t22 -> ()
  end
  | Branch _ t11 t12 -> begin match t2 with
    | Leaf _ -> ()
    | Branch _ t21 t22 -> tree_size_gives_height t11 t21
  end

val treeRoot : #x:pos -> #b:Type -> comBiTree b x -> b
let treeRoot #x #b t = match t with
  | Leaf a -> a
  | Branch a _ _ -> a

val preorder : (#x:pos) -> (#b:Type) -> t:comBiTree b x -> l:list b{length l = treeSize t}
let rec preorder #x #b t = match t with
  | Leaf a -> [a]
  | Branch a t1 t2 -> begin
    lemma_append_length (preorder t1) (preorder t2);
    a :: (preorder t1) @ preorder t2
  end

//val lemma_preorder_has_the_root_first : 
//                                #n:pos -> 
//                                #b:eqtype ->
//                                x:b ->
//                                t1:comBiTree b n -> 
//                                t2:comBiTree b n -> 
//                                Lemma 
//                                  (preorder (Branch x t1 t2) = 
//                                    x :: ((preorder t1) @ (preorder t2)))
//let lemma_preorder_has_the_root_first #n #b x t1 t2 = () 

(* raNode
   It's a non empty linked list of strictly increasing comBiTrees
   With the height of the head tree at type level.
*)
type raNode 'a : (n:pos) -> Type =
    | Last : #m:pos -> comBiTree 'a m -> raNode 'a m
    | More : #m:pos -> #k:pos{k>m} -> comBiTree 'a m -> 
        raNode 'a k -> raNode 'a m

val ranLen : #x:pos -> #b:Type -> r:raNode b x -> Tot (y:pos) (decreases r)
let rec ranLen #x #b r  = match r with
    | Last _ -> 1
    | More _ m -> 1 + ranLen m

val toList : #x:pos -> #b:Type -> r:raNode b x -> Tot (list b) (decreases r)
let rec toList #x #b r = match r with
    | Last t -> preorder t
    | More t m -> preorder t @ (toList m)

val sizeRan : #x:pos -> #b:Type -> r:raNode b x -> Tot (y:pos{y = length (toList r)}) (decreases r)
let rec sizeRan #x #b r = match r with
    | Last t -> treeSize t
    | More t m -> begin
      lemma_append_length (preorder t) (toList m);
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

val sizeRAList : #b:Type -> ralist b -> nat
let sizeRAList #b rl = match rl with
  | Empty -> 0
  | Once rn -> sizeRan rn
  | Twice t rn -> treeSize t + sizeRan rn

val size_lemma : #b:Type -> rl:ralist b -> Lemma (sizeRAList rl = length (raToList rl))
let size_lemma #b rl = match rl with
  | Empty -> ()
  | Once _ -> ()
  | Twice t rn -> lemma_append_length (preorder t) (toList rn)

val insert : #b:Type -> b -> rl:ralist b -> rl2:ralist b
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


val helper_fun : #b:Type -> ralist b -> bool
let helper_fun #b r = match r with
  | Twice (Leaf _)  _ -> true 
  | _ -> false

// This states that insert behaves like :: on the list
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
      | Last t2 -> ()
      | More t2 ran -> lemma_append_assoc (preorder t) (preorder t2) (toList ran) 
  end

// insert modifies the size as expected
val insert_lemma_size : #b:Type -> x:b -> rl:ralist b -> Lemma (sizeRAList (insert x rl) = sizeRAList rl + 1)
let insert_lemma_size #b x rl = begin 
  size_lemma (insert x rl)
end

val head : #b:Type -> l:ralist b{sizeRAList l > 0} -> b
let head #b ral = match ral with
  | Once ran -> treeRoot (headTree ran)
  | Twice t _ -> treeRoot t

// head after an insert returns the inserted element
val head_lemma : #b:eqtype -> x:b -> rl:ralist b -> Lemma (head (insert x rl) = x)
let head_lemma #b x rl = ()

// head behaves as hd on the list version
val head_lemma_2 : #b:eqtype -> rl:ralist b{sizeRAList rl > 0} -> Lemma (head rl = hd (raToList rl))
let head_lemma_2 #b rl = ()
  
val ratail : #b:Type -> #n:pos -> l:ralist b{sizeRAList l = n} -> m:ralist b{sizeRAList m = n - 1}
let ratail #b #n ral = match ral with
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

// tailing after inserting gives back the same list
val ratail_lemma : #b:eqtype -> #n:nat -> x:b -> rl:ralist b{sizeRAList rl = n} -> Lemma (ensures ratail #b #(n+1) (insert x rl) = rl)
let rec ratail_lemma #b #n x rl = match rl with
  | Empty -> ()
  | Once ran -> begin 
    match treeHeight (headTree ran) with
      | 1 -> ()
      | _ -> ()
  end
  | Twice t ran2 -> begin
    match ran2 with 
      | Last t2 -> ()
      | More t2 ran -> 
          lemma_append_assoc (preorder t) (preorder t2) (toList ran)
  end

// tail behaves as tail on the corresponding list
val ratail_lemma_list : #b:eqtype -> #n:pos -> rl:ralist b{sizeRAList rl = n} -> Lemma (raToList (ratail #b #n rl) = tail (raToList rl))
let ratail_lemma_list  #b #n rl = match rl with
   | Once ran -> begin match ran with
         | Last t -> begin match t with
                | Leaf _ -> () //Empty
                | Branch _ t1 t2 -> () //Twice t1 (Last t2)
           end
         | More t nxtRan -> begin match t with
                | Leaf _ -> () //Once nxtRan
                | Branch _ t1 t2 -> lemma_append_assoc (preorder t1) (preorder t2) (toList nxtRan) //Twice t1 (More t2 nxtRan)
           end
    end
  | Twice t nxtRan -> begin match t with
      | Leaf a -> () //Once nxtRan
      | Branch _ t1 t2 -> lemma_append_assoc (preorder t1) (preorder t2) (toList nxtRan) //Twice t1 (More t2 nxtRan)
    end

// This says that deconstructing a list with tail and head, and then reconstructing it using the insert
// gives the same list.
// I think this gives a very strong result, saying that every ralist is equal to a list constructed with inserts, this
// if stated correctly, could allow us to do a case on RAlists similar to list, ie, you can see a RAlist as a head and a tail, or 
// an empty list
val insert_inverse_head_tail : #b:eqtype -> #n:pos -> rl:ralist b{sizeRAList rl = n} -> Lemma (insert (head rl) (ratail #b #n rl) = rl)
let insert_inverse_head_tail #b #n rl = match rl with
  | Once ran -> begin match ran with
         | Last t -> begin match t with
                | Leaf _ -> () //Empty
                | Branch _ t1 t2 -> () //Twice t1 (Last t2)
           end
         | More t nxtRan -> begin match t with
                | Leaf _ -> () //Once nxtRan
                | Branch _ t1 t2 -> lemma_append_assoc (preorder t1) (preorder t2) (toList nxtRan) //Twice t1 (More t2 nxtRan)
           end
    end
  | Twice t nxtRan -> begin match t with
      | Leaf a -> () //Once nxtRan
      | Branch _ t1 t2 -> lemma_append_assoc (preorder t1) (preorder t2) (toList nxtRan) //Twice t1 (More t2 nxtRan)
    end| Once ran -> ()
  | Twice t ran -> ()



val fromList : #b:eqtype -> l:list b -> rl:ralist b{raToList rl = l}
let rec fromList #b l = match l with
  | [] -> Empty
  | hd::tl -> begin
    insert_lemma hd (fromList tl);
    insert hd (fromList tl)
  end

val fromList_toList_inverses : #b:eqtype -> rl:ralist b -> Lemma (rl = fromList (raToList rl))
// fromList l = insert (hd l) (fromlist (tail l))
// fromlist (toList rl) = insert (hd (toList rl)) (fromList (tail (toList rl)))
// fromlist (toList rl) = insert (head rl) (fromlist (tolist (ratail rl)))
let fromList_toList_inverses #b rl = match rl with
  | Empty -> ()
  | a -> begin match (head a, ratail a) with 
    | (x, xs) -> 

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
        
        

//// Some results on the structure

val tree_spine_eq : #b:Type -> #h1:pos -> #h2:pos -> t1:comBiTree b h1 -> t2:comBiTree b h2 -> r:bool{r = (h1 = h2)}
let rec tree_spine_eq #b #h1 #h2 t1 t2 = match t1 with
  | Leaf _ -> begin match t2 with
    | Leaf _ -> true
    | _ -> false
  end
  | Branch _ t11 t12 -> begin match t2 with
    | Branch _ t21 t22 -> (tree_spine_eq t11 t21) &&  (tree_spine_eq t12 t22)
    | _ -> false
  end
  | _ -> false

val tree_spine_doesnt_depend_on_elements : #b:Type -> #h1:pos -> #h2:pos -> t1:comBiTree b h1 -> t2:comBiTree b h2 -> Lemma (requires treeSize t1 = treeSize t2) (ensures tree_spine_eq t1 t2)
let tree_spine_doesnt_depend_on_elements #b #h1 #h2 t1 t2 = tree_size_gives_height t1 t2

val node_spine_eq : #b:Type -> #s1:pos -> #s2:pos -> ran1:raNode b s1 -> ran2:raNode b s2 -> Tot (r:bool{r ==> (sizeRan ran1 = sizeRan ran2)}) (decreases ran1)
let rec node_spine_eq #b #s1 #s2 ran1 ran2 = match ran1 with
  | Last t1 -> begin match ran2 with
    | Last t2 -> tree_spine_eq t1 t2
    | _ -> false
  end
  | More t1 rran1 -> begin match ran2 with
    | More t2 rran2 -> (tree_spine_eq t1 t2) && (node_spine_eq rran1 rran2)
    | _ -> false
  end

//val node_spine_only_depends_on_size : #b:Type -> #s1:pos -> #s2:pos -> ran1:raNode b s1 -> ran2:raNode b s2 -> Lemma ((sizeRan ran1 = sizeRan ran2) ==> node_spine_eq ran1 ran2)


val raspine_eq : #b:Type -> rl1:ralist b -> rl2:ralist b -> bool
let rec raspine_eq #b rl1 rl2 = match (rl1, rl2) with
  | (Empty, Empty) -> true
  | (Once ran1, Once ran2) -> node_spine_eq ran1 ran2
  | (Twice t1 ran1, Twice t2 ran2) -> tree_spine_eq t1 t2 && node_spine_eq ran1 ran2
  | _ -> false 


// This would be a very important proof, it would allow us to think about the structure
// of the ralist only by its size, which would make most proofs easier
// TODO do this, as of now I dont have a good intuiton on how to proceed, but its very related
// to the theory of skew binary numbers
//val spine_doesnt_depend_on_elements : #b:Type -> #n:pos -> rl1:ralist b{sizeRAList rl1 = n} -> rl2:ralist b{sizeRAList rl2 = n} -> Lemma (raspine_eq rl1 rl2)
