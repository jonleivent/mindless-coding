type __ = Obj.t
let __ = let rec f _ = Obj.repr f in Obj.repr f

type nat =
| O
| S of nat

type comparison =
| Eq
| Lt
| Gt

type compareSpecT =
| CompEqT
| CompLtT
| CompGtT

(** val id : 'a1 -> 'a1 **)

let id x =
  x

type 'a sig0 =
  'a
  (* singleton inductive, whose constructor was exist *)

type 'a eqDec = 'a -> 'a -> bool

type 'a ordered = { eq_dec : 'a eqDec; compare : ('a -> 'a -> comparison);
                    compare_spec : ('a -> 'a -> compareSpecT) }

(** val compare_spec : 'a1 ordered -> 'a1 -> 'a1 -> compareSpecT **)

let compare_spec x = x.compare_spec

type ('a, 'tree) breakResult =
| BreakLeaf
| BreakNode of 'tree * 'a * 'tree

type ('a, 'tree) insertResult =
| InsertFound
| Inserted of 'tree

type ('a, 'tree) delminResult =
| DelminLeaf
| DelminNode of 'a * 'tree

type ('a, 'tree) delmaxResult =
| DelmaxLeaf
| DelmaxNode of 'a * 'tree

type ('a, 'tree) deleteResult =
| DelNotFound
| Deleted of 'tree

type 'a tree = { leaf : __; break : (__ -> __ -> ('a, __) breakResult);
                 insert : ('a -> __ -> __ -> ('a, __) insertResult);
                 join : (__ -> __ -> 'a -> __ -> __ -> __ -> __);
                 delmin : (__ -> __ -> ('a, __) delminResult);
                 delmax : (__ -> __ -> ('a, __) delmaxResult);
                 delete : ('a -> __ -> __ -> ('a, __) deleteResult) }

type 'a tree0 = __

(** val leaf : 'a1 ordered -> 'a1 tree -> 'a1 tree0 **)

let leaf _ x = x.leaf

(** val break :
    'a1 ordered -> 'a1 tree -> 'a1 tree0 -> ('a1, 'a1 tree0) breakResult **)

let break ordA0 tree1 t =
  tree1.break __ t

(** val join :
    'a1 ordered -> 'a1 tree -> 'a1 tree0 -> 'a1 -> 'a1 tree0 -> 'a1 tree0 **)

let join ordA0 tree1 tl d tr =
  tree1.join __ tl d __ tr __

(** val delmin :
    'a1 ordered -> 'a1 tree -> 'a1 tree0 -> ('a1, 'a1 tree0) delminResult **)

let delmin ordA0 tree1 t =
  tree1.delmin __ t

(** val enat_xrect : (__ -> (__ -> __ -> 'a1) -> 'a1) -> 'a1 **)

let enat_xrect x =
  let rec f x0 =
    x x0 (fun y _ -> f y)
  in f __

type a (* AXIOM TO BE REALIZED *)

(** val ordA : a ordered **)

let ordA =
  failwith "AXIOM TO BE REALIZED"

(** val treeA : a tree **)

let treeA =
  failwith "AXIOM TO BE REALIZED"

type findResult =
| Found
| NotFound

(** val find : a -> a tree0 -> findResult **)

let find x t =
  enat_xrect (fun _ recurse _ t0 _ ->
    match break ordA treeA t0 with
    | BreakLeaf -> NotFound
    | BreakNode (tl, d, tr) ->
      (match ordA.compare_spec x d with
       | CompEqT -> Found
       | CompLtT -> recurse __ __ __ tl __
       | CompGtT -> recurse __ __ __ tr __)) __ t __

type splitResult =
| Split of bool * a tree0 * a tree0

(** val split : a -> a tree0 -> splitResult **)

let split x t =
  enat_xrect (fun _ recurse _ t0 _ ->
    match break ordA treeA t0 with
    | BreakLeaf -> Split (false, t0, t0)
    | BreakNode (tl, d, tr) ->
      (match ordA.compare_spec x d with
       | CompEqT -> Split (true, tl, tr)
       | CompLtT ->
         let h = recurse __ __ __ tl __ in
         let Split (found, x0, x1) = h in
         Split (found, x0, (join ordA treeA x1 d tr))
       | CompGtT ->
         let h = recurse __ __ __ tr __ in
         let Split (found, x0, x1) = h in
         Split (found, (join ordA treeA tl d x0), x1))) __ t __

type unionResult =
  a tree0
  (* singleton inductive, whose constructor was UnionResult *)

(** val union : a tree0 -> a tree0 -> unionResult **)

let union t1 t2 =
  enat_xrect (fun _ recurse _ _ _ t3 t4 ->
    match break ordA treeA t3 with
    | BreakLeaf -> t4
    | BreakNode (tl, d, tr) ->
      let Split (found, x, x0) = split d t4 in
      let h = recurse __ __ __ __ __ tl x in
      let h0 = recurse __ __ __ __ __ tr x0 in join ordA treeA h d h0) __ __ __
    t1 t2

(** val delete_free_delmin : a tree0 -> (a, a tree0) delminResult **)

let delete_free_delmin t =
  enat_xrect (fun _ recurse _ _ t0 ->
    match break ordA treeA t0 with
    | BreakLeaf -> DelminLeaf
    | BreakNode (tl, d, tr) ->
      let dr = recurse __ __ __ __ tl in
      (match dr with
       | DelminLeaf -> DelminNode (d, tr)
       | DelminNode (m, t1) -> DelminNode (m, (join ordA treeA t1 d tr)))) __
    __ t

(** val merge : a tree0 -> a tree0 -> a tree0 **)

let merge t1 t2 =
  match delmin ordA treeA t2 with
  | DelminLeaf -> t1
  | DelminNode (m, tr) -> join ordA treeA t1 m tr

type intersectResult =
  a tree0
  (* singleton inductive, whose constructor was IntersectResult *)

(** val intersection : a tree0 -> a tree0 -> intersectResult **)

let intersection t1 t2 =
  enat_xrect (fun _ recurse _ _ _ t3 t4 ->
    match break ordA treeA t3 with
    | BreakLeaf -> treeA.leaf
    | BreakNode (tl, d, tr) ->
      let Split (found, x, x0) = split d t4 in
      let h = recurse __ __ __ __ __ tl x in
      let h0 = recurse __ __ __ __ __ tr x0 in
      if found then join ordA treeA h d h0 else merge h h0) __ __ __ t1 t2

type setdiffResult =
  a tree0
  (* singleton inductive, whose constructor was SetDiffResult *)

(** val setdifference : a tree0 -> a tree0 -> setdiffResult **)

let setdifference t1 t2 =
  enat_xrect (fun _ recurse _ _ _ t3 t4 ->
    match break ordA treeA t3 with
    | BreakLeaf -> treeA.leaf
    | BreakNode (tl, d, tr) ->
      let Split (found, x, x0) = split d t4 in
      let h = recurse __ __ __ __ __ tl x in
      let h0 = recurse __ __ __ __ __ tr x0 in
      if found then merge h h0 else join ordA treeA h d h0) __ __ __ t1 t2

type filterResult =
  a tree0
  (* singleton inductive, whose constructor was Filtered *)

(** val filter : (a -> bool) -> a tree0 -> filterResult **)

let filter filt t =
  enat_xrect (fun _ recurse _ t0 _ ->
    match break ordA treeA t0 with
    | BreakLeaf -> treeA.leaf
    | BreakNode (tl, d, tr) ->
      let h = recurse __ __ __ tl __ in
      let h0 = recurse __ __ __ tr __ in
      if filt d then join ordA treeA h d h0 else merge h h0) __ t __

type partitionResult =
| Partitioned of a tree0 * a tree0

(** val partition : (a -> bool) -> a tree0 -> partitionResult **)

let partition filt t =
  enat_xrect (fun _ recurse _ t0 _ ->
    match break ordA treeA t0 with
    | BreakLeaf -> Partitioned (treeA.leaf, treeA.leaf)
    | BreakNode (tl, d, tr) ->
      let h = recurse __ __ __ tl __ in
      let Partitioned (tl1, tl0) = h in
      let h0 = recurse __ __ __ tr __ in
      let Partitioned (tr1, tr0) = h0 in
      if filt d
      then Partitioned ((join ordA treeA tl1 d tr1), (merge tl0 tr0))
      else Partitioned ((merge tl1 tr1), (join ordA treeA tl0 d tr0))) __ t __

type subsetResult =
| IsSubset of bool
| NotSubset of a

(** val subset : a tree0 -> a tree0 -> subsetResult **)

let subset t1 t2 =
  enat_xrect (fun _ recurse _ _ _ t3 t4 ->
    match break ordA treeA t3 with
    | BreakLeaf ->
      IsSubset
        (match break ordA treeA t4 with
         | BreakLeaf -> false
         | BreakNode (tl, d, tr) -> true)
    | BreakNode (tl, d, tr) ->
      let Split (found, x, x0) = split d t4 in
      if found
      then let rl = recurse __ __ __ __ __ tl x in
           (match rl with
            | IsSubset isProperl ->
              let rr = recurse __ __ __ __ __ tr x0 in
              (match rr with
               | IsSubset isProperr ->
                 IsSubset (if isProperl then true else isProperr)
               | NotSubset a0 -> NotSubset a0)
            | NotSubset a0 -> NotSubset a0)
      else NotSubset d) __ __ __ t1 t2

(** val equiv : a tree0 -> a tree0 -> bool **)

let equiv t1 t2 =
  match subset t1 t2 with
  | IsSubset isProper -> if isProper then false else true
  | NotSubset a0 -> false

type 't ecomprehension = 't

type 'b foldLeftResult = 'b ecomprehension

(** val fold_left :
    ('a1 -> a -> 'a1) -> a tree0 -> 'a1 -> 'a1 foldLeftResult **)

let fold_left foldf t b =
  enat_xrect (fun _ recurse _ t0 b0 _ ->
    match break ordA treeA t0 with
    | BreakLeaf -> b0
    | BreakNode (tl, d, tr) ->
      let h = recurse __ __ __ tl b0 __ in recurse __ __ __ tr (foldf h d) __)
    __ t b __

type 'b foldRightResult = 'b ecomprehension

(** val fold_right :
    (a -> 'a1 -> 'a1) -> 'a1 -> a tree0 -> 'a1 foldRightResult **)

let fold_right foldf b t =
  enat_xrect (fun _ recurse _ t0 b0 _ ->
    match break ordA treeA t0 with
    | BreakLeaf -> b0
    | BreakNode (tl, d, tr) ->
      let h = recurse __ __ __ tr b0 __ in recurse __ __ __ tl (foldf d h) __)
    __ t b __

(** val cardinality : a tree0 -> nat ecomprehension **)

let cardinality t =
  fold_right (fun x n -> S n) O t

(** val map : (a -> 'a1) -> a tree0 -> 'a1 list ecomprehension **)

let map mapf t =
  fold_right (fun a0 bs -> (mapf a0) :: bs) [] t

(** val flatten : a tree0 -> a list ecomprehension **)

let flatten t =
  map id t

