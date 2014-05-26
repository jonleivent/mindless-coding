type comparison =
| Eq
| Lt
| Gt

type compareSpecT =
| CompEqT
| CompLtT
| CompGtT

type 'a sig0 =
  'a
  (* singleton inductive, whose constructor was exist *)

type sumbool =
| Left
| Right

type 'a eqDec = 'a -> 'a -> sumbool

type 'a ordered = { eq_dec : 'a eqDec; compare : ('a -> 'a -> comparison); compare_spec : ('a -> 'a -> compareSpecT) }

(** val compare_spec : 'a1 ordered -> 'a1 -> 'a1 -> compareSpecT **)

let compare_spec x = x.compare_spec

type a (* AXIOM TO BE REALIZED *)

(** val ordA : a ordered **)

let ordA =
  failwith "AXIOM TO BE REALIZED"

type color =
| Red
| Black

type rbtree =
| Leaf
| Node of color * rbtree * a * rbtree

type findResult =
| Found
| NotFound

(** val find : a -> rbtree -> findResult **)

let rec find x = function
| Leaf -> NotFound
| Node (co, tl, d, tr) ->
  (match ordA.compare_spec x d with
   | CompEqT -> Found
   | CompLtT -> find x tl
   | CompGtT -> find x tr)

(** val cof : rbtree -> color **)

let cof = function
| Leaf -> Black
| Node (co, t1, d, t2) -> co

(** val midRedCombine : rbtree -> a -> rbtree -> a -> rbtree -> rbtree **)

let midRedCombine tl x tm y tr =
  match tm with
  | Leaf -> assert false (* absurd case *)
  | Node (co, tl0, d, tr0) -> Node (Red, (Node (Black, tl, x, tl0)), d, (Node (Black, tr0, y, tr)))

(** val red2black : rbtree -> rbtree **)

let red2black = function
| Leaf -> assert false (* absurd case *)
| Node (co, tl, d, tr) -> Node (Black, tl, d, tr)

type iChanged =
| ISameIndx
| IReddened
| IBlackInc

(** val rebalRight : rbtree -> a -> rbtree -> ( * ) **)

let rebalRight tl d tr =
  match tl with
  | Leaf -> assert false (* absurd case *)
  | Node (co, tl0, d0, tr0) ->
    (match cof tr0 with
     | Red -> IReddened,(midRedCombine tl0 d0 tr0 d tr)
     | Black ->
       (match cof tl0 with
        | Red -> IReddened,(Node (Red, (red2black tl0), d0, (Node (Black, tr0, d, tr))))
        | Black -> ISameIndx,(Node (Black, (Node (Red, tl0, d0, tr0)), d, tr))))

(** val rebalLeft : rbtree -> a -> rbtree -> ( * ) **)

let rebalLeft tl d = function
| Leaf -> assert false (* absurd case *)
| Node (co, tl0, d0, tr0) ->
  (match cof tl0 with
   | Red -> IReddened,(midRedCombine tl d tl0 d0 tr0)
   | Black ->
     (match cof tr0 with
      | Red -> IReddened,(Node (Red, (Node (Black, tl, d, tl0)), d0, (red2black tr0)))
      | Black -> ISameIndx,(Node (Black, tl, d, (Node (Red, tl0, d0, tr0))))))

(** val color2change : color -> iChanged **)

let color2change = function
| Red -> IBlackInc
| Black -> ISameIndx

type insertResult =
| FoundByInsert
| Inserted of iChanged * rbtree

(** val insert : a -> rbtree -> insertResult **)

let rec insert x = function
| Leaf -> Inserted (IReddened, (Node (Red, Leaf, x, Leaf)))
| Node (co, tl, d, tr) ->
  (match ordA.compare_spec x d with
   | CompEqT -> FoundByInsert
   | CompLtT ->
     (match insert x tl with
      | FoundByInsert -> FoundByInsert
      | Inserted (i, to0) ->
        (match i with
         | ISameIndx -> Inserted (ISameIndx, (Node (co, to0, d, tr)))
         | IReddened -> Inserted ((color2change co), (Node (Black, to0, d, tr)))
         | IBlackInc -> let i0,to1 = rebalRight to0 d tr in Inserted (i0, to1)))
   | CompGtT ->
     (match insert x tr with
      | FoundByInsert -> FoundByInsert
      | Inserted (i, to0) ->
        (match i with
         | ISameIndx -> Inserted (ISameIndx, (Node (co, tl, d, to0)))
         | IReddened -> Inserted ((color2change co), (Node (Black, tl, d, to0)))
         | IBlackInc -> let i0,to1 = rebalLeft tl d to0 in Inserted (i0, to1))))

type dChanged =
| StillFits
| Rebalance

(** val dRotateLeft : rbtree -> a -> rbtree -> rbtree **)

let dRotateLeft tl d = function
| Leaf -> assert false (* absurd case *)
| Node (co, tl0, d0, tr0) ->
  (match tl0 with
   | Leaf -> assert false (* absurd case *)
   | Node (co0, tl1, d1, tr1) ->
     (match cof tl1 with
      | Red -> Node (Black, (midRedCombine tl d tl1 d1 tr1), d0, tr0)
      | Black -> Node (Black, (Node (Black, (Node (Red, tl, d, tl1)), d1, tr1)), d0, tr0)))

(** val dRotateRight : rbtree -> a -> rbtree -> rbtree **)

let dRotateRight tl d tr =
  match tl with
  | Leaf -> assert false (* absurd case *)
  | Node (co, tl0, d0, tr0) ->
    (match tr0 with
     | Leaf -> assert false (* absurd case *)
     | Node (co0, tl1, d1, tr1) ->
       (match cof tr1 with
        | Red -> Node (Black, tl0, d0, (midRedCombine tl1 d1 tr1 d tr))
        | Black -> Node (Black, tl0, d0, (Node (Black, tl1, d1, (Node (Red, tr1, d, tr)))))))

(** val color2dchange : color -> dChanged **)

let color2dchange = function
| Red -> StillFits
| Black -> Rebalance

(** val colorAs : color -> rbtree -> rbtree **)

let colorAs c t =
  match c with
  | Red -> t
  | Black -> red2black t

(** val dRebalRight : color -> rbtree -> a -> rbtree -> ( * ) **)

let dRebalRight co tl d tr =
  match tl with
  | Leaf -> assert false (* absurd case *)
  | Node (co0, tl0, d0, tr0) ->
    (match co0 with
     | Red -> StillFits,(dRotateRight (Node (Red, tl0, d0, tr0)) d tr)
     | Black ->
       (match cof tr0 with
        | Red -> StillFits,(colorAs co (midRedCombine tl0 d0 tr0 d tr))
        | Black -> (color2dchange co),(Node (Black, tl0, d0, (Node (Red, tr0, d, tr))))))

(** val dRebalLeft : color -> rbtree -> a -> rbtree -> ( * ) **)

let dRebalLeft co tl d = function
| Leaf -> assert false (* absurd case *)
| Node (co0, tl0, d0, tr0) ->
  (match co0 with
   | Red -> StillFits,(dRotateLeft tl d (Node (Red, tl0, d0, tr0)))
   | Black ->
     (match cof tl0 with
      | Red -> StillFits,(colorAs co (midRedCombine tl d tl0 d0 tr0))
      | Black -> (color2dchange co),(Node (Black, (Node (Red, tl, d, tl0)), d0, tr0))))

(** val dFitLeft : color -> ( * ) -> a -> rbtree -> ( * ) **)

let dFitLeft co dr d tr =
  let dc,t = dr in
  (match dc with
   | StillFits -> StillFits,(Node (co, t, d, tr))
   | Rebalance -> dRebalLeft co t d tr)

(** val dFitRight : color -> rbtree -> a -> ( * ) -> ( * ) **)

let dFitRight co tl d = function
| dc,t ->
  (match dc with
   | StillFits -> StillFits,(Node (co, tl, d, t))
   | Rebalance -> dRebalRight co tl d t)

(** val colorFit : color -> rbtree -> ( * ) **)

let colorFit co t =
  match cof t with
  | Red -> StillFits,(red2black t)
  | Black -> (color2dchange co),t

type delminResult =
| NoMin
| MinDeleted of a * ( * )

(** val delmin : rbtree -> delminResult **)

let rec delmin = function
| Leaf -> NoMin
| Node (co, tl, d, tr) ->
  (match delmin tl with
   | NoMin -> MinDeleted (d, (colorFit co tr))
   | MinDeleted (m, dr) -> MinDeleted (m, (dFitLeft co dr d tr)))

type deleteResult =
| DelNotFound
| Deleted of ( * )

(** val delete : a -> rbtree -> deleteResult **)

let rec delete x = function
| Leaf -> DelNotFound
| Node (co, tl, d, tr) ->
  (match ordA.compare_spec x d with
   | CompEqT ->
     let h = delmin tr in
     (match h with
      | NoMin -> Deleted (colorFit co tl)
      | MinDeleted (m, dr) -> Deleted (dFitRight co tl m dr))
   | CompLtT ->
     (match delete x tl with
      | DelNotFound -> DelNotFound
      | Deleted r -> Deleted (dFitLeft co r d tr))
   | CompGtT ->
     (match delete x tr with
      | DelNotFound -> DelNotFound
      | Deleted r -> Deleted (dFitRight co tl d r)))

