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

type fnd =
| Found
| NotFound

(** val find : a -> rbtree -> fnd **)

let rec find x = function
| Leaf -> NotFound
| Node (co, tl, d, tr) ->
  (match ordA.compare_spec x d with
   | CompEqT -> Found
   | CompLtT -> find x tl
   | CompGtT -> find x tr)

(** val bal0 : rbtree -> a -> rbtree -> a -> rbtree -> rbtree **)

let bal0 tl x tm y tr =
  match tm with
  | Leaf -> assert false (* absurd case *)
  | Node (co, tl0, d, tr0) -> Node (Red, (Node (Black, tl, x, tl0)), d, (Node (Black, tr0, y, tr)))

(** val r2b : rbtree -> rbtree **)

let r2b = function
| Leaf -> assert false (* absurd case *)
| Node (co, tl, d, tr) -> Node (Black, tl, d, tr)

(** val cof : rbtree -> color **)

let cof = function
| Leaf -> Black
| Node (co, tl, d, tr) -> co

type iChangedTo =
| ISameIndx
| IReddened
| IBlackInc

(** val bal1 : rbtree -> a -> rbtree -> ( * ) **)

let bal1 tl d tr =
  match tl with
  | Leaf -> assert false (* absurd case *)
  | Node (co, tl0, d0, tr0) ->
    (match cof tr0 with
     | Red -> IReddened,(bal0 tl0 d0 tr0 d tr)
     | Black ->
       (match cof tl0 with
        | Red -> IReddened,(Node (Red, (r2b tl0), d0, (Node (Black, tr0, d, tr))))
        | Black -> ISameIndx,(Node (Black, (Node (Red, tl0, d0, tr0)), d, tr))))

(** val bal2 : rbtree -> a -> rbtree -> ( * ) **)

let bal2 tl d = function
| Leaf -> assert false (* absurd case *)
| Node (co, tl0, d0, tr0) ->
  (match cof tl0 with
   | Red -> IReddened,(bal0 tl d tl0 d0 tr0)
   | Black ->
     (match cof tr0 with
      | Red -> IReddened,(Node (Red, (Node (Black, tl, d, tl0)), d0, (r2b tr0)))
      | Black -> ISameIndx,(Node (Black, tl, d, (Node (Red, tl0, d0, tr0))))))

(** val c2i : color -> iChangedTo **)

let c2i = function
| Red -> IBlackInc
| Black -> ISameIndx

type ins =
| IFound
| IInsed of iChangedTo * rbtree

(** val insert : a -> rbtree -> ins **)

let rec insert x = function
| Leaf -> IInsed (IReddened, (Node (Red, Leaf, x, Leaf)))
| Node (co, tl, d, tr) ->
  (match ordA.compare_spec x d with
   | CompEqT -> IFound
   | CompLtT ->
     (match insert x tl with
      | IFound -> IFound
      | IInsed (i, to0) ->
        (match i with
         | ISameIndx -> IInsed (ISameIndx, (Node (co, to0, d, tr)))
         | IReddened -> IInsed ((c2i co), (Node (Black, to0, d, tr)))
         | IBlackInc -> let i0,to1 = bal1 to0 d tr in IInsed (i0, to1)))
   | CompGtT ->
     (match insert x tr with
      | IFound -> IFound
      | IInsed (i, to0) ->
        (match i with
         | ISameIndx -> IInsed (ISameIndx, (Node (co, tl, d, to0)))
         | IReddened -> IInsed ((c2i co), (Node (Black, tl, d, to0)))
         | IBlackInc -> let i0,to1 = bal2 tl d to0 in IInsed (i0, to1))))

type dChangedTo =
| StillFits
| Rebalance

(** val bal3 : rbtree -> a -> rbtree -> rbtree **)

let bal3 tl d = function
| Leaf -> assert false (* absurd case *)
| Node (co, tl0, d0, tr0) ->
  (match tl0 with
   | Leaf -> assert false (* absurd case *)
   | Node (co0, tl1, d1, tr1) ->
     (match cof tl1 with
      | Red -> Node (Black, (bal0 tl d tl1 d1 tr1), d0, tr0)
      | Black -> Node (Black, (Node (Black, (Node (Red, tl, d, tl1)), d1, tr1)), d0, tr0)))

(** val bal4 : rbtree -> a -> rbtree -> rbtree **)

let bal4 tl d tr =
  match tl with
  | Leaf -> assert false (* absurd case *)
  | Node (co, tl0, d0, tr0) ->
    (match tr0 with
     | Leaf -> assert false (* absurd case *)
     | Node (co0, tl1, d1, tr1) ->
       (match cof tr1 with
        | Red -> Node (Black, tl0, d0, (bal0 tl1 d1 tr1 d tr))
        | Black -> Node (Black, tl0, d0, (Node (Black, tl1, d1, (Node (Red, tr1, d, tr)))))))

(** val c2d : color -> dChangedTo **)

let c2d = function
| Red -> StillFits
| Black -> Rebalance

(** val r2c : color -> rbtree -> rbtree **)

let r2c c t' =
  match c with
  | Red -> t'
  | Black -> r2b t'

(** val dfitl : color -> ( * ) -> a -> rbtree -> ( * ) **)

let dfitl co dr d tr =
  let dc,t = dr in
  (match dc with
   | StillFits -> StillFits,(Node (co, t, d, tr))
   | Rebalance ->
     (match tr with
      | Leaf -> assert false (* absurd case *)
      | Node (co0, tl0, d0, tr0) ->
        (match co0 with
         | Red -> StillFits,(bal3 t d (Node (Red, tl0, d0, tr0)))
         | Black ->
           (match cof tl0 with
            | Red -> StillFits,(r2c co (bal0 t d tl0 d0 tr0))
            | Black -> (c2d co),(Node (Black, (Node (Red, t, d, tl0)), d0, tr0))))))

(** val dfitr : color -> rbtree -> a -> ( * ) -> ( * ) **)

let dfitr co tl d = function
| dc,t ->
  (match dc with
   | StillFits -> StillFits,(Node (co, tl, d, t))
   | Rebalance ->
     (match tl with
      | Leaf -> assert false (* absurd case *)
      | Node (co0, tl0, d0, tr0) ->
        (match co0 with
         | Red -> StillFits,(bal4 (Node (Red, tl0, d0, tr0)) d t)
         | Black ->
           (match cof tr0 with
            | Red -> StillFits,(r2c co (bal0 tl0 d0 tr0 d t))
            | Black -> (c2d co),(Node (Black, tl0, d0, (Node (Red, tr0, d, t))))))))

(** val t2d : color -> rbtree -> ( * ) **)

let t2d co t =
  match cof t with
  | Red -> StillFits,(r2b t)
  | Black -> (c2d co),t

type dmin =
| Dmleaf
| Dmnode of a * ( * )

(** val delmin : rbtree -> dmin **)

let rec delmin = function
| Leaf -> Dmleaf
| Node (co, tl, d, tr) ->
  (match delmin tl with
   | Dmleaf -> Dmnode (d, (t2d co tr))
   | Dmnode (m, dr) -> Dmnode (m, (dfitl co dr d tr)))

type del =
| Delfnd of ( * )
| Delnot

(** val delete : a -> rbtree -> del **)

let rec delete x = function
| Leaf -> Delnot
| Node (co, tl, d, tr) ->
  (match ordA.compare_spec x d with
   | CompEqT ->
     let h = delmin tr in
     (match h with
      | Dmleaf -> Delfnd (t2d co tl)
      | Dmnode (m, dr) -> Delfnd (dfitr co tl m dr))
   | CompLtT ->
     (match delete x tl with
      | Delfnd r -> Delfnd (dfitl co r d tr)
      | Delnot -> Delnot)
   | CompGtT ->
     (match delete x tr with
      | Delfnd r -> Delfnd (dfitr co tl d r)
      | Delnot -> Delnot))

