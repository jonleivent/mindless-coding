type bool =
| True
| False

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

(** val compareSpec2Type : comparison -> compareSpecT **)

let compareSpec2Type = function
| Eq -> CompEqT
| Lt -> CompLtT
| Gt -> CompGtT

type 'a sig0 =
  'a
  (* singleton inductive, whose constructor was exist *)

(** val nat_compare : nat -> nat -> comparison **)

let rec nat_compare n m =
  match n with
  | O ->
    (match m with
     | O -> Eq
     | S n0 -> Lt)
  | S n' ->
    (match m with
     | O -> Gt
     | S m' -> nat_compare n' m')

type color =
| Red
| Black

type oKNode =
| OKRed
| OKBlack

type rbtree =
| Leaf
| Node of oKNode * rbtree * nat * rbtree

(** val r2b : rbtree -> rbtree **)

let r2b = function
| Leaf -> assert false (* absurd case *)
| Node (ok, tl, d, tr) -> Node (OKBlack, tl, d, tr)

type blkn =
| Mkblkn of bool * rbtree

(** val blacken : rbtree -> blkn **)

let blacken = function
| Leaf -> Mkblkn (True, Leaf)
| Node (ok, tl, d, tr) ->
  (match ok with
   | OKRed -> Mkblkn (False, (Node (OKBlack, tl, d, tr)))
   | OKBlack -> Mkblkn (True, (Node (OKBlack, tl, d, tr))))

(** val cof : rbtree -> color **)

let cof = function
| Leaf -> Black
| Node (ok, tl, d, tr) ->
  (match ok with
   | OKRed -> Red
   | OKBlack -> Black)

type cComp =
| CCompEQ
| CCompRB
| CCompBR

(** val ccomp : rbtree -> rbtree -> cComp **)

let ccomp t1 t2 =
  match cof t1 with
  | Red ->
    (match cof t2 with
     | Red -> CCompEQ
     | Black -> CCompRB)
  | Black ->
    (match cof t2 with
     | Red -> CCompBR
     | Black -> CCompEQ)

(** val bal0 : nat -> nat -> rbtree -> rbtree -> rbtree -> rbtree **)

let bal0 x y tl tm tr =
  match tm with
  | Leaf -> assert false (* absurd case *)
  | Node (ok, tl0, d, tr0) ->
    Node (OKRed, (Node (OKBlack, tl, x, tl0)), d, (Node (OKBlack, tr0, y, tr)))

type cT =
  rbtree
  (* singleton inductive, whose constructor was mkCT *)

(** val bal1 : rbtree -> nat -> rbtree -> cT **)

let bal1 tl d tr =
  match tl with
  | Leaf -> assert false (* absurd case *)
  | Node (ok, tl0, d0, tr0) ->
    (match cof tr0 with
     | Red -> bal0 d0 d tl0 tr0 tr
     | Black ->
       (match cof tl0 with
        | Red -> Node (OKRed, (r2b tl0), d0, (Node (OKBlack, tr0, d, tr)))
        | Black -> Node (OKBlack, (Node (OKRed, tl0, d0, tr0)), d, tr)))

(** val bal2 : rbtree -> nat -> rbtree -> cT **)

let bal2 tl d = function
| Leaf -> assert false (* absurd case *)
| Node (ok, tl0, d0, tr0) ->
  (match cof tr0 with
   | Red -> Node (OKRed, (Node (OKBlack, tl, d, tl0)), d0, (r2b tr0))
   | Black ->
     (match cof tl0 with
      | Red -> bal0 d d0 tl tl0 tr0
      | Black -> Node (OKBlack, tl, d, (Node (OKRed, tl0, d0, tr0)))))

(** val bal3 : rbtree -> nat -> rbtree -> rbtree **)

let bal3 tl d = function
| Leaf -> assert false (* absurd case *)
| Node (ok, tl0, d0, tr0) -> Node (OKBlack, (bal2 tl d tl0), d0, tr0)

(** val bal4 : rbtree -> nat -> rbtree -> rbtree **)

let bal4 tl d tr =
  match tl with
  | Leaf -> assert false (* absurd case *)
  | Node (ok, tl0, d0, tr0) -> Node (OKBlack, tl0, d0, (bal1 tr0 d tr))

(** val comp : nat -> nat -> compareSpecT **)

let comp x y =
  compareSpec2Type (nat_compare x y)

type fnd =
| Found
| NotFound

(** val find : nat -> rbtree -> fnd **)

let rec find x = function
| Leaf -> NotFound
| Node (ok, tl, d, tr) ->
  (match comp x d with
   | CompEqT -> Found
   | CompLtT -> find x tl
   | CompGtT -> find x tr)

type ins =
| Mkins of bool * rbtree

(** val insert : nat -> rbtree -> ins **)

let rec insert x = function
| Leaf -> Mkins (False, (Node (OKRed, Leaf, x, Leaf)))
| Node (ok, tl, d, tr) ->
  (match comp x d with
   | CompEqT -> Mkins (True, (Node (ok, tl, d, tr)))
   | CompLtT ->
     let Mkins (found, tl') = insert x tl in
     (match ccomp tl tl' with
      | CCompEQ -> Mkins (found, (Node (ok, tl', d, tr)))
      | CCompRB -> Mkins (False, (bal1 tl' d tr))
      | CCompBR -> Mkins (False, (Node (OKBlack, tl', d, tr))))
   | CompGtT ->
     let Mkins (found, tr') = insert x tr in
     (match ccomp tr tr' with
      | CCompEQ -> Mkins (found, (Node (ok, tl, d, tr')))
      | CCompRB -> Mkins (False, (bal2 tl d tr'))
      | CCompBR -> Mkins (False, (Node (OKBlack, tl, d, tr')))))

type dmin =
| Nodmin
| Mkdmin of nat * bool * rbtree

(** val delmin : rbtree -> dmin **)

let rec delmin = function
| Leaf -> Nodmin
| Node (ok, tl, d, tr) ->
  (match delmin tl with
   | Nodmin ->
     (match cof tr with
      | Red -> Mkdmin (d, False, (r2b tr))
      | Black ->
        (match ok with
         | OKRed -> Mkdmin (d, False, tr)
         | OKBlack -> Mkdmin (d, True, tr)))
   | Mkdmin (m, incbh, t) ->
     (match ccomp tl t with
      | CCompEQ ->
        (match incbh with
         | True ->
           (match cof tr with
            | Red -> Mkdmin (m, False, (bal3 t d tr))
            | Black ->
              (match ok with
               | OKRed -> Mkdmin (m, False, (bal2 t d tr))
               | OKBlack -> let Mkblkn (x, x0) = blacken (bal2 t d tr) in Mkdmin (m, x, x0)))
         | False -> Mkdmin (m, False, (Node (ok, t, d, tr))))
      | CCompRB -> Mkdmin (m, False, (Node (OKBlack, t, d, tr)))
      | CCompBR -> assert false (* absurd case *)))

type del =
| Delfnd of bool * rbtree
| Delnot

(** val delete : nat -> rbtree -> del **)

let rec delete x = function
| Leaf -> Delnot
| Node (ok, tl, d, tr) ->
  (match comp x d with
   | CompEqT ->
     let d0 = delmin tr in
     (match d0 with
      | Nodmin ->
        (match ok with
         | OKRed -> Delfnd (False, tl)
         | OKBlack -> let Mkblkn (x0, x1) = blacken tl in Delfnd (x0, x1))
      | Mkdmin (m, incbh, t0) ->
        (match incbh with
         | True ->
           (match cof tl with
            | Red -> Delfnd (False, (bal4 tl m t0))
            | Black ->
              (match ok with
               | OKRed -> Delfnd (False, (bal1 tl m t0))
               | OKBlack -> let Mkblkn (x0, x1) = blacken (bal1 tl m t0) in Delfnd (x0, x1)))
         | False -> Delfnd (False, (Node (ok, tl, m, t0)))))
   | CompLtT ->
     (match delete x tl with
      | Delfnd (incbh, h) ->
        (match ccomp tl h with
         | CCompEQ ->
           (match incbh with
            | True ->
              (match cof tr with
               | Red -> Delfnd (False, (bal3 h d tr))
               | Black ->
                 (match ok with
                  | OKRed -> Delfnd (False, (bal2 h d tr))
                  | OKBlack -> let Mkblkn (x0, x1) = blacken (bal2 h d tr) in Delfnd (x0, x1)))
            | False -> Delfnd (False, (Node (ok, h, d, tr))))
         | CCompRB -> Delfnd (False, (Node (OKBlack, h, d, tr)))
         | CCompBR -> assert false (* absurd case *))
      | Delnot -> Delnot)
   | CompGtT ->
     (match delete x tr with
      | Delfnd (incbh, h) ->
        (match ccomp tr h with
         | CCompEQ ->
           (match incbh with
            | True ->
              (match cof tl with
               | Red -> Delfnd (False, (bal4 tl d h))
               | Black ->
                 (match ok with
                  | OKRed -> Delfnd (False, (bal1 tl d h))
                  | OKBlack -> let Mkblkn (x0, x1) = blacken (bal1 tl d h) in Delfnd (x0, x1)))
            | False -> Delfnd (False, (Node (ok, tl, d, h))))
         | CCompRB -> Delfnd (False, (Node (OKBlack, tl, d, h)))
         | CCompBR -> assert false (* absurd case *))
      | Delnot -> Delnot))

