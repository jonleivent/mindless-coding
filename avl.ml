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

type balanceFactor =
| HiLeft
| Flat
| HiRight
| NoSubs

type avltree =
| Leaf
| Node of balanceFactor * avltree * a * avltree

type findResult =
| Found
| NotFound

(** val find : a -> avltree -> findResult **)

let rec find x = function
| Leaf -> NotFound
| Node (b, tl, d, tr) ->
  (match ordA.compare_spec x d with
   | CompEqT -> Found
   | CompLtT -> find x tl
   | CompGtT -> find x tr)

(** val bof : avltree -> balanceFactor **)

let bof = function
| Leaf -> NoSubs
| Node (b, t1, d, t2) -> b

(** val rotateRight : avltree -> a -> avltree -> avltree **)

let rotateRight tl d tr =
  match tl with
  | Leaf -> assert false (* absurd case *)
  | Node (b, tl0, d0, tr0) ->
    (match b with
     | HiLeft -> Node (Flat, tl0, d0, (Node (Flat, tr0, d, tr)))
     | HiRight ->
       (match tr0 with
        | Leaf -> assert false (* absurd case *)
        | Node (b0, tl1, d1, tr1) ->
          (match b0 with
           | HiLeft -> Node (Flat, (Node (Flat, tl0, d0, tl1)), d1, (Node (HiRight, tr1, d, tr)))
           | Flat -> Node (Flat, (Node (Flat, tl0, d0, tl1)), d1, (Node (Flat, tr1, d, tr)))
           | HiRight -> Node (Flat, (Node (HiLeft, tl0, d0, tl1)), d1, (Node (Flat, tr1, d, tr)))
           | NoSubs -> assert false (* absurd case *)))
     | _ -> assert false (* absurd case *))

(** val rotateLeft : avltree -> a -> avltree -> avltree **)

let rotateLeft tl d = function
| Leaf -> assert false (* absurd case *)
| Node (b, tl0, d0, tr0) ->
  (match b with
   | HiLeft ->
     (match tl0 with
      | Leaf -> assert false (* absurd case *)
      | Node (b0, tl1, d1, tr1) ->
        (match b0 with
         | HiLeft -> Node (Flat, (Node (Flat, tl, d, tl1)), d1, (Node (HiRight, tr1, d0, tr0)))
         | Flat -> Node (Flat, (Node (Flat, tl, d, tl1)), d1, (Node (Flat, tr1, d0, tr0)))
         | HiRight -> Node (Flat, (Node (HiLeft, tl, d, tl1)), d1, (Node (Flat, tr1, d0, tr0)))
         | NoSubs -> assert false (* absurd case *)))
   | HiRight -> Node (Flat, (Node (Flat, tl, d, tl0)), d0, tr0)
   | _ -> assert false (* absurd case *))

(** val raised : avltree -> avltree -> bool **)

let raised ti to0 =
  let s = bof ti in
  (match s with
   | Flat ->
     let s0 = bof to0 in
     (match s0 with
      | HiLeft -> true
      | HiRight -> true
      | _ -> false)
   | NoSubs ->
     let s0 = bof to0 in
     (match s0 with
      | Flat -> true
      | _ -> false)
   | _ -> false)

type insertResult =
| FoundByInsert
| Inserted of avltree

(** val ifitl : balanceFactor -> avltree -> a -> avltree -> insertResult **)

let ifitl b to0 d tr =
  match b with
  | HiLeft -> Inserted (rotateRight to0 d tr)
  | Flat -> Inserted (Node (HiLeft, to0, d, tr))
  | HiRight -> Inserted (Node (Flat, to0, d, tr))
  | NoSubs -> assert false (* absurd case *)

(** val ifitr : balanceFactor -> avltree -> a -> avltree -> insertResult **)

let ifitr b tl d to0 =
  match b with
  | HiLeft -> Inserted (Node (Flat, tl, d, to0))
  | Flat -> Inserted (Node (HiRight, tl, d, to0))
  | HiRight -> Inserted (rotateLeft tl d to0)
  | NoSubs -> assert false (* absurd case *)

(** val insert : a -> avltree -> insertResult **)

let rec insert x = function
| Leaf -> Inserted (Node (Flat, Leaf, x, Leaf))
| Node (b, tl, d, tr) ->
  (match ordA.compare_spec x d with
   | CompEqT -> FoundByInsert
   | CompLtT ->
     (match insert x tl with
      | FoundByInsert -> FoundByInsert
      | Inserted to0 ->
        (match raised tl to0 with
         | false -> Inserted (Node (b, to0, d, tr))
         | true -> ifitl b to0 d tr))
   | CompGtT ->
     (match insert x tr with
      | FoundByInsert -> FoundByInsert
      | Inserted to0 ->
        (match raised tr to0 with
         | false -> Inserted (Node (b, tl, d, to0))
         | true -> ifitr b tl d to0)))

(** val lowered : avltree -> avltree -> bool **)

let lowered ti to0 =
  let s = bof ti in
  (match s with
   | Flat ->
     let s0 = bof to0 in
     (match s0 with
      | NoSubs -> true
      | _ -> false)
   | NoSubs -> false
   | _ ->
     let s0 = bof to0 in
     (match s0 with
      | Flat -> true
      | _ -> false))

type delout =
  avltree
  (* singleton inductive, whose constructor was Delout *)

(** val dRotateRight : avltree -> a -> avltree -> delout **)

let dRotateRight tl m tr =
  match tl with
  | Leaf -> assert false (* absurd case *)
  | Node (b, tl0, d, tr0) ->
    (match b with
     | HiLeft -> Node (Flat, tl0, d, (Node (Flat, tr0, m, tr)))
     | Flat -> Node (HiRight, tl0, d, (Node (HiLeft, tr0, m, tr)))
     | HiRight ->
       (match tr0 with
        | Leaf -> assert false (* absurd case *)
        | Node (b0, tl1, d0, tr1) ->
          (match b0 with
           | HiLeft -> Node (Flat, (Node (Flat, tl0, d, tl1)), d0, (Node (HiRight, tr1, m, tr)))
           | Flat -> Node (Flat, (Node (Flat, tl0, d, tl1)), d0, (Node (Flat, tr1, m, tr)))
           | HiRight -> Node (Flat, (Node (HiLeft, tl0, d, tl1)), d0, (Node (Flat, tr1, m, tr)))
           | NoSubs -> assert false (* absurd case *)))
     | NoSubs -> assert false (* absurd case *))

(** val dRotateLeft : avltree -> a -> avltree -> delout **)

let dRotateLeft tl m = function
| Leaf -> assert false (* absurd case *)
| Node (b, tl0, d, tr0) ->
  (match b with
   | HiLeft ->
     (match tl0 with
      | Leaf -> assert false (* absurd case *)
      | Node (b0, tl1, d0, tr1) ->
        (match b0 with
         | HiLeft -> Node (Flat, (Node (Flat, tl, m, tl1)), d0, (Node (HiRight, tr1, d, tr0)))
         | Flat -> Node (Flat, (Node (Flat, tl, m, tl1)), d0, (Node (Flat, tr1, d, tr0)))
         | HiRight -> Node (Flat, (Node (HiLeft, tl, m, tl1)), d0, (Node (Flat, tr1, d, tr0)))
         | NoSubs -> assert false (* absurd case *)))
   | Flat -> Node (HiLeft, (Node (HiRight, tl, m, tl0)), d, tr0)
   | HiRight -> Node (Flat, (Node (Flat, tl, m, tl0)), d, tr0)
   | NoSubs -> assert false (* absurd case *))

(** val dfitl : balanceFactor -> delout -> avltree -> a -> avltree -> delout **)

let dfitl b dr tl d tr =
  match lowered tl dr with
  | false -> Node (b, dr, d, tr)
  | true ->
    (match b with
     | HiLeft -> Node (Flat, dr, d, tr)
     | Flat -> Node (HiRight, dr, d, tr)
     | HiRight -> dRotateLeft dr d tr
     | NoSubs -> assert false (* absurd case *))

(** val dfitr : balanceFactor -> delout -> avltree -> a -> avltree -> delout **)

let dfitr b dr tl d tr =
  match lowered tr dr with
  | false -> Node (b, tl, d, dr)
  | true ->
    (match b with
     | HiLeft -> dRotateRight tl d dr
     | Flat -> Node (HiLeft, tl, d, dr)
     | HiRight -> Node (Flat, tl, d, dr)
     | NoSubs -> assert false (* absurd case *))

type delminResult =
| NoMin
| MinDeleted of a * delout

(** val delmin : avltree -> delminResult **)

let rec delmin = function
| Leaf -> NoMin
| Node (b, tl, d, tr) ->
  (match delmin tl with
   | NoMin -> MinDeleted (d, tr)
   | MinDeleted (m, dr) -> MinDeleted (m, (dfitl b dr tl d tr)))

type deleteResult =
| DelNotFound
| Deleted of delout

(** val delete : a -> avltree -> deleteResult **)

let rec delete x = function
| Leaf -> DelNotFound
| Node (b, tl, d, tr) ->
  (match ordA.compare_spec x d with
   | CompEqT ->
     let h = delmin tr in
     (match h with
      | NoMin -> Deleted tl
      | MinDeleted (m, dr) -> Deleted (dfitr b dr tl m tr))
   | CompLtT ->
     (match delete x tl with
      | DelNotFound -> DelNotFound
      | Deleted dr -> Deleted (dfitl b dr tl d tr))
   | CompGtT ->
     (match delete x tr with
      | DelNotFound -> DelNotFound
      | Deleted dr -> Deleted (dfitr b dr tl d tr)))

