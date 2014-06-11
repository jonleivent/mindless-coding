type 'a option =
| Some of 'a
| None

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

type gap =
| G1
| G0

type gaptree =
| Leaf
| Node of gap * gaptree * a * gaptree

type findResult =
| Found
| NotFound

(** val find : a -> gaptree -> findResult **)

let rec find x = function
| Leaf -> NotFound
| Node (g, tl, d, tr) ->
  (match ordA.compare_spec x d with
   | CompEqT -> Found
   | CompLtT -> find x tl
   | CompGtT -> find x tr)

(** val gof : gaptree -> gap option **)

let gof = function
| Leaf -> None
| Node (g, t1, d, t2) -> Some g

(** val setGap : gap -> gaptree -> gaptree **)

let setGap ng = function
| Leaf -> Leaf
| Node (g, t1, d, t2) -> Node (ng, t1, d, t2)

(** val regapAs : gaptree -> gaptree -> gaptree **)

let regapAs t ast =
  match gof ast with
  | Some g0 -> setGap g0 t
  | None -> Leaf

type regapR =
  gaptree
  (* singleton inductive, whose constructor was regapR *)

(** val regapAs' : gaptree -> gaptree -> regapR **)

let regapAs' t ast =
  match gof ast with
  | Some g0 -> setGap g0 t
  | None -> assert false (* absurd case *)

type gapnode =
  gaptree
  (* singleton inductive, whose constructor was Gapnode *)

type ires =
| ISameH
| Higher

type insertResult =
| FoundByInsert
| Inserted of gaptree * ires

(** val rotateRight : gaptree -> a -> gaptree -> gap -> gapnode **)

let rotateRight tl d tr go =
  match tl with
  | Leaf -> assert false (* absurd case *)
  | Node (g0, tl0, d0, tr0) ->
    (match tr0 with
     | Leaf -> Node (go, tl0, d0, (Node (G0, Leaf, d, Leaf)))
     | Node (g1, x, x0, x1) ->
       (match g1 with
        | G1 -> Node (go, tl0, d0, (Node (G0, (setGap G0 tr0), d, (setGap G0 tr))))
        | G0 -> Node (go, (Node (G0, (setGap G0 tl0), d0, x)), x0, (Node (G0, x1, d, (setGap G0 tr))))))

(** val rotateLeft : gaptree -> a -> gaptree -> gap -> gapnode **)

let rotateLeft tl d tr go =
  match tr with
  | Leaf -> assert false (* absurd case *)
  | Node (g0, tl0, d0, tr0) ->
    (match tl0 with
     | Leaf -> Node (go, (Node (G0, Leaf, d, Leaf)), d0, tr0)
     | Node (g1, x, x0, x1) ->
       (match g1 with
        | G1 -> Node (go, (Node (G0, (setGap G0 tl), d, (setGap G0 tl0))), d0, tr0)
        | G0 -> Node (go, (Node (G0, (setGap G0 tl), d, x)), x0, (Node (G0, x1, d0, (setGap G0 tr0))))))

(** val iFitLeft : a -> gap -> gaptree -> gaptree -> a -> gaptree -> insertResult **)

let iFitLeft x c tl t d tr =
  match gof tl with
  | Some g ->
    (match g with
     | G1 -> Inserted ((Node (c, t, d, tr)), ISameH)
     | G0 ->
       (match gof tr with
        | Some g0 ->
          (match g0 with
           | G1 -> Inserted ((rotateRight t d tr c), ISameH)
           | G0 -> Inserted ((Node (G0, t, d, (setGap G1 tr))), Higher))
        | None -> Inserted ((rotateRight t d Leaf c), ISameH)))
  | None ->
    (match gof tr with
     | Some g -> Inserted ((Node (c, t, d, tr)), ISameH)
     | None -> Inserted ((Node (G0, t, d, Leaf)), Higher))

(** val iFitRight : a -> gap -> gaptree -> a -> gaptree -> gaptree -> insertResult **)

let iFitRight x c tl d tr t =
  match gof tr with
  | Some g ->
    (match g with
     | G1 -> Inserted ((Node (c, tl, d, t)), ISameH)
     | G0 ->
       (match gof tl with
        | Some g0 ->
          (match g0 with
           | G1 -> Inserted ((rotateLeft tl d t c), ISameH)
           | G0 -> Inserted ((Node (G0, (setGap G1 tl), d, t)), Higher))
        | None -> Inserted ((rotateLeft Leaf d t c), ISameH)))
  | None ->
    (match gof tl with
     | Some g -> Inserted ((Node (c, tl, d, t)), ISameH)
     | None -> Inserted ((Node (G0, Leaf, d, t)), Higher))

(** val insert : a -> gaptree -> insertResult **)

let rec insert x = function
| Leaf -> Inserted ((Node (G0, Leaf, x, Leaf)), Higher)
| Node (g, tl, d, tr) ->
  (match ordA.compare_spec x d with
   | CompEqT -> FoundByInsert
   | CompLtT ->
     (match insert x tl with
      | FoundByInsert -> FoundByInsert
      | Inserted (t0, i) ->
        (match i with
         | ISameH -> Inserted ((Node (g, t0, d, tr)), ISameH)
         | Higher -> iFitLeft x g tl t0 d tr))
   | CompGtT ->
     (match insert x tr with
      | FoundByInsert -> FoundByInsert
      | Inserted (t0, i) ->
        (match i with
         | ISameH -> Inserted ((Node (g, tl, d, t0)), ISameH)
         | Higher -> iFitRight x g tl d tr t0)))

type dres =
| DSameH
| Lower

type tryLowerResult =
| Lowered of gaptree
| LowerFailed

(** val tryLowering : gaptree -> tryLowerResult **)

let tryLowering = function
| Leaf -> assert false (* absurd case *)
| Node (g, tl, d, tr) ->
  (match gof tl with
   | Some g0 ->
     (match g0 with
      | G1 ->
        (match gof tr with
         | Some g1 ->
           (match g1 with
            | G1 -> Lowered (Node (G0, (setGap G0 tl), d, (setGap G0 tr)))
            | G0 -> LowerFailed)
         | None -> assert false (* absurd case *))
      | G0 -> LowerFailed)
   | None -> LowerFailed)

(** val dRotateLeft : gaptree -> a -> gaptree -> gap -> gapnode **)

let dRotateLeft tl d tr go =
  match tr with
  | Leaf -> assert false (* absurd case *)
  | Node (g, tl0, d0, tr0) ->
    (match tl0 with
     | Leaf -> Node (go, (Node (G1, Leaf, d, Leaf)), d0, (setGap G1 tr0))
     | Node (g0, x, x0, x1) ->
       (match g0 with
        | G1 -> Node (go, (Node (G0, (regapAs tl tl0), d, tl0)), d0, (setGap G1 tr0))
        | G0 ->
          (match gof tr0 with
           | Some g1 ->
             (match g1 with
              | G1 -> Node (go, (Node (G1, (setGap G0 tl), d, x)), x0, (Node (G1, x1, d0, (setGap G0 tr0))))
              | G0 -> Node (go, (Node (G0, (setGap G1 tl), d, tl0)), d0, (setGap G1 tr0)))
           | None -> Node (go, (Node (G1, Leaf, d, Leaf)), x0, (Node (G1, Leaf, d0, Leaf))))))

type delminResult =
| NoMin
| MinDeleted of a * ( * )

(** val dFitLeft : gap -> gaptree -> gaptree -> a -> gaptree -> ( * ) **)

let dFitLeft g tl t' d tr =
  match gof tr with
  | Some g0 ->
    (match g0 with
     | G1 -> (Node (G1, (regapAs' t' tl), d, (setGap G0 tr))),Lower
     | G0 ->
       (match gof tl with
        | Some g1 ->
          (match g1 with
           | G1 ->
             let t = tryLowering tr in
             (match t with
              | Lowered t0 -> (Node (G1, t', d, t0)),Lower
              | LowerFailed -> (dRotateLeft t' d tr g),DSameH)
           | G0 -> (Node (g, t', d, tr)),DSameH)
        | None -> assert false (* absurd case *)))
  | None -> (Node (G1, Leaf, d, Leaf)),Lower

(** val delmin : gaptree -> delminResult **)

let rec delmin = function
| Leaf -> NoMin
| Node (g0, tl, d, tr) ->
  (match delmin tl with
   | NoMin -> MinDeleted (d, ((setGap G1 tr),Lower))
   | MinDeleted (m, dr) ->
     let t,dc = dr in
     MinDeleted (m,
     (match dc with
      | DSameH -> (Node (g0, t, d, tr)),DSameH
      | Lower -> dFitLeft g0 tl t d tr)))

(** val dRotateRight : gaptree -> a -> gaptree -> gap -> gapnode **)

let dRotateRight tl d tr go =
  match tl with
  | Leaf -> assert false (* absurd case *)
  | Node (g, tl0, d0, tr0) ->
    (match tr0 with
     | Leaf -> Node (go, (setGap G1 tl0), d0, (Node (G1, Leaf, d, Leaf)))
     | Node (g0, x, x0, x1) ->
       (match g0 with
        | G1 -> Node (go, (setGap G1 tl0), d0, (Node (G0, tr0, d, (regapAs tr tr0))))
        | G0 ->
          (match gof tl0 with
           | Some g1 ->
             (match g1 with
              | G1 -> Node (go, (Node (G1, (setGap G0 tl0), d0, x)), x0, (Node (G1, x1, d, (setGap G0 tr))))
              | G0 -> Node (go, (setGap G1 tl0), d0, (Node (G0, tr0, d, (setGap G1 tr)))))
           | None -> Node (go, (Node (G1, Leaf, d0, Leaf)), x0, (Node (G1, Leaf, d, Leaf))))))

(** val dFitRight : gap -> gaptree -> a -> gaptree -> gaptree -> ( * ) **)

let dFitRight g tl d tr t' =
  match gof tl with
  | Some g0 ->
    (match g0 with
     | G1 -> (Node (G1, (setGap G0 tl), d, (regapAs' t' tr))),Lower
     | G0 ->
       (match gof tr with
        | Some g1 ->
          (match g1 with
           | G1 ->
             let t = tryLowering tl in
             (match t with
              | Lowered t0 -> (Node (G1, t0, d, t')),Lower
              | LowerFailed -> (dRotateRight tl d t' g),DSameH)
           | G0 -> (Node (g, tl, d, t')),DSameH)
        | None -> assert false (* absurd case *)))
  | None -> (Node (G1, Leaf, d, Leaf)),Lower

type delmaxResult =
| NoMax
| MaxDeleted of a * ( * )

(** val delmax : gaptree -> delmaxResult **)

let rec delmax = function
| Leaf -> NoMax
| Node (g0, tl, d, tr) ->
  (match delmax tr with
   | NoMax -> MaxDeleted (d, ((setGap G1 tl),Lower))
   | MaxDeleted (m, dr) ->
     let t,dc = dr in
     MaxDeleted (m,
     (match dc with
      | DSameH -> (Node (g0, tl, d, t)),DSameH
      | Lower -> dFitRight g0 tl d tr t)))

type deleteResult =
| DelNotFound
| Deleted of ( * )

type twoGaps =
| NoneNone
| G0G0
| G1G1
| NoneG0
| G1G0
| G0None
| G0G1

(** val gof2 : gaptree -> gaptree -> twoGaps **)

let gof2 t1 t2 =
  match gof t2 with
  | Some g ->
    (match g with
     | G1 ->
       (match gof t1 with
        | Some g0 ->
          (match g0 with
           | G1 -> G1G1
           | G0 -> G0G1)
        | None -> assert false (* absurd case *))
     | G0 ->
       (match gof t1 with
        | Some g0 ->
          (match g0 with
           | G1 -> G1G0
           | G0 -> G0G0)
        | None -> NoneG0))
  | None ->
    (match gof t1 with
     | Some g ->
       (match g with
        | G1 -> assert false (* absurd case *)
        | G0 -> G0None)
     | None -> NoneNone)

(** val delMinOrMax : gap -> gaptree -> a -> gaptree -> ( * ) **)

let delMinOrMax g tl d tr =
  match gof2 tl tr with
  | NoneNone -> Leaf,Lower
  | G1G1 ->
    let h = delmin tr in
    (match h with
     | NoMin -> assert false (* absurd case *)
     | MinDeleted (m, dr) ->
       let t,dc = dr in
       (match dc with
        | DSameH -> (Node (g, tl, m, t)),DSameH
        | Lower -> (Node (G1, (setGap G0 tl), m, t)),Lower))
  | NoneG0 -> (setGap G1 tr),Lower
  | G0None -> (setGap G1 tl),Lower
  | G0G1 ->
    let h = delmax tl in
    (match h with
     | NoMax -> assert false (* absurd case *)
     | MaxDeleted (m, dr) -> let t,dc = dr in (Node (g, t, m, tr)),DSameH)
  | _ ->
    let h = delmin tr in
    (match h with
     | NoMin -> assert false (* absurd case *)
     | MinDeleted (m, dr) -> let t,dc = dr in (Node (g, tl, m, t)),DSameH)

(** val delete : a -> gaptree -> deleteResult **)

let rec delete x = function
| Leaf -> DelNotFound
| Node (g, tl, d, tr) ->
  (match ordA.compare_spec x d with
   | CompEqT -> Deleted (delMinOrMax g tl d tr)
   | CompLtT ->
     (match delete x tl with
      | DelNotFound -> DelNotFound
      | Deleted dr ->
        let t0,dc = dr in
        Deleted
        (match dc with
         | DSameH -> (Node (g, t0, d, tr)),DSameH
         | Lower -> dFitLeft g tl t0 d tr))
   | CompGtT ->
     (match delete x tr with
      | DelNotFound -> DelNotFound
      | Deleted dr ->
        let t0,dc = dr in
        Deleted
        (match dc with
         | DSameH -> (Node (g, tl, d, t0)),DSameH
         | Lower -> dFitRight g tl d tr t0)))

