type comparison =
| Eq
| Lt
| Gt

type compareSpecT =
| CompEqT
| CompLtT
| CompGtT

type 'a eqDec = 'a -> 'a -> bool

type 'a ordered = { eq_dec : 'a eqDec; compare : ('a -> 'a -> comparison);
                    compare_spec : ('a -> 'a -> compareSpecT) }

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
| Node of gap * gaptree * a * gap * gaptree

(** val isLeaf : gaptree -> bool **)

let isLeaf = function
| Leaf -> true
| Node (gl0, tl, d, gr0, tr) -> false

type gapnode =
  gaptree
  (* singleton inductive, whose constructor was Gapnode *)

type ires =
| ISameH
| Higher

type insertResult =
| FoundByInsert
| Inserted of gaptree * ires

(** val iRotateRight : gaptree -> a -> gaptree -> gapnode **)

let iRotateRight tl d tr =
  match tl with
  | Leaf -> assert false (* absurd case *)
  | Node (gl, tl0, d0, gr, tr0) ->
    (match gr with
     | G1 -> Node (G0, tl0, d0, G0, (Node (G0, tr0, d, G0, tr)))
     | G0 ->
       (match tr0 with
        | Leaf -> assert false (* absurd case *)
        | Node (gl0, tl1, d1, gr0, tr1) ->
          Node (G0, (Node (G0, tl0, d0, gl0, tl1)), d1, G0, (Node (gr0, tr1, d, G0, tr)))))

(** val iFitLeft : gap -> gap -> gaptree -> a -> gaptree -> insertResult **)

let iFitLeft gl gr t d tr =
  match gl with
  | G1 -> Inserted ((Node (G0, t, d, gr, tr)), ISameH)
  | G0 ->
    (match gr with
     | G1 -> Inserted ((iRotateRight t d tr), ISameH)
     | G0 -> Inserted ((Node (G0, t, d, G1, tr)), Higher))

(** val iRotateLeft : gaptree -> a -> gaptree -> gapnode **)

let iRotateLeft tl d = function
| Leaf -> assert false (* absurd case *)
| Node (gl, tl0, d0, gr, tr0) ->
  (match gl with
   | G1 -> Node (G0, (Node (G0, tl, d, G0, tl0)), d0, G0, tr0)
   | G0 ->
     (match tl0 with
      | Leaf -> assert false (* absurd case *)
      | Node (gl0, tl1, d1, gr0, tr1) ->
        Node (G0, (Node (G0, tl, d, gl0, tl1)), d1, G0, (Node (gr0, tr1, d0, G0, tr0)))))

(** val iFitRight : gap -> gap -> gaptree -> a -> gaptree -> insertResult **)

let iFitRight gl gr tl d tr =
  match gr with
  | G1 -> Inserted ((Node (gl, tl, d, G0, tr)), ISameH)
  | G0 ->
    (match gl with
     | G1 -> Inserted ((iRotateLeft tl d tr), ISameH)
     | G0 -> Inserted ((Node (G1, tl, d, G0, tr)), Higher))

(** val insert : a -> gaptree -> insertResult **)

let rec insert x = function
| Leaf -> Inserted ((Node (G0, Leaf, x, G0, Leaf)), Higher)
| Node (gl, tl, d, gr, tr) ->
  (match ordA.compare_spec x d with
   | CompEqT -> FoundByInsert
   | CompLtT ->
     (match insert x tl with
      | FoundByInsert -> FoundByInsert
      | Inserted (t0, i) ->
        (match i with
         | ISameH -> Inserted ((Node (gl, t0, d, gr, tr)), ISameH)
         | Higher -> iFitLeft gl gr t0 d tr))
   | CompGtT ->
     (match insert x tr with
      | FoundByInsert -> FoundByInsert
      | Inserted (t0, i) ->
        (match i with
         | ISameH -> Inserted ((Node (gl, tl, d, gr, t0)), ISameH)
         | Higher -> iFitRight gl gr tl d t0)))

type dres =
| DSameH
| Lower

type tryLowerResult =
| Lowered of gaptree
| LowerFailed

(** val tryLowering : gaptree -> tryLowerResult **)

let tryLowering = function
| Leaf -> assert false (* absurd case *)
| Node (gl0, tl, d, gr0, tr) ->
  (match gl0 with
   | G1 ->
     (match gr0 with
      | G1 -> Lowered (Node (G0, tl, d, G0, tr))
      | G0 -> LowerFailed)
   | G0 -> LowerFailed)

(** val gflip : gap -> gap **)

let gflip = function
| G1 -> G0
| G0 -> G1

(** val dRotateLeft : gaptree -> a -> gaptree -> gapnode **)

let dRotateLeft tl d = function
| Leaf -> assert false (* absurd case *)
| Node (gl, trl, d0, gr, trr) ->
  (match gr with
   | G1 ->
     (match trl with
      | Leaf -> assert false (* absurd case *)
      | Node (gl0, tl0, d1, gr0, tr0) ->
        Node (G1, (Node (G0, tl, d, gl0, tl0)), d1, G1, (Node (gr0, tr0, d0, G0, trr))))
   | G0 -> Node (gl, (Node ((gflip gl), tl, d, G0, trl)), d0, G1, trr))

type delminResult =
| NoMin
| MinDeleted of a * ( * )

(** val dFitLeft : gap -> gap -> gaptree -> a -> gaptree -> ( * ) **)

let dFitLeft gl gr tl d tr =
  match gl with
  | G1 ->
    (match gr with
     | G1 -> (Node (G1, tl, d, G0, tr)),Lower
     | G0 ->
       let h0 = tryLowering tr in
       (match h0 with
        | Lowered t -> (Node (G1, tl, d, G0, t)),Lower
        | LowerFailed -> (dRotateLeft tl d tr),DSameH))
  | G0 -> (Node (G1, tl, d, gr, tr)),DSameH

(** val delmin : gaptree -> delminResult **)

let rec delmin = function
| Leaf -> NoMin
| Node (gl, tl, d, gr, tr) ->
  (match delmin tl with
   | NoMin -> MinDeleted (d, (tr,Lower))
   | MinDeleted (m, dr) ->
     let t,dr0 = dr in
     (match dr0 with
      | DSameH -> MinDeleted (m, ((Node (gl, t, d, gr, tr)),DSameH))
      | Lower ->
        if isLeaf tr
        then MinDeleted (m, ((Node (G0, Leaf, d, G0, Leaf)),Lower))
        else MinDeleted (m, (dFitLeft gl gr t d tr))))

(** val dRotateRight : gaptree -> a -> gaptree -> gapnode **)

let dRotateRight tl d tr =
  match tl with
  | Leaf -> assert false (* absurd case *)
  | Node (gl, tll, d0, gr, tlr) ->
    (match gl with
     | G1 ->
       (match tlr with
        | Leaf -> assert false (* absurd case *)
        | Node (gl0, tl0, d1, gr0, tr0) ->
          Node (G1, (Node (G0, tll, d0, gl0, tl0)), d1, G1, (Node (gr0, tr0, d, G0, tr))))
     | G0 -> Node (G1, tll, d0, gr, (Node (G0, tlr, d, (gflip gr), tr))))

(** val dFitRight : gap -> gap -> gaptree -> a -> gaptree -> ( * ) **)

let dFitRight gl gr tl d tr =
  match gr with
  | G1 ->
    (match gl with
     | G1 -> (Node (G0, tl, d, G1, tr)),Lower
     | G0 ->
       let h0 = tryLowering tl in
       (match h0 with
        | Lowered t -> (Node (G0, t, d, G1, tr)),Lower
        | LowerFailed -> (dRotateRight tl d tr),DSameH))
  | G0 -> (Node (gl, tl, d, G1, tr)),DSameH

type delmaxResult =
| NoMax
| MaxDeleted of a * ( * )

(** val delmax : gaptree -> delmaxResult **)

let rec delmax = function
| Leaf -> NoMax
| Node (gl, tl, d, gr, tr) ->
  (match delmax tr with
   | NoMax -> MaxDeleted (d, (tl,Lower))
   | MaxDeleted (m, dr) ->
     let t,dr0 = dr in
     (match dr0 with
      | DSameH -> MaxDeleted (m, ((Node (gl, tl, d, gr, t)),DSameH))
      | Lower ->
        if isLeaf tl
        then MaxDeleted (m, ((Node (G0, Leaf, d, G0, Leaf)),Lower))
        else MaxDeleted (m, (dFitRight gl gr tl d t))))

(** val delMinOrMax : gap -> gap -> gaptree -> a -> gaptree -> ( * ) **)

let delMinOrMax gl gr tl d tr =
  match gl with
  | G1 ->
    (match gr with
     | G1 ->
       let h = delmin tr in
       (match h with
        | NoMin -> assert false (* absurd case *)
        | MinDeleted (m, dr) ->
          let t,dr0 = dr in
          (match dr0 with
           | DSameH -> (Node (G1, tl, m, G1, t)),DSameH
           | Lower -> (Node (G0, tl, m, G1, t)),Lower))
     | G0 ->
       let h = delmin tr in
       (match h with
        | NoMin -> assert false (* absurd case *)
        | MinDeleted (m, dr) ->
          let t,dr0 = dr in
          (match dr0 with
           | DSameH -> (Node (G1, tl, m, G0, t)),DSameH
           | Lower -> (Node (G0, tl, m, G0, t)),Lower)))
  | G0 ->
    (match gr with
     | G1 ->
       let h = delmax tl in
       (match h with
        | NoMax -> assert false (* absurd case *)
        | MaxDeleted (m, dr) ->
          let t,dr0 = dr in
          (match dr0 with
           | DSameH -> (Node (G0, t, m, G1, tr)),DSameH
           | Lower -> (Node (G0, t, m, G0, tr)),Lower))
     | G0 ->
       let h = delmin tr in
       (match h with
        | NoMin -> Leaf,Lower
        | MinDeleted (m, dr) ->
          let t,dr0 = dr in
          (match dr0 with
           | DSameH -> (Node (G0, tl, m, G0, t)),DSameH
           | Lower -> (Node (G0, tl, m, G1, t)),DSameH)))

type deleteResult =
| DelNotFound
| Deleted of ( * )

(** val delete : a -> gaptree -> deleteResult **)

let rec delete x = function
| Leaf -> DelNotFound
| Node (gl, tl, d, gr, tr) ->
  (match ordA.compare_spec x d with
   | CompEqT -> Deleted (delMinOrMax gl gr tl d tr)
   | CompLtT ->
     (match delete x tl with
      | DelNotFound -> DelNotFound
      | Deleted dr ->
        let t0,dr0 = dr in
        Deleted
        (match dr0 with
         | DSameH -> (Node (gl, t0, d, gr, tr)),DSameH
         | Lower ->
           if isLeaf tr
           then (Node (G0, Leaf, d, G0, Leaf)),Lower
           else dFitLeft gl gr t0 d tr))
   | CompGtT ->
     (match delete x tr with
      | DelNotFound -> DelNotFound
      | Deleted dr ->
        let t0,dr0 = dr in
        Deleted
        (match dr0 with
         | DSameH -> (Node (gl, tl, d, gr, t0)),DSameH
         | Lower ->
           if isLeaf tl
           then (Node (G0, Leaf, d, G0, Leaf)),Lower
           else dFitRight gl gr tl d t0)))

