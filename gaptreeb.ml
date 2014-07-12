type __ = Obj.t
let __ = let rec f _ = Obj.repr f in Obj.repr f

(** val xorb : bool -> bool -> bool **)

let xorb b1 b2 =
  if b1 then if b2 then false else true else b2

(** val negb : bool -> bool **)

let negb = function
| true -> false
| false -> true

type nat =
| O
| S of nat

(** val fst : ('a1 * 'a2) -> 'a1 **)

let fst = function
| (x, y) -> x

(** val snd : ('a1 * 'a2) -> 'a2 **)

let snd = function
| (x, y) -> y

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

type 'a compSpecT = compareSpecT

(** val compSpec2Type : 'a1 -> 'a1 -> comparison -> 'a1 compSpecT **)

let compSpec2Type x y c =
  compareSpec2Type c

type 'a sig0 =
  'a
  (* singleton inductive, whose constructor was exist *)

type reflect =
| ReflectT
| ReflectF

(** val iff_reflect : bool -> reflect **)

let iff_reflect = function
| true -> ReflectT
| false -> ReflectF

type 'a eqDec = 'a -> 'a -> bool

type 'a ordered = { eq_dec : 'a eqDec; compare0 : ('a -> 'a -> comparison);
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
                 join : (__ -> __ -> 'a -> __ -> __ -> __ -> __); delmin : (__ -> __ -> ('a, __) delminResult);
                 delmax : (__ -> __ -> ('a, __) delmaxResult); delete : ('a -> __ -> __ -> ('a, __) deleteResult) }

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

type findResult =
| Found
| NotFound

(** val find : a -> gaptree -> findResult **)

let rec find x = function
| Leaf -> NotFound
| Node (gl, tl, d, gr, tr) ->
  (match ordA.compare_spec x d with
   | CompEqT -> Found
   | CompLtT -> find x tl
   | CompGtT -> find x tr)

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

type insertResult0 =
| FoundByInsert
| Inserted0 of gaptree * ires

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

(** val iFitLeft : gap -> gap -> gaptree -> a -> gaptree -> insertResult0 **)

let iFitLeft gl gr t0 d tr =
  match gl with
  | G1 -> Inserted0 ((Node (G0, t0, d, gr, tr)), ISameH)
  | G0 ->
    (match gr with
     | G1 -> Inserted0 ((iRotateRight t0 d tr), ISameH)
     | G0 -> Inserted0 ((Node (G0, t0, d, G1, tr)), Higher))

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

(** val iFitRight : gap -> gap -> gaptree -> a -> gaptree -> insertResult0 **)

let iFitRight gl gr tl d tr =
  match gr with
  | G1 -> Inserted0 ((Node (gl, tl, d, G0, tr)), ISameH)
  | G0 ->
    (match gl with
     | G1 -> Inserted0 ((iRotateLeft tl d tr), ISameH)
     | G0 -> Inserted0 ((Node (G1, tl, d, G0, tr)), Higher))

(** val insert0 : a -> gaptree -> insertResult0 **)

let rec insert0 x = function
| Leaf -> Inserted0 ((Node (G0, Leaf, x, G0, Leaf)), Higher)
| Node (gl, tl, d, gr, tr) ->
  (match ordA.compare_spec x d with
   | CompEqT -> FoundByInsert
   | CompLtT ->
     (match insert0 x tl with
      | FoundByInsert -> FoundByInsert
      | Inserted0 (t1, i) ->
        (match i with
         | ISameH -> Inserted0 ((Node (gl, t1, d, gr, tr)), ISameH)
         | Higher -> iFitLeft gl gr t1 d tr))
   | CompGtT ->
     (match insert0 x tr with
      | FoundByInsert -> FoundByInsert
      | Inserted0 (t1, i) ->
        (match i with
         | ISameH -> Inserted0 ((Node (gl, tl, d, gr, t1)), ISameH)
         | Higher -> iFitRight gl gr tl d t1)))

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

type delminResult0 =
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
        | Lowered t0 -> (Node (G1, tl, d, G0, t0)),Lower
        | LowerFailed -> (dRotateLeft tl d tr),DSameH))
  | G0 -> (Node (G1, tl, d, gr, tr)),DSameH

(** val delmin0 : gaptree -> delminResult0 **)

let rec delmin0 = function
| Leaf -> NoMin
| Node (gl, tl, d, gr, tr) ->
  (match delmin0 tl with
   | NoMin -> MinDeleted (d, (tr,Lower))
   | MinDeleted (m, dr) ->
     let t0,dr0 = dr in
     (match dr0 with
      | DSameH -> MinDeleted (m, ((Node (gl, t0, d, gr, tr)),DSameH))
      | Lower ->
        if isLeaf tr
        then MinDeleted (m, ((Node (G0, Leaf, d, G0, Leaf)),Lower))
        else MinDeleted (m, (dFitLeft gl gr t0 d tr))))

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
        | Lowered t0 -> (Node (G0, t0, d, G1, tr)),Lower
        | LowerFailed -> (dRotateRight tl d tr),DSameH))
  | G0 -> (Node (gl, tl, d, G1, tr)),DSameH

type delmaxResult0 =
| NoMax
| MaxDeleted of a * ( * )

(** val delmax0 : gaptree -> delmaxResult0 **)

let rec delmax0 = function
| Leaf -> NoMax
| Node (gl, tl, d, gr, tr) ->
  (match delmax0 tr with
   | NoMax -> MaxDeleted (d, (tl,Lower))
   | MaxDeleted (m, dr) ->
     let t0,dr0 = dr in
     (match dr0 with
      | DSameH -> MaxDeleted (m, ((Node (gl, tl, d, gr, t0)),DSameH))
      | Lower ->
        if isLeaf tl
        then MaxDeleted (m, ((Node (G0, Leaf, d, G0, Leaf)),Lower))
        else MaxDeleted (m, (dFitRight gl gr tl d t0))))

(** val delMinOrMax : gap -> gap -> gaptree -> a -> gaptree -> ( * ) **)

let delMinOrMax gl gr tl d tr =
  match gl with
  | G1 ->
    (match gr with
     | G1 ->
       let h = delmin0 tr in
       (match h with
        | NoMin -> assert false (* absurd case *)
        | MinDeleted (m, dr) ->
          let t0,dr0 = dr in
          (match dr0 with
           | DSameH -> (Node (G1, tl, m, G1, t0)),DSameH
           | Lower -> (Node (G0, tl, m, G1, t0)),Lower))
     | G0 ->
       let h = delmin0 tr in
       (match h with
        | NoMin -> assert false (* absurd case *)
        | MinDeleted (m, dr) ->
          let t0,dr0 = dr in
          (match dr0 with
           | DSameH -> (Node (G1, tl, m, G0, t0)),DSameH
           | Lower -> (Node (G0, tl, m, G0, t0)),Lower)))
  | G0 ->
    (match gr with
     | G1 ->
       let h = delmax0 tl in
       (match h with
        | NoMax -> assert false (* absurd case *)
        | MaxDeleted (m, dr) ->
          let t0,dr0 = dr in
          (match dr0 with
           | DSameH -> (Node (G0, t0, m, G1, tr)),DSameH
           | Lower -> (Node (G0, t0, m, G0, tr)),Lower))
     | G0 ->
       let h = delmin0 tr in
       (match h with
        | NoMin -> Leaf,Lower
        | MinDeleted (m, dr) ->
          let t0,dr0 = dr in
          (match dr0 with
           | DSameH -> (Node (G0, tl, m, G0, t0)),DSameH
           | Lower -> (Node (G0, tl, m, G1, t0)),DSameH)))

type deleteResult0 =
| DelNotFound0
| Deleted0 of ( * )

(** val delete0 : a -> gaptree -> deleteResult0 **)

let rec delete0 x = function
| Leaf -> DelNotFound0
| Node (gl, tl, d, gr, tr) ->
  (match ordA.compare_spec x d with
   | CompEqT -> Deleted0 (delMinOrMax gl gr tl d tr)
   | CompLtT ->
     (match delete0 x tl with
      | DelNotFound0 -> DelNotFound0
      | Deleted0 dr ->
        let t1,dr0 = dr in
        Deleted0
        (match dr0 with
         | DSameH -> (Node (gl, t1, d, gr, tr)),DSameH
         | Lower -> if isLeaf tr then (Node (G0, Leaf, d, G0, Leaf)),Lower else dFitLeft gl gr t1 d tr))
   | CompGtT ->
     (match delete0 x tr with
      | DelNotFound0 -> DelNotFound0
      | Deleted0 dr ->
        let t1,dr0 = dr in
        Deleted0
        (match dr0 with
         | DSameH -> (Node (gl, tl, d, gr, t1)),DSameH
         | Lower -> if isLeaf tl then (Node (G0, Leaf, d, G0, Leaf)),Lower else dFitRight gl gr tl d t1)))

(** val g2h : nat -> gap -> nat **)

let g2h ph = function
| G1 -> pred (pred ph)
| G0 -> pred ph

type jres =
| JSameH
| JHigher

type joinResult =
| JoinResult of nat * gaptree * jres

(** val joinle : nat -> gaptree -> a -> nat -> gaptree -> joinResult **)

let joinle h1 t1 d h2 t2 =
  let rec f g t3 t4 h3 =
    match g with
    | Leaf -> JoinResult ((S O), (Node (G0, Leaf, d, G0, Leaf)), JHigher)
    | Node (gl, tl, d0, gr, tr) ->
      if (=) h1 h3
      then JoinResult ((S h3), (Node (G0, t4, d, G0, t3)), JHigher)
      else if (=) (S h1) h3
           then JoinResult ((S (S h1)), (Node (G1, t4, d, G0, t3)), JHigher)
           else (match gl with
                 | G1 ->
                   let JoinResult (x, x0, x1) = f tl tl t4 (pred (pred h3)) in
                   (match x1 with
                    | JSameH -> JoinResult (h3, (Node (gl, x0, d0, gr, tr)), JSameH)
                    | JHigher -> JoinResult (h3, (Node (G0, x0, d0, gr, tr)), JSameH))
                 | G0 ->
                   let JoinResult (x, x0, x1) = f tl tl t4 (pred h3) in
                   (match x1 with
                    | JSameH -> JoinResult (h3, (Node (G0, x0, d0, gr, tr)), JSameH)
                    | JHigher ->
                      (match gr with
                       | G1 -> JoinResult (h3, (iRotateRight x0 d0 tr), JSameH)
                       | G0 -> JoinResult ((S h3), (Node (G0, x0, d0, G1, tr)), JHigher))))
  in f t2 t2 t1 h2

(** val joinge : nat -> gaptree -> a -> nat -> gaptree -> joinResult **)

let joinge h1 t1 d h2 t2 =
  let rec f g t3 h3 t4 =
    match g with
    | Leaf -> JoinResult ((S O), (Node (G0, Leaf, d, G0, Leaf)), JHigher)
    | Node (gl, tl, d0, gr, tr) ->
      if (=) h3 h2
      then JoinResult ((S h2), (Node (G0, t3, d, G0, t4)), JHigher)
      else if (=) (S h2) h3
           then JoinResult ((S (S h2)), (Node (G0, t3, d, G1, t4)), JHigher)
           else (match gr with
                 | G1 ->
                   let JoinResult (x, x0, x1) = f tr tr (pred (pred h3)) t4 in
                   (match x1 with
                    | JSameH -> JoinResult (h3, (Node (gl, tl, d0, gr, x0)), JSameH)
                    | JHigher -> JoinResult (h3, (Node (gl, tl, d0, G0, x0)), JSameH))
                 | G0 ->
                   let JoinResult (x, x0, x1) = f tr tr (pred h3) t4 in
                   (match x1 with
                    | JSameH -> JoinResult (h3, (Node (gl, tl, d0, G0, x0)), JSameH)
                    | JHigher ->
                      (match gl with
                       | G1 -> JoinResult (h3, (iRotateLeft tl d0 x0), JSameH)
                       | G0 -> JoinResult ((S h3), (Node (G1, tl, d0, G0, x0)), JHigher))))
  in f t1 t1 h1 t2

(** val join0 : nat -> gaptree -> a -> nat -> gaptree -> joinResult **)

let join0 h1 t1 d h2 t2 =
  if (<) h1 h2 then joinle h1 t1 d h2 t2 else joinge h1 t1 d h2 t2

type gaphtree =
| Gaphtree of nat * gaptree

(** val gaphtree_tree : a tree **)

let gaphtree_tree =
  { leaf = (Obj.magic (Gaphtree (O, Leaf))); break = (fun _ t0 ->
    let Gaphtree (h, t1) = Obj.magic t0 in
    (match t1 with
     | Leaf -> BreakLeaf
     | Node (gl, g1, d, gr, g2) ->
       BreakNode ((Obj.magic (Gaphtree ((g2h h gl), g1))), d, (Obj.magic (Gaphtree ((g2h h gr), g2))))));
    insert = (fun x _ t0 ->
    let Gaphtree (h, t1) = Obj.magic t0 in
    let h0 = insert0 x t1 in
    let x0 = fun _ _ ->
      match h0 with
      | FoundByInsert -> InsertFound
      | Inserted0 (t2, i) ->
        (match i with
         | ISameH -> Inserted (Gaphtree (h, t2))
         | Higher -> Inserted (Gaphtree ((S h), t2)))
    in
    Obj.magic x0 __ __); join = (fun _ tl d _ tr _ ->
    let Gaphtree (h, tl0) = Obj.magic tl in
    let Gaphtree (h0, tr0) = Obj.magic tr in
    let JoinResult (x, x0, x1) = join0 h tl0 d h0 tr0 in Obj.magic (Gaphtree (x, x0))); delmin = (fun _ t0 ->
    let Gaphtree (h, t1) = Obj.magic t0 in
    let h0 = delmin0 t1 in
    let x = fun _ _ ->
      match h0 with
      | NoMin -> DelminLeaf
      | MinDeleted (m, dr) ->
        let t2,dr0 = dr in
        (match dr0 with
         | DSameH -> DelminNode (m, (Gaphtree (h, t2)))
         | Lower -> DelminNode (m, (Gaphtree ((pred h), t2))))
    in
    Obj.magic x __ __); delmax = (fun _ t0 ->
    let Gaphtree (h, t1) = Obj.magic t0 in
    let h0 = delmax0 t1 in
    let x = fun _ _ ->
      match h0 with
      | NoMax -> DelmaxLeaf
      | MaxDeleted (m, dr) ->
        let t2,dr0 = dr in
        (match dr0 with
         | DSameH -> DelmaxNode (m, (Gaphtree (h, t2)))
         | Lower -> DelmaxNode (m, (Gaphtree ((pred h), t2))))
    in
    Obj.magic x __ __); delete = (fun x _ t0 ->
    let Gaphtree (h, t1) = Obj.magic t0 in
    let h0 = delete0 x t1 in
    let x0 = fun _ ->
      match h0 with
      | DelNotFound0 -> DelNotFound
      | Deleted0 dr ->
        let t2,dr0 = dr in
        (match dr0 with
         | DSameH -> Deleted (Gaphtree (h, t2))
         | Lower -> Deleted (Gaphtree ((pred h), t2)))
    in
    Obj.magic x0 __) }

