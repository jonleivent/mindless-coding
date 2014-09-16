(***********************************************************************

Copyright (c) 2014 Jonathan Leivent

Permission is hereby granted, free of charge, to any person obtaining
a copy of this software and associated documentation files (the
"Software"), to deal in the Software without restriction, including
without limitation the rights to use, copy, modify, merge, publish,
distribute, sublicense, and/or sell copies of the Software, and to
permit persons to whom the Software is furnished to do so, subject to
the following conditions:

The above copyright notice and this permission notice shall be
included in all copies or substantial portions of the Software.

THE SOFTWARE IS PROVIDED "AS IS", WITHOUT WARRANTY OF ANY KIND,
EXPRESS OR IMPLIED, INCLUDING BUT NOT LIMITED TO THE WARRANTIES OF
MERCHANTABILITY, FITNESS FOR A PARTICULAR PURPOSE AND
NONINFRINGEMENT. IN NO EVENT SHALL THE AUTHORS OR COPYRIGHT HOLDERS BE
LIABLE FOR ANY CLAIM, DAMAGES OR OTHER LIABILITY, WHETHER IN AN ACTION
OF CONTRACT, TORT OR OTHERWISE, ARISING FROM, OUT OF OR IN CONNECTION
WITH THE SOFTWARE OR THE USE OR OTHER DEALINGS IN THE SOFTWARE.

***********************************************************************)

(***********************************************************************

"Fully" Verified, "Fully" Erased, AVL Trees

See README.md for details.

***********************************************************************)

Require Import common.
Typeclasses eauto := 7.

Context {A : Set}.
Context {ordA : Ordered A}.

Notation EL := (## (list A)).

Inductive balanceFactor : Set :=
| HiLeft  : balanceFactor (*left subtree is 1 higher than right*)
| Flat    : balanceFactor (*both subtrees at same height*)
| HiRight : balanceFactor (*right subtree is 1 higher than left*)
| NoSubs  : balanceFactor (*iff leaf*).

Notation EB := (##balanceFactor).

(***********************************************************************
OKNode captures allowed relationships between the balance factor of the
current node, its height, and the heights of its left and right
subtrees.
***********************************************************************)
Inductive OKNode
: forall (bf : balanceFactor)(nodeHeight : EN)(leftHeight : EN)(rightHeight : EN), Prop :=
| OKHL{h} : OKNode HiLeft     (ES (ES h))        (ES h)               h
| OKF {h} : OKNode Flat           (ES h)             h                h
| OKHR{h} : OKNode HiRight    (ES (ES h))            h            (ES h).

Hint Constructors OKNode.

(*Lemmas and hints to enable automatic inversion of OKNodes, 
  even in non-Prop contexts.*)
Lemma OKNode1{ho hl hr}(ok : OKNode HiLeft ho hl hr) : hl=ES hr /\ ho=ES hl.
Proof. xinv ok. Qed.

Hint Extern 1 =>
match goal with H:OKNode HiLeft _ _ _ |- _ => apply OKNode1 in H; simplify_hyps end.

Lemma OKNode2{ho hl hr}(ok : OKNode Flat ho hl hr) : hl=hr /\ ho=ES hl.
Proof. xinv ok. Qed.

Hint Extern 1 =>
match goal with H:OKNode Flat _ _ _ |- _ => apply OKNode2 in H; simplify_hyps end.

Lemma OKNode3{ho hl hr}(ok : OKNode HiRight ho hl hr) : hr=ES hl /\ ho=ES hr.
Proof. xinv ok. Qed.

Hint Extern 1 =>
match goal with H:OKNode HiRight _ _ _ |- _ => apply OKNode3 in H; simplify_hyps end.

Lemma OKNode4{ho hl hr}(ok : OKNode NoSubs ho hl hr) : False.
Proof. xinv ok. Qed.

Hint Extern 1 =>
match goal with H:OKNode NoSubs _ _ _ |- _ => contradict (OKNode4 H) end.

(***********************************************************************
The AVL Tree itself, with erasable indices
***********************************************************************)
Inductive avltree : forall (balFactor : EB)(height : EN)(contents : EL), Set :=
| Leaf : avltree #NoSubs #0 []
| Node{h bl br hl hr fl fr}
      (b : balanceFactor)(tl : avltree bl hl fl)(d : A)(tr : avltree br hr fr)
      {ok : OKNode b h hl hr} (*balance factor and heights correspond properly*)
      {s : Esorted (fl++^d++fr)} (*contents are properly sorted*)
  : avltree #b h (fl++^d++fr).

Hint Constructors avltree.

(************************************************************************)

(*some prettifying tactic notation*)

Tactic Notation 
  "Recurse" hyp(t) "=" "Node" ident(b) ident(tl) ident(d) ident(tr) "[" ident(xl) "|" ident(xr) "]"
  := induction t as [ |? ? ? ? ? ? ? b tl xl d tr xr]; [zauto| ].

Tactic Notation "Compare" hyp(x) hyp(y) := case (compare_spec x y); intros; subst.

Ltac Call x := let Q := fresh in assert (Q:=x); xinv Q.

(************************************************************************)

Section Find.

  Inductive findResult(x : A) : forall (contents : EL), Set :=
  | Found{fl fr} :  findResult x (fl++^x++fr)
  | NotFound{f}{ni : ENotIn x f} : findResult x f.

  Hint Constructors findResult.

  Definition find(x : A){b h f}(t : avltree b h f) : findResult x f.
  Proof.
    Recurse t = Node b tl d tr [GoLeft|GoRight].
    Compare x d.
    - (*x=d*) eauto.
    - (*x<d*) xinv GoLeft. all:zauto.
    - (*x>d*) xinv GoRight. all:zauto.
  Defined.

End Find.

(************************************************************************)

Definition Bof{b h f}(t : avltree b h f) : {b' : balanceFactor | b=#b'}.
Proof. destruct t. all:eexists. all:reflexivity. Defined.

Ltac bsplit x := (*case-analyze a balance factor, given a source of one*)
  match type of x with
    | balanceFactor => destruct x
    | OKNode ?B _ _ _ => destruct B
    | avltree _ _ _ => destruct (Bof x) as [[ | | | ] ->]
  end.

(************************************************************************)

(*Only Esorted and lt props are needed when solving Esorted props - so
convert all avltree hyps into Esorted hyps prior to solving Esorted
(sorted, when unerased) props. *)

Definition Sof{b h f}(t : avltree b h f) : Esorted f.
Proof. destruct t. all:unerase. all:eauto. Defined.

Ltac SofAll :=
  repeat match goal with
             H : avltree _ _ _ |- _ => apply Sof in H
         end.

Ltac solve_esorted := SofAll; unerase; solve_sorted.

Hint Extern 20 (Esorted _) => solve_esorted.

(************************************************************************)

Inductive heightChange(hlo hhi : EN) : Set :=
| notChanged : hhi=hlo -> heightChange hlo hhi
| yesChanged : hhi=ES hlo -> heightChange hlo hhi.

Hint Constructors heightChange.

(************************************************************************)

Section insertion.

  Definition rotateRight{bl br h fl fr}
             (tl : avltree bl (ES (ES h)) fl)(d : A)(tr : avltree br h fr)
             {s: Esorted(fl++^d++fr)}{notFlat : bl<>#Flat}
  : avltree #Flat (ES (ES h)) (fl++^d++fr).
  Proof.
    xinv tl. intros tl0 tr0 ok0 s0. 
    bsplit ok0.
    - (*HiLeft*) zauto.
    - (*Flat*) eauto.
    - (*HiRight*) xinv tr0. 
      + eauto.
      + intros tl1 tr1 ok1 s1. bsplit ok1; zauto.
    - (*NoSubs*) eauto.
  Defined.

  Definition rotateLeft{bl br h fl fr}
             (tl : avltree bl h fl)(d : A)(tr : avltree br (ES (ES h)) fr)
             {s: Esorted(fl++^d++fr)}{notFlat : br<>#Flat}
  : avltree #Flat (ES (ES h)) (fl++^d++fr).
  Proof.
    xinv tr. intros tl0 tr0 ok0 s0.
    bsplit ok0.
    - (*HiLeft*) xinv tl0. 
      + eauto.
      + intros tl1 tr1 ok1 s1. bsplit ok1; zauto.
    - (*Flat*) eauto.
    - (*HiRight*) zauto.
    - (*NoSubs*) eauto.
  Defined.

  Hint Resolve rotateRight rotateLeft.

  (***********************************************************************
  OKins captures allowed relationships between the balance factors and
  heights of the input and output nodes of insert.  It is a Prop - and
  so completely erased: the runtime uses the raised function to
  determine height changes instead of inverting OKins.
  ***********************************************************************)
  Inductive OKins
  : forall              (inB : EB)(inH : EN)(outB : EB)(outH : EN), Prop :=
  | OKinsEQ{b h} : OKins b         h         b              h
  | OKinsHL2F{h} : OKins #HiLeft   h         #Flat          h
  | OKinsHR2F{h} : OKins #HiRight  h         #Flat          h
  | OKinsF2HL{h} : OKins #Flat     h         #HiLeft   (ES  h)
  | OKinsF2HR{h} : OKins #Flat     h         #HiRight  (ES  h)
  | OKinsN2F     : OKins #NoSubs   #0        #Flat     (ES #0).

  Hint Constructors OKins.

  (* Compare insert input and output to determine if the insert raised
  the output height.  This can be done by just examining the AVL balance
  factors of the two nodes. *)
  Definition raised{bi bo hi ho fi fo}
             (ti : avltree bi hi fi)(to : avltree bo ho fo)
             {oki : OKins bi hi bo ho}
  : heightChange hi ho.
  Proof.
    bsplit ti.
    all: bsplit to.
    all: solve [constructor; xinv oki].
  Defined.

  Inductive insertResult(x : A) 
  : forall (inB : EB)(inH : EN)(contents : EL), Set :=
  | FoundByInsert{bi hi fl fr} : insertResult x bi hi (fl++^x++fr)
  | Inserted{bi hi fl fr bo ho}
            (to : avltree bo ho (fl++^x++fr))
            {oki : OKins bi hi bo ho} 
    : insertResult x bi hi (fl++fr).

  Hint Constructors insertResult.

  Hint Extern 5 => match goal with H: ?n=S ?n |- _ => contradict (n_Sn n H) end.

  Hint Extern 1 (~(_ = _)) =>
  match goal with H : OKins _ _ _ _ |- _ => xinv H; unerase end.

  Hint Extern 1 (insertResult _ #NoSubs #0 []) => rewrite <- Eapp_nil_l; eapply Inserted.

  Definition ifitl{bo hl fl x fm br hr fr bl b ho}
             (to : avltree bo (ES hl) (fl ++ ^ x ++ fm))(d : A)(tr : avltree br hr fr)
             {oki : OKins bl hl bo (ES hl)}{ok : OKNode b ho hl hr}
             {s : Esorted (fl ++ fm ++ ^ d ++ fr)}{l : lt x d}
  : insertResult x # b ho (fl ++ fm ++ ^ d ++ fr).
  Proof.
    bsplit ok.
    - zauto.
    - zauto.
    - zauto.
    - eauto. (*zauto solves this indirectly, with an absurd arg to Inserted - why?*)
  Defined.

  Definition ifitr{bl hl fl bo hr fm x fr br b ho}
             (tl : avltree bl hl fl)(d : A)(to : avltree bo (ES hr) (fm ++ ^ x ++ fr))
             {oki : OKins br hr bo (ES hr)}{ok : OKNode b ho hl hr}
             {s : Esorted (fl ++ ^ d ++ fm ++ fr)}{l : lt d x}
  : insertResult x # b ho (fl ++ ^ d ++ fm ++ fr).
  Proof.
    bsplit ok.
    - zauto.
    - zauto.
    - zauto.
    - eauto. (*zauto solves this indirectly, with an absurd arg to Inserted - why?*)
  Defined.

  Hint Resolve ifitl ifitr.

  Definition insert(x : A){b h f}(t : avltree b h f) : insertResult x b h f.
  Proof.
    Recurse t = Node b tl d tr [GoLeft|GoRight].
    Compare x d.
    - (*x=d*) eauto.
    - (*x<d*) xinv GoLeft. 
      + zauto.
      + intros tl' oki. ecase (raised tl tl'); intro; subst. all:zauto.
    - (*x>d*) xinv GoRight. 
      + zauto.
      + intros tr' oki. ecase (raised tr tr'); intro; subst. all:zauto.
  Defined.

End insertion.

(***********************************************************************
OKdel captures allowed relationships between the balance factors and
heights of the input and output nodes of delete and delmin.  Like
OKins, it is a Prop, and the runtime instead gets information about
deletion height changes from the lowered function.
***********************************************************************)
Inductive OKdel 
: forall               (inB : EB)(inH : EN)(outB : EB)(outH : EN),  Prop :=
| OKdelEq{b h}  : OKdel b             h     b          h
| OKdelF2HL{h}  : OKdel #Flat         h     #HiLeft    h
| OKdelF2HR{h}  : OKdel #Flat         h     #HiRight   h
| OKdelHL2HR{h} : OKdel #HiLeft       h     #HiRight   h
| OKdelHL2F{h}  : OKdel #HiLeft  (ES  h)    #Flat      h
| OKdelHR2HL{h} : OKdel #HiRight      h     #HiLeft    h
| OKdelHR2F{h}  : OKdel #HiRight (ES  h)    #Flat      h
| OKdelF2N      : OKdel #Flat    (ES #0)    #NoSubs    #0.

Hint Constructors OKdel.

Inductive delout (*intermediate result for delmin and delete*)
: forall (inB : EB)(inH : EN)(contents : EL), Set :=
| Delout{bi hi bo ho f}
        (t : avltree bo ho f){okd : OKdel bi hi bo ho} : delout bi hi f.

Hint Constructors delout.

Section delete_rebalancing.

  (* Compare delete input and output to determine if the delete lowered
  the output height.  This can be done by just examining the AVL balance
  factors of the two nodes. *)
  Definition lowered{bi bo hi ho fi fo}
             (ti : avltree bi hi fi)(to : avltree bo ho fo)
             {okd : OKdel bi hi bo ho}
  : heightChange ho hi.
  Proof.
    bsplit ti.
    all: bsplit to.
    all: solve [constructor; xinv okd].
  Defined.

  (* dRotateRight and dRotateRight differ from rotateRight and
  rotateLeft because they allow the additional case where the higher
  sibling is flat - and as a result may produce output at two different
  heights.  However, their proofs are identical. *)
  Definition dRotateRight{bl br h fl fr}
             (tl : avltree bl (ES (ES h)) fl)(m : A)(tr : avltree br h fr)
             {s : Esorted (fl++^m++fr)}
  : delout #HiLeft (ES (ES (ES h))) (fl++^m++fr).
  Proof.
    xinv tl. intros ? tr0 ok0 ?.
    bsplit ok0.
    - (*HiLeft*) zauto.
    - (*Flat*) zauto.
    - (*HiRight*) xinv tr0.
      + eauto.
      + intros ? ? ok1 ?. bsplit ok1. all:zauto.
    - (*NoSubs*) eauto.
  Defined.

  Definition dRotateLeft{bl br h fl fr}
             (tl : avltree bl h fl)(m : A)(tr : avltree br (ES (ES h)) fr)
             {s : Esorted (fl++^m++fr)}
  : delout #HiRight (ES (ES (ES h))) (fl++^m++fr).
  Proof.
    xinv tr. intros tl0 ? ok0 ?. 
    bsplit ok0.
    - (*HiLeft*) xinv tl0.
      + eauto.
      + intros ? ? ok1 ?. bsplit ok1. all:zauto.
    - (*Flat*) zauto.
    - (*HiRight*) zauto.
    - (*NoSubs*) eauto.
  Defined.

  Hint Resolve dRotateRight dRotateLeft.

  Definition dFitLeft{bl hl fl0 fl br hr fr b ho}
             (dr : delout bl hl fl0)
             (tl : avltree bl hl fl)(d : A)(tr : avltree br hr fr)
             {ok : OKNode b ho hl hr}{s : Esorted(fl0++^d++fr)}
  : delout #b ho (fl0++^d++fr).
  Proof.
    xinv dr. intros tl0 okd.
    ecase (lowered tl tl0); intro; subst.
    - zauto.
    - bsplit ok. all:zauto.
  Defined.

  Definition dFitRight{br hr fr0 fr bl hl fl b ho}
             (dr : delout br hr fr0)
             (tl : avltree bl hl fl)(d : A)(tr : avltree br hr fr)
             {ok : OKNode b ho hl hr}{s : Esorted(fl++^d++fr0)}
  : delout #b ho (fl++^d++fr0).
  Proof.
    xinv dr. intros tr0 okd.
    ecase (lowered tr tr0); intro; subst.
    - zauto.
    - bsplit ok. all:zauto.
  Defined.

End delete_rebalancing.

Section deletion.

  Hint Resolve dFitLeft dFitRight.

  (*Auto-solve OKdels by just inverting anything that might be
  appropriate.  Since OKdel is a Prop, all of the resulting operations
  get erased anyway.*)
  Hint Extern 1 (OKdel _ _ ?BL ?BR) =>
  match goal with 
    | H : OKNode _ _ _ _ |- _ => xinv H
    | TL : avltree ?BL _ _ |- _ => xinv TL; intros
    | TR : avltree ?BR _ _ |- _ => xinv TR; intros
  end.

  Inductive delminResult
  : forall (inB : EB)(inH : EN)(contents : EL), Set :=
  | NoMin : delminResult #NoSubs #0 []
  | MinDeleted{bi hi f}
              (m : A)(dr : delout bi hi f) : delminResult bi hi (^m++f).

  Hint Constructors delminResult.

  Definition delmin{b h f}(t : avltree b h f) : delminResult b h f.
  Proof.
    Recurse t = Node b tl d tr [GoLeft|GoRight].
    xinv GoLeft. all:zauto.
  Defined.

  Inductive deleteResult(x : A)(bi : EB)(hi : EN)
  : forall (contents : EL), Set :=
  | DelNotFound{f}{ni : ENotIn x f} : deleteResult x bi hi f
  | Deleted{fl fr}
           (dr : delout bi hi (fl++fr)) : deleteResult x bi hi (fl++^x++fr).

  Hint Constructors deleteResult.

  Definition delete(x : A){b h f}(t : avltree b h f) : deleteResult x b h f.
  Proof.
    Recurse t = Node b tl d tr [GoLeft|GoRight].
    Compare x d.
    - (*x=d*) Call (delmin tr). all:zauto.
    - (*x<d*) xinv GoLeft. all:zauto.
    - (*x>d*) xinv GoRight. all:zauto.
  Defined.

End deletion.

(*The fully erased generated code:*)
Extraction Language Ocaml.
Set Printing Width 132.
Extract Inductive heightChange => "bool" [ "false" "true" ].
Extraction Implicit ifitl [x].
Extraction Implicit ifitr [x].
Extraction "avl.ml" find insert delmin delete.

