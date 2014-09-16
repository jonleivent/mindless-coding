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

"Fully" Verified, "Fully" Erased, Red/Black Trees

See README.md for details.

***********************************************************************)

Require Import common.
Typeclasses eauto := 8.

Context {A : Set}.
Context {ordA : Ordered A}.

Notation EL := (## (list A)).

Inductive color : Set :=
| Red : color
| Black : color.

Notation EC := (## color).

(***********************************************************************
OKNode captures allowed relationships between the color of the current
node, its height (all heights are "black" heights - only black nodes
are counted), and the colors and height of its left and right
subtrees.
***********************************************************************)
Inductive OKNode
: forall (c : color)(height : EN)(leftColor :  EC)(rightColor : EC)(childHeight : EN), Prop :=
| OKRed{h}         : OKNode Red       h #Black #Black h
| OKBlack{h cl cr} : OKNode Black (ES h)  cl     cr   h.

Hint Constructors OKNode.

(*Lemmas and hints to enable automatic inversion of OKNodes, 
  even in non-Prop contexts.*)
Lemma OKNode1{ho hi cl cr}(ok : OKNode Red ho cl cr hi) : ho=hi/\cl=#Black/\cr=#Black.
Proof. xinv ok. Qed.

Hint Extern 1 => 
match goal with H:OKNode Red _ _ _ _ |- _ => apply OKNode1 in H; simplify_hyps end.

Lemma OKNode2{ho hi cl cr}(ok : OKNode Black ho cl cr hi) : ho=ES hi.
Proof. xinv ok. Qed.

Hint Extern 1 => 
match goal with H:OKNode Black _ _ _ _ |- _ => apply OKNode2 in H; simplify_hyps end.

Lemma OKNode3{ho hi co cr}(ok : OKNode co ho #Red cr hi) : co=Black/\ho=ES hi.
Proof. xinv ok. Qed.

Hint Extern 1 => 
match goal with H:OKNode _ _ #Red _ _ |- _ => apply OKNode3 in H; simplify_hyps end.

Lemma OKNode4{ho hi co cl}(ok : OKNode co ho cl #Red hi) : co=Black/\ho=ES hi.
Proof. xinv ok. Qed.

Hint Extern 1 => 
match goal with H:OKNode _ _ _ #Red _ |- _ => apply OKNode4 in H; simplify_hyps end.

(***********************************************************************
The Red/Black Tree itself, with erasable indices
***********************************************************************)
Inductive rbtree : forall (color : EC)(height : EN)(contents : EL), Set :=
| Leaf : rbtree #Black #0 []
| Node{ho cl cr hi fl fr}
      (co : color)(tl : rbtree cl hi fl)(d : A)(tr : rbtree cr hi fr)
      {ok : OKNode co ho cl cr hi} (*colors and heights correspond properly*)
      {s : Esorted (fl++^d++fr)} (*contents are properly sorted*)
  : rbtree #co ho (fl++^d++fr).

Hint Constructors rbtree.

(************************************************************************)

(*some prettifying tactic notation*)

Tactic Notation 
  "Recurse" hyp(t) "=" "Node" ident(co) ident(tl) ident(d) ident(tr) "[" ident(xl) "|" ident(xr) "]"
  := induction t as [ |? ? ? ? ? ? co tl xl d tr xr]; [zauto| ].

Tactic Notation "Compare" hyp(x) hyp(y) := case (compare_spec x y); intros; subst.

Ltac Call x := let Q := fresh in assert (Q:=x); xinv Q.

(************************************************************************)

Section Find.

  Inductive findResult(x : A) : forall (contents : EL), Set :=
  | Found{fl fr} : findResult x (fl++^x++fr)
  | NotFound{f}{ni : ENotIn x f} : findResult x f.

  Hint Constructors findResult.

  Definition find(x : A){c h f}(t : rbtree c h f) : findResult x f.
  Proof.
    Recurse t = Node c tl d tr [GoLeft|GoRight].
    Compare x d.
    - (*x=d*) eauto.
    - (*x<d*) xinv GoLeft. all:zauto.
    - (*x>d*) xinv GoRight. all:zauto.
  Defined.

End Find.

(************************************************************************)

Definition Cof{c h f}(t : rbtree c h f) : {c' : color | c=#c'}.
Proof. destruct t. all:eexists. all:reflexivity. Defined.

Ltac csplit t := case (Cof t); intros [|] ->.

(************************************************************************)

(*Only Esorted and lt props are needed when solving Esorted props - so
convert all rbtree hyps into Esorted hyps prior to solving Esorted
(sorted, when unerased) props. *)

Definition Sof{c h f}(t : rbtree c h f) : Esorted f.
Proof. destruct t. all:unerase. all:eauto. Defined.

Ltac SofAll :=
  repeat match goal with
             H : rbtree _ _ _ |- _ => apply Sof in H
         end.

Ltac solve_esorted := SofAll; unerase; solve_sorted.

Hint Extern 20 (Esorted _) => solve_esorted.

(************************************************************************)

Definition midRedCombine{h cl cr fl fm fr}
           (tl : rbtree cl h fl)(x:A)(tm : rbtree #Red h fm)(y:A)(tr : rbtree cr h fr)
           {s : Esorted (fl++^x++fm++^y++fr)}
: rbtree #Red (ES h) (fl++^x++fm++^y++fr).
Proof.
  xinv tm. intros. zauto.
Defined.

Hint Extern 40 (rbtree _ _ (_++_++_++_++_)) => eapply midRedCombine.

Definition red2black{h f}(t : rbtree #Red h f) : rbtree #Black (ES h) f.
Proof.
  xinv t. intros. eauto.
Defined.

Hint Extern 10 (rbtree ?C _ ?F) => 
  unify C #Black; match goal with T : rbtree #Red _ F |- _ => apply (red2black T) end.

(***********************************************************************
iChanged captures allowed relationships between the colors and heights
of the input and output nodes of insert.  It is a set, but with erased
indices, and so is available to the runtime as an enumeration type,
which reduces the need for insert to inspect nodes to determine
whether rebalancing is necessary.
***********************************************************************)
Inductive iChanged 
: forall                   (inC : EC)(inH : EN)(outC : EC)(outH : EN), Set :=
| iSameIndx{c h} : iChanged c         h         c              h
| iReddened{h}   : iChanged #Black    h         #Red           h
| iBlackInc{h}   : iChanged #Red      h         #Black     (ES h).

Hint Constructors iChanged.

Hint Extern 100 (OKNode _ _ _ _ _) =>
match goal with H : (OKNode _ _ _ _ _) |- _ =>  xinv H end.

Section insert_rebalancing.

  Inductive iOut(ci : EC)(hi : EN)(f : EL) : Set :=
  | iout{co ho}(i : iChanged ci hi co ho)(to : rbtree co ho f) : iOut ci hi f.

  Hint Constructors iOut.

  Definition rebalRight{h fl fr cr}
             (tl : rbtree #Black (ES h) fl)(d : A)(tr : rbtree cr h fr)
             {s : Esorted (fl++^d++fr)} 
  : iOut #Black (ES h) (fl++^d++fr).
  Proof.
    xinv tl. intros tl0 tr0 ok0 s0.
    csplit tr0.
    - zauto.
    - csplit tl0. all:zauto.
  Defined.

  Definition rebalLeft{h fl fr cl}
             (tl : rbtree cl h fl)(d : A)(tr : rbtree #Black (ES h) fr)
             {s : Esorted (fl++^d++fr)} 
  : iOut #Black (ES h) (fl++^d++fr).
  Proof.
    xinv tr. intros tl0 tr0 ok0 s0.
    csplit tl0.
    - zauto.
    - csplit tr0. all:zauto.
  Defined.

End insert_rebalancing.

Section insertion.

  Hint Resolve rebalRight rebalLeft.

  Definition color2change(c : color){h} 
  : iChanged #c h #Black (match c with Red => ES h | Black => h end).
  Proof.
    destruct c; eauto.
  Defined.

  Hint Extern 5 (iChanged _ _ _ _) => eapply color2change.

  Inductive insertResult(x : A) 
  : forall (inC : EC)(inH : EN)(contents : EL), Set :=
  | FoundByInsert{c h fl fr} : insertResult x c h (fl++^x++fr)
  | Inserted{ci hi co ho fl fr}
          (i : iChanged ci hi co ho)(to : rbtree co ho (fl++^x++fr))
    : insertResult x ci hi (fl++fr).

  Hint Constructors insertResult.

  Definition iout2ins{ci hi fl x fr}(i : iOut ci hi (fl++^x++fr))
  : insertResult x ci hi (fl++fr).
  Proof.
    destruct i. eauto.
  Defined.

  Hint Resolve iout2ins.

  Hint Extern 1 (insertResult _ #Black #0 []) => rewrite <- Eapp_nil_l; eapply Inserted.

  Definition insert(x : A){c h f}(t : rbtree c h f) : insertResult x c h f.
  Proof.
    Recurse t = Node c tl d tr [GoLeft|GoRight].
    Compare x d.
    - (*x=d*) eauto.
    - (*x<d*) xinv GoLeft.
      + zauto.
      + intros i t'. xinv i. all:zauto.
    - (*x>d*) xinv GoRight.
      + zauto.
      + intros i t'. xinv i. all:zauto.
  Defined.

End insertion.

(***********************************************************************
dChanged captures allowed relationships between the colors and heights
of the input and output nodes of delete and delmin.  It is a set, like
iChanged, and reduces the need for delmin and delete to inspect nodes
to determine if rebalancing is necessary.
***********************************************************************)
Inductive dChanged 
: forall (inC : EC)(inH : EN)(outC : EC)(outH : EN), Set :=
| stillFits{ci co h} : ci=co \/ ci=#Red \/ co=#Black -> dChanged ci h co h
| rebalance{h}       : dChanged #Black (ES h) #Black h.

Inductive delout (*intermediate result for delmin and delete*)
: forall (inC : EC)(inH : EN)(contents : EL), Set :=
| Delout {co ho f ci hi}
       (dc : dChanged ci hi co ho)(t : rbtree co ho f) : delout ci hi f.

Hint Constructors delout.

Section delete_rebalancing.

  Hint Constructors dChanged.

  Definition dRotateLeft{h fl fr}
             (tl : rbtree #Black h fl)(d : A)(tr : rbtree #Red (ES h) fr)
             {s : Esorted (fl++^d++fr)}
  : rbtree #Black (ES (ES h)) (fl++^d++fr).
  Proof.
    xinv tr. intros tl0 tr0 ok0 s0.
    xinv tl0. 
    - eauto. 
    - intros tl1 tr1 ok1 s1.
      csplit tl1. 
      + zauto.
      + (*zauto alone used to work here, but no longer*)
        rewrite ?Eapp_assoc.
        rewrite group3Eapp.
        zauto.
  Defined.

  Hint Resolve dRotateLeft.

  Definition dRotateRight{h fl fr}
             (tl : rbtree #Red (ES h) fl)(d : A)(tr : rbtree #Black h fr)
             {s : Esorted (fl++^d++fr)}
  : rbtree #Black (ES (ES h)) (fl++^d++fr).
  Proof.
    xinv tl. intros tl0 tr0 ok0 s0.
    xinv tr0. 
    - eauto. 
    - intros tl1 tr1 ok1 s1.
      csplit tr1. all:zauto.
  Defined.

  Hint Resolve dRotateRight.

  Definition color2dchange(c : color){ho hi}{ok : OKNode c ho # Black # Black hi}
  : dChanged #c ho #Black hi.
  Proof.
    destruct c. all:eauto.
  Defined.

  Hint Resolve color2dchange.

  Definition colorAs(c : color){h f ho}(ok : OKNode c ho # Black # Black h)(t : rbtree # Red h f)
  : rbtree # c ho f.
  Proof.
    destruct c. all:eauto.
  Defined.

  Hint Extern 100 (rbtree _ _ ?F) => 
  match goal with C : color, O : OKNode _ _ #Black #Black _ |- _ => eapply (colorAs C O) end.

  Definition CofOK{h1 c1 h2 c2 c}(ok : OKNode c h1 c1 h2 c2) := c.
  Ltac csplitOK ok := let c := eval compute in (CofOK ok) in destruct c.

  Definition dRebalRight{h fl fr cl co ho}
             (tl : rbtree cl (ES h) fl)(d:A)(tr : rbtree # Black h fr)
             (ok : OKNode co ho cl # Black (ES h)){s : Esorted (fl ++ ^ d ++ fr)}
  : delout # co ho (fl ++ ^ d ++ fr).
  Proof.
    xinv tl. intros tl0 tr0 ok0 s0.
    csplitOK ok0.
    - zauto.
    - csplit tr0. all:zauto. 
  Defined.

  Definition dRebalLeft{h fl fr cr co ho}
             (tl : rbtree # Black h fl)(d:A)(tr : rbtree cr (ES h) fr)
             (ok : OKNode co ho # Black cr (ES h)){s : Esorted (fl ++ ^ d ++ fr)}
  : delout # co ho (fl ++ ^ d ++ fr).
  Proof.
    xinv tr. intros tl0 tr0 ok0 s0.
    csplitOK ok0.
    - zauto.
    - csplit tl0. all:zauto.
  Defined.

  Hint Resolve dRebalRight dRebalLeft.

  Definition dFitLeft{fl cr hi fr co ho cl}
             (dr : delout cl hi fl)(d : A)(tr : rbtree cr hi fr)
             (ok : OKNode co ho cl cr hi){s : Esorted (fl ++ ^ d ++ fr)}
  : delout # co ho (fl ++ ^ d ++ fr).
  Proof.
    xinv dr. intros dc t'. xinv dc. all:zauto.
  Defined.

  Definition dFitRight{cl hi fl fr co ho cr}
             (tl : rbtree cl hi fl)(d : A)(dr : delout cr hi fr)
             (ok : OKNode co ho cl cr hi){s : Esorted (fl ++ ^ d ++ fr)}
  : delout # co ho (fl ++ ^ d ++ fr).
  Proof.
    xinv dr. intros dc t'. xinv dc. all:zauto.
  Defined.

  Definition colorFit{ci hi f co ho}(t : rbtree ci hi f)(ok : OKNode co ho # Black ci hi)
  : delout # co ho f.
  Proof.
    csplit t. all:eauto.
  Defined.

End delete_rebalancing.

Section deletion.

  Hint Resolve colorFit dFitLeft dFitRight.

  Inductive delminResult 
  : forall (inC : EC)(inH : EN)(contents : EL), Set :=
  | NoMin : delminResult #Black #0 []
  | MinDeleted{ci hi f}
              (m : A)(dr : delout ci hi f) : delminResult ci hi (^m++f).

  Hint Constructors delminResult.

  Definition delmin{c h f}(t : rbtree c h f) : delminResult c h f.
  Proof.
    Recurse t = Node c tl d tr [GoLeft|GoRight].
    xinv GoLeft. all:zauto.
  Defined.

  Inductive deleteResult(x : A)(ci : EC)(hi : EN)
  : forall (contents : EL), Set :=
  | DelNotFound{f}{ni : ENotIn x f} : deleteResult x ci hi f
  | Deleted{fl fr}
           (r : delout ci hi (fl++fr)) : deleteResult x ci hi (fl++^x++fr).

  Hint Constructors deleteResult.

  Definition delete(x : A){c h f}(t : rbtree c h f) : deleteResult x c h f.
  Proof.
    Recurse t = Node c tl d tr [GoLeft|GoRight].
    Compare x d.
    - (*x=d*) Call (delmin tr). all:eauto.
    - (*x<d*) xinv GoLeft. all:zauto.
    - (*x>d*) xinv GoRight. all:zauto.
  Defined.

End deletion.

(*The fully erased generated code:*)
Extraction Language Ocaml.
Set Printing Width 132.
Extract Inductive delout => "( * )" [ "(,)" ].
Extract Inductive iOut => "( * )" [ "(,)" ].
Extraction Inline iout2ins.
Extraction "redblack.ml" insert find delmin delete.
