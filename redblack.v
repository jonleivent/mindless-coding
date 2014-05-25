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

Context {A : Type}.
Context {ordA : Ordered A}.

Notation EL := (## (list A)).

Inductive color : Set :=
| Red : color
| Black : color.

Notation EC := (## color).

Inductive OKNode : color -> EN -> EC -> EC -> EN -> Prop :=
| OKRed{n} : OKNode Red n #Black #Black n
| OKBlack{n cl cr} : OKNode Black (ES n) cl cr n.

Hint Constructors OKNode.

Lemma OKNode1{no ni cl cr}(ok : OKNode Red no cl cr ni) : no=ni/\cl=#Black/\cr=#Black.
Proof. xinv ok. Qed.

Hint Extern 1 => 
match goal with H:OKNode Red _ _ _ _ |- _ => apply OKNode1 in H; simplify_hyps end.

Lemma OKNode2{no ni cl cr}(ok : OKNode Black no cl cr ni) : no=ES ni.
Proof. xinv ok. Qed.

Hint Extern 1 => 
match goal with H:OKNode Black _ _ _ _ |- _ => apply OKNode2 in H; simplify_hyps end.

Lemma OKNode3{no ni co cr}(ok : OKNode co no #Red cr ni) : co=Black/\no=ES ni.
Proof. xinv ok. Qed.

Hint Extern 1 => 
match goal with H:OKNode _ _ #Red _ _ |- _ => apply OKNode3 in H; simplify_hyps end.

Lemma OKNode4{no ni co cl}(ok : OKNode co no cl #Red ni) : co=Black/\no=ES ni.
Proof. xinv ok. Qed.

Hint Extern 1 => 
match goal with H:OKNode _ _ _ #Red _ |- _ => apply OKNode4 in H; simplify_hyps end.

Inductive rbtree : EC -> EN -> EL -> Type :=
| Leaf : rbtree #Black #0 []
| Node{no cl cr ni fl fr}
      (co : color)(tl : rbtree cl ni fl)(d : A)(tr : rbtree cr ni fr)
      {ok : OKNode co no cl cr ni}{s : Esorted (fl++^d++fr)}
  : rbtree #co no (fl++^d++fr).

Hint Constructors rbtree.

Tactic Notation 
  "Recurse" hyp(t) "=" "Node" ident(co) ident(tl) ident(d) ident(tr) "[" ident(xl) "|" ident(xr) "]"
  := induction t as [ |? ? ? ? ? ? co tl xl d tr xr]; [zauto| ].

Tactic Notation "Compare" hyp(x) hyp(y) := case (compare_spec x y); intros; subst.

Definition Sof{c n f}(t : rbtree c n f) : Esorted f.
Proof.
  destruct t. all:unerase. all:eauto.
Defined.

Hint Resolve Sof.

Ltac Sofem :=
  repeat match goal with
             H : rbtree _ _ _ |- _ => apply Sof in H
         end.

Ltac solve_esorted := Sofem; unerase; solve_sorted.

Hint Extern 20 (Esorted _) => solve_esorted.

Section Find.

  Inductive fnd(x : A) : EL -> Type :=
  | Found{fl fr} : fnd x (fl++^x++fr)
  | NotFound{f}{ni : ENotIn x f} : fnd x f.

  Hint Constructors fnd.

  Definition find(x : A){c n f}(t : rbtree c n f) : fnd x f.
  Proof.
    Recurse t = Node c tl d tr [GoLeft|GoRight].
    Compare x d.
    - eauto.
    - xinv GoLeft. all:zauto.
    - xinv GoRight. all:zauto.
  Defined.

End Find.

Definition bal0{n cl cr fl fm fr}
           (tl : rbtree cl n fl)(x:A)(tm : rbtree #Red n fm)(y:A)(tr : rbtree cr n fr)
           {s : Esorted (fl++^x++fm++^y++fr)}
: rbtree #Red (ES n) (fl++^x++fm++^y++fr).
Proof.
  xinv tm. intros. zauto.
Defined.

Hint Extern 40 (rbtree _ _ (_++_++_++_++_)) => eapply bal0.

Definition r2b{n f}(t : rbtree #Red n f) : rbtree #Black (ES n) f.
Proof.
  xinv t. intros. eauto.
Defined.

Hint Extern 10 (rbtree ?C _ ?F) => 
  unify C #Black; match goal with T : rbtree #Red _ F |- _ => apply (r2b T) end.

Definition Cof{c n f}(t : rbtree c n f) : { c' : color | c=#c' }.
Proof.
  xinv t. all:eexists. all:reflexivity.
Defined.

Ltac csplit t := case (Cof t); intros [|] ->.

Inductive iChangedTo : EC -> EN -> EC -> EN -> Set :=
| iSameIndx{c n} : iChangedTo c n c n
| iReddened{n} : iChangedTo #Black n #Red n
| iBlackInc{n} : iChangedTo #Red n #Black (ES n).

Hint Constructors iChangedTo.

Hint Extern 100 (OKNode _ _ _ _ _) =>
match goal with H : (OKNode _ _ _ _ _) |- _ =>  xinv H end.

Section insert_balancing.

  Inductive iOut(ci : EC)(ni : EN)(f : EL) : Type :=
  | iout{co no}(i : iChangedTo ci ni co no)(to : rbtree co no f) : iOut ci ni f.

  Hint Constructors iOut.

  Definition bal1{n fl fr cr}
             (tl : rbtree #Black (ES n) fl)(d : A)(tr : rbtree cr n fr)
             {s : Esorted (fl++^d++fr)} 
  : iOut #Black (ES n) (fl++^d++fr).
  Proof.
    xinv tl. intros tl0 tr0 ok0 s0.
    csplit tr0.
    - zauto.
    - csplit tl0. all:zauto.
  Defined.

  Definition bal2{n fl fr cl}
             (tl : rbtree cl n fl)(d : A)(tr : rbtree #Black (ES n) fr)
             {s : Esorted (fl++^d++fr)} 
  : iOut #Black (ES n) (fl++^d++fr).
  Proof.
    xinv tr. intros tl0 tr0 ok0 s0.
    csplit tl0.
    - zauto.
    - csplit tr0. all:zauto.
  Defined.

End insert_balancing.

Section insertion.

  Hint Resolve bal1 bal2.

  Definition c2i(c : color){n} 
  : iChangedTo #c n #Black (match c with Red => ES n | Black => n end).
  Proof.
    destruct c; eauto.
  Defined.

  Hint Extern 5 (iChangedTo _ _ _ _) => eapply c2i.

  Inductive ins(x : A) : EC -> EN -> EL -> Type :=
  | iFound{c n fl fr} : ins x c n (fl++^x++fr)
  | iInsed{ci ni co no fl fr}
          (i : iChangedTo ci ni co no)(to : rbtree co no (fl++^x++fr))
    : ins x ci ni (fl++fr).

  Hint Constructors ins.

  Definition iout2ins{ci ni fl x fr}(i : iOut ci ni (fl++^x++fr))
  : ins x ci ni (fl++fr).
  Proof.
    destruct i. eauto.
  Defined.

  Hint Resolve iout2ins.

  Hint Extern 1 (ins _ #Black #0 []) => rewrite <- Eapp_nil_l; eapply iInsed.

  Definition insert(x : A){c n f}(t : rbtree c n f) : ins x c n f.
  Proof.
    Recurse t = Node c tl d tr [GoLeft|GoRight].
    Compare x d.
    - eauto.
    - xinv GoLeft.
      + zauto.
      + intros i t'. xinv i. all:zauto.
    - xinv GoRight.
      + zauto.
      + intros i t'. xinv i. all:zauto.
  Defined.

End insertion.

(******************************************************************************)

Inductive dChangedTo : EC -> EN -> EC -> EN -> Set :=
| stillFits{ci co n} : ci=co \/ ci=#Red \/ co=#Black -> dChangedTo ci n co n
| rebalance{n} : dChangedTo #Black (ES n) #Black n.

Inductive dres : EC -> EN -> EL -> Type :=
| Dres {co no f ci ni}
       (dc : dChangedTo ci ni co no)(t : rbtree co no f) : dres ci ni f.

Hint Constructors dres.

Section delete_balancing.

  Hint Constructors dChangedTo.

  Definition bal3{n fl fr}
             (tl : rbtree #Black n fl)(d : A)(tr : rbtree #Red (ES n) fr)
             {s : Esorted (fl++^d++fr)}
  : rbtree #Black (ES (ES n)) (fl++^d++fr).
  Proof.
    xinv tr. intros tl0 tr0 ok0 s0.
    xinv tl0. 
    - eauto. 
    - intros tl1 tr1 ok1 s1.
      csplit tl1. all:zauto.
  Defined.

  Hint Resolve bal3.

  Definition bal4{n fl fr}
             (tl : rbtree #Red (ES n) fl)(d : A)(tr : rbtree #Black n fr)
             {s : Esorted (fl++^d++fr)}
  : rbtree #Black (ES (ES n)) (fl++^d++fr).
  Proof.
    xinv tl. intros tl0 tr0 ok0 s0.
    xinv tr0. 
    - eauto. 
    - intros tl1 tr1 ok1 s1.
      csplit tr1. all:zauto.
  Defined.

  Hint Resolve bal4.

  Definition c2d(c : color){no ni}{ok : OKNode c no # Black # Black ni}
  : dChangedTo #c no #Black ni.
  Proof.
    destruct c. all:eauto.
  Defined.

  Hint Resolve c2d.

  Definition r2c(c : color){n f no}(ok : OKNode c no # Black # Black n)(t' : rbtree # Red n f)
  : rbtree # c no f.
  Proof.
    destruct c. all:eauto.
  Defined.

  Hint Extern 100 (rbtree _ _ ?F) => 
  match goal with C : color, O : OKNode _ _ #Black #Black _ |- _ => eapply (r2c C O) end.

  Definition CofOK{n1 c1 n2 c2 c}(ok : OKNode c n1 c1 n2 c2) := c.
  Ltac csplitOK ok := let c := eval compute in (CofOK ok) in destruct c.

  Definition dball{n fl fr cl co no}
             (tl : rbtree cl (ES n) fl)(d:A)(tr : rbtree # Black n fr)
             (ok : OKNode co no cl # Black (ES n)){s : Esorted (fl ++ ^ d ++ fr)}
  : dres # co no (fl ++ ^ d ++ fr).
  Proof.
    xinv tl. intros tl0 tr0 ok0 s0.
    csplitOK ok0.
    - zauto.
    - csplit tr0. all:zauto. 
  Defined.

  Definition dbalr{n fl fr cr co no}
             (tl : rbtree # Black n fl)(d:A)(tr : rbtree cr (ES n) fr)
             (ok : OKNode co no # Black cr (ES n)){s : Esorted (fl ++ ^ d ++ fr)}
  : dres # co no (fl ++ ^ d ++ fr).
  Proof.
    xinv tr. intros tl0 tr0 ok0 s0.
    csplitOK ok0.
    - zauto.
    - csplit tl0. all:zauto.
  Defined.

  Hint Resolve dball dbalr.

  Definition dfitl{fl cr ni fr co no cl}
             (dr : dres cl ni fl)(d : A)(tr : rbtree cr ni fr)
             (ok : OKNode co no cl cr ni){s : Esorted (fl ++ ^ d ++ fr)}
  : dres # co no (fl ++ ^ d ++ fr).
  Proof.
    xinv dr. intros dc t'. xinv dc. all:zauto.
  Defined.

  Definition dfitr{cl ni fl fr co no cr}
             (tl : rbtree cl ni fl)(d : A)(dr : dres cr ni fr)
             (ok : OKNode co no cl cr ni){s : Esorted (fl ++ ^ d ++ fr)}
  : dres # co no (fl ++ ^ d ++ fr).
  Proof.
    xinv dr. intros dc t'. xinv dc. all:zauto.
  Defined.

  Definition t2d{ci ni f co no}(t : rbtree ci ni f)(ok : OKNode co no # Black ci ni)
  : dres # co no f.
  Proof.
    csplit t. all:eauto.
  Defined.

End delete_balancing.

Hint Resolve t2d.

Hint Resolve  dfitl dfitr.

Inductive dmin : EC -> EN -> EL -> Type :=
| dmleaf : dmin #Black #0 []
| dmnode(m : A){ci ni f}(dr : dres ci ni f) : dmin ci ni (^m++f).

Hint Constructors dmin.

Definition delmin{c n f}(t : rbtree c n f) : dmin c n f.
Proof.
  Recurse t = Node c tl d tr [GoLeft|GoRight].
  xinv GoLeft; intros; subst. all:zauto.
Defined.

Inductive del(x : A)(c : EC)(n : EN) : EL -> Type :=
| delfnd{fl fr}(r : dres c n (fl++fr)) : del x c n (fl++^x++fr)
| delnot{f}{ni : ENotIn x f} : del x c n f.

Hint Constructors del.

Ltac Call x := let Q := fresh in assert (Q:=x); xinv Q.

Definition delete(x : A){c n f}(t : rbtree c n f) : del x c n f.
Proof.
  Recurse t = Node c tl d tr [GoLeft|GoRight].
  Compare x d.
  - Call (delmin tr). all:eauto.
  - xinv GoLeft. all:zauto.
  - xinv GoRight. all:zauto.
Defined.

(*The fully erased generated code:*)
Extraction Language Ocaml.
Set Printing Width 132.
Extract Inductive dres => "( * )" [ "(,)" ].
Extract Inductive iOut => "( * )" [ "(,)" ].
Extraction Inline iout2ins dball dbalr.
Extraction "redblack.ml" insert find delmin delete.
