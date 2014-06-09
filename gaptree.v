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

Require Import common.
Typeclasses eauto := 8.

Context {A : Type}.
Context {ordA : Ordered A}.

Notation EL := (## (list A)).

Inductive Gap : Set :=
| G1 : Gap
| G0 : Gap.

(* We'll use option Gaps because leaves don't have gaps, but still
need to provide something as an index. *)
Notation EG := (## (option Gap)).
Notation SG0 := #(Some G0).
Notation SG1 := #(Some G1).

Inductive OKNode
: forall (height : EN)(leftGap : EG)(leftHeight : EN)(rightGap : EG)(rightHeight : EN), Prop :=
| OKnn{h} : OKNode (ES (ES h)) SG0 (ES h) SG0 (ES h)
| OKgn{h} : OKNode (ES (ES (ES h))) SG1 (ES h) SG0 (ES (ES h))
| OKng{h} : OKNode (ES (ES (ES h))) SG0 (ES (ES h)) SG1 (ES h)
| OKgg{h} : OKNode (ES (ES (ES h))) SG1 (ES h) SG1 (ES h)
| OKll : OKNode (ES #0) #None #0 #None #0
| OKln : OKNode (ES (ES #0)) #None #0 SG0 (ES #0)
| OKnl : OKNode (ES (ES #0)) SG0 (ES #0) #None #0.

Hint Constructors OKNode.

Hint Extern 100 (OKNode _ _ _ _ _) =>
match goal with H : (OKNode _ _ _ _ _) |- _ =>  xinv H end.

(* The gaptree type exposes the gaps of each child as indices in the
parent to make the "gapee" and "avlee" props easier to work with. *)

Inductive gaptree : forall (ogap logap rogap : EG)(height : EN)(contents : EL), Type :=
| Leaf : gaptree #None #None #None #0 []
| Node{ho gl hl fl gr hr fr gll glr grl grr}
      (g : Gap)(tl : gaptree gl gll glr hl fl)(d : A)(tr : gaptree gr grl grr hr fr)
      {ok : OKNode ho gl hl gr hr}
      {s : Esorted (fl++^d++fr)} (*contents are properly sorted*)
  : gaptree #(Some g) gl gr ho (fl++^d++fr).

Hint Constructors gaptree.

(************************************************************************)

(*some prettifying tactic notation*)

Tactic Notation 
  "Recurse" hyp(t) "=" "Node" ident(g) ident(tl) ident(d) ident(tr) "[" ident(xl) "|" ident(xr) "]"
  := induction t as [ |? ? ? ? ? ? ? ? ? ? ? g tl xl d tr xr]; [zauto| ].

Tactic Notation "Compare" hyp(x) hyp(y) := case (compare_spec x y); intros; subst.

Ltac Call x := let Q := fresh in assert (Q:=x); xinv Q.

(************************************************************************)

Section Find.

  Inductive findResult(x : A) : forall (contents : EL), Type :=
  | Found{fl fr} : findResult x (fl++^x++fr)
  | NotFound{f}{ni : ENotIn x f} : findResult x f.

  Hint Constructors findResult.

  Definition find(x : A){g gl gr h f}(t : gaptree g gl gr h f) : findResult x f.
  Proof.
    Recurse t = Node c tl d tr [GoLeft|GoRight].
    Compare x d.
    - (*x=d*) eauto.
    - (*x<d*) xinv GoLeft. all:zauto.
    - (*x>d*) xinv GoRight. all:zauto.
  Qed.

End Find.

(************************************************************************)

Definition Gof{g gl gr h f}(t : gaptree g gl gr h f) : {g' : option Gap | g=#g'}.
Proof. destruct t. all:eexists. all:reflexivity. Qed.

(************************************************************************)

(*Only Esorted and lt props are needed when solving Esorted props - so
convert all rbtree hyps into Esorted hyps prior to solving Esorted
(sorted, when unerased) props. *)

Definition Sof{g gl gr h f}(t : gaptree g gl gr h f) : Esorted f.
Proof. destruct t. all:unerase. all:eauto. Qed.

Ltac SofAll :=
  repeat match goal with
             H : gaptree _ _ _ _ _ |- _ => apply Sof in H
         end.

Ltac solve_esorted := SofAll; unerase; solve_sorted.

Hint Extern 20 (Esorted _) => solve_esorted.

(************************************************************************)

Lemma leaf1{g gl gr f}(t : gaptree g gl gr #0 f) : g=#None /\ gl=#None /\ gr=#None /\ f=[].
Proof.
  xinv t. intros tl tr ok s. xinv ok.
Qed.

Hint Extern 1 =>
match goal with H:gaptree _ _ _ #0 _ |- _ => apply leaf1 in H; simplify_hyps end.

Lemma leaf2{gl gr h f}(t : gaptree #None gl gr h f) : gl=#None /\ gr=#None /\ h=#0 /\ f=[].
Proof.
  xinv t.
Qed.

Hint Extern 1 =>
match goal with H:gaptree #None _ _ _ _ |- _ => apply leaf2 in H; simplify_hyps end.

(************************************************************************)

Hint Extern 1 (_ \/ _) => (left + right).

Hint Extern 1 (~(_ = _)) => intro; simplify_hyps.

Section gapping.

  Definition ngap(g : EG)(n : Gap) :=
    match g with
      | #None => #None
      | _ => #(Some n)
    end.

  Definition setGap{g ng g' gl gr h f}(t : gaptree g gl gr h f){x : g'=ngap g ng}
  : gaptree g' gl gr h f.
  Proof.
    destruct t; subst; simpl; eauto.
  Qed.

  Definition regapAs{g h go gl gr gl' gr' f f'}
             (t : gaptree go gl gr h f)(ast : gaptree g gl' gr' h f') : gaptree g gl gr h f.
  Proof.
    case (Gof ast). intros [g0|] ->.
    - refine (setGap t). exact g0.
      xinv t. xinv ast.
      intros ? ? ok. xinv ok.
    - eauto.
  Qed.

  Inductive RegapR(g gi gl gr : EG)(h : EN)(f : EL) : Type :=
  | regapR{go} : gaptree go gl gr h f -> gi=#None/\go=#None\/gi<>#None/\go=g
                 -> RegapR g gi gl gr h f.

  Definition regapAs'{g h h' gi gl gr gl' gr' f f'}
             (t : gaptree gi gl gr h f)(ast : gaptree g gl' gr' (ES h') f')
  : RegapR g gi gl gr h f.
  Proof.
    case (Gof ast). intros [g0|] ->.
    - econstructor.
      refine (setGap t). exact g0. 2:reflexivity.
      destruct gi as [[|]]; simpl.
      + right. split; eauto.
      + tauto.
    - eauto.
  Qed.

  Inductive gapnode(g : EG)(h : EN)(f : EL) : Type :=
  | Gapnode{gl gr}(t : gaptree g gl gr h f) : gapnode g h f.

End gapping.

Hint Constructors gapnode.

Hint Extern 1 (#(Some ?G) = ngap _ ?V) => is_evar V; instantiate (1:=G).

Section insertion.

  (* Gapee: one child has (or can have) a gap while the other doesn't.  *)
  Definition gapee(gl gr : EG) := (gl=#None \/ gl<>gr).

  Inductive ires(gi go gl gr : EG) : EN -> EN ->  Set :=
  | ISameH{h} : go=gi -> ires gi go gl gr h h
  | Higher{h} : go=SG0 -> gapee gl gr -> ires gi go gl gr h (ES h).

  Inductive insertResult(x : A)
  : forall (inG : EG)(inH : EN)(contents : EL), Type :=
  | FoundByInsert{g h fl fr} : insertResult x g h (fl++^x++fr)
  | Inserted{gi go gl gr hi ho fl fr}
      (t : gaptree go gl gr ho (fl++^x++fr))(i : ires gi go gl gr hi ho)
      : insertResult x gi hi (fl++fr).

  Definition rotateRight{h fl g gll glr grl grr fr}
             (tl : gaptree SG0 gll glr (ES (ES h)) fl)(d : A)(tr : gaptree g grl grr h fr)
             (gg: gapee gll glr)(go : Gap)(s : Esorted (fl++^d++fr))
  : gapnode #(Some go) (ES (ES h)) (fl++^d++fr).
  Proof.
    xinv tl. intros tl1 tl2 ok sl.
    unfold gapee in gg.
    destruct tl2 as [ |? ? ? ? ? ? ? ? ? ? ? [|] tl2l d1 tl2r ok0 s0] eqn:E.
    - assert (h=#0) by xinv ok. subst h.
      apply leaf1 in tr. simplify_hyps.
      econstructor.
      rewrite ?Eapp_assoc.
      econstructor.
      exact tl1.
      econstructor.
      econstructor.
      econstructor.
      all:zauto.
    - assert (ho=h) by xinv ok. subst ho.
      rewrite 2 Eapp_assoc.
      econstructor. econstructor.
      eassumption. econstructor.
      refine (setGap tl2). shelve. shelve. shelve.
      refine (setGap tr). shelve. shelve. shelve.
      2:eauto. 3:eauto.
      Unshelve. 3:shelve. 3:shelve. 4:shelve. 4:shelve.
      instantiate (3:=ES h).
      2:instantiate(1:=G0).
      instantiate (1:=SG0).
      instantiate (1:=SG0).
      3:instantiate (1:=G0).
      4:instantiate (1:=G0).
      all:eauto.
      destruct g as [[|]]. trivial.
      apply leaf2 in tr. simplify_hyps; xinv ok0.
    - assert (ho=ES h) by xinv ok. subst ho.
      rewrite ?Eapp_assoc.
      rewrite group3Eapp.
      clear E.
      econstructor.
      econstructor.
      econstructor.
      refine (setGap tl1). shelve. shelve. shelve.
      eassumption.
      3:econstructor.
      3:eassumption.
      3:refine (setGap tr). 3:shelve. 3:shelve. 3:shelve.
      2:eauto. 3:eauto. 4:eauto.
      1:instantiate (2:=ES h).
      2:instantiate (2:=ES h).
      3:instantiate (1:=G0).
      3:instantiate (1:=G0).
      instantiate(1:=ngap gll G0).
      2:instantiate (1:=ngap g G0).
      eauto. 2:econstructor.
      destruct g as [[|]]; eauto.
      Unshelve.
      shelve.
      reflexivity.
      shelve.
      reflexivity.
  Qed.

  Definition rotateLeft{h fl g gll glr grl grr fr}
             (tl : gaptree g gll glr h fl)(d : A)(tr : gaptree SG0 grl grr (ES (ES h)) fr)
             (gg: gapee grl grr)(go : Gap)(s : Esorted (fl++^d++fr))
  : gapnode #(Some go) (ES (ES h)) (fl++^d++fr).
  Proof.
    xinv tr.
    intros tr1 tr2 ok sr.
    unfold gapee in gg.
    destruct tr1 eqn:E.
    - assert (h=#0) by xinv ok. subst h.
      apply leaf1 in tl. simplify_hyps.
      econstructor.
      rewrite group3Eapp.
      econstructor.
      econstructor.
      econstructor.
      econstructor.
      all:zauto.
    - destruct g0.
      + assert (ho=h) by xinv ok. subst ho.
        rewrite group3Eapp.
        econstructor. econstructor.
        econstructor.
        refine (setGap tl). shelve. shelve. shelve.
        refine (setGap tr1). shelve. shelve. shelve.
        2:eauto. 4:eauto.
        instantiate (1:=SG0). instantiate(1:=SG0). instantiate (1:=ES h). shelve.
        exact tr2.
        instantiate(1:=G0).
        Unshelve.
        5:instantiate(1:=G0);compute;reflexivity.
        3:instantiate(1:=G0).
        eauto. 2:eauto.
        destruct g. destruct o. trivial.
        apply leaf2 in tl. simplify_hyps; xinv ok0.
      + assert(ho=ES h) by xinv ok. subst ho.
        rewrite ?Eapp_assoc.
        rewrite group3Eapp.
        clear E.
        econstructor.
        econstructor.
        econstructor.
        refine (setGap tl). shelve. shelve. shelve.
        eassumption.
        shelve. eauto.
        econstructor.
        eassumption.
        refine (setGap tr2). shelve. shelve. shelve.
        2:eauto. 3:eauto.
        instantiate(2:=ES h). instantiate(1:=ngap grr G0).
        2:instantiate(1:=G0). Unshelve.
        8:reflexivity. 5:reflexivity.
        4:instantiate(2:=ES h).
        4:instantiate(1:=G0).
        2:instantiate(1:=G0).
        eauto. 2:eauto.
        econstructor.
        destruct g. destruct o; eauto.
  Qed.

  Hint Constructors insertResult ires.

  Hint Unfold gapee.

  Hint Extern 1 (insertResult _ #None #0 []) => 
    rewrite <- Eapp_nil_l; eapply Inserted; [econstructor|].

  Definition iFitLeft{gl gll glr hl fl0 fr0 gl0 gr0 gr grl grr hr fr ho x c}
             (tl : gaptree gl gll glr hl (fl0 ++ fr0))
             (t : gaptree SG0 gl0 gr0 (ES hl) (fl0 ++ ^ x ++ fr0))(d : A)
             (tr : gaptree gr grl grr hr fr)
             (ok : OKNode ho gl hl gr hr)(H : lt x d)(H1 : gapee gl0 gr0)
             (s : Esorted ((fl0 ++ fr0) ++ ^ d ++ fr))
  : insertResult x # (Some c) ho (fl0 ++ fr0 ++ ^ d ++ fr).
  Proof.
    case (Gof tl). intros [[|]|] ->.
    - assert (ho=ES (ES hl)) by xinv ok. subst ho.
      econstructor.
      2:zauto.
      zauto.
    - assert (ho=ES hl) by xinv ok. subst ho.
      case (Gof tr). intros [[|]|] ->.
      + assert (hl=ES hr) by xinv ok. subst hl.
        eelim (rotateRight t d tr H1 c). intros ? ? X.  all:zauto.
      + assert (hl=hr) by xinv ok. subst.
        econstructor.
        rewrite group3Eapp.
        econstructor.
        exact t.
        refine (setGap tr). shelve. shelve. shelve.
        instantiate (2:=ES (ES hr)).
        instantiate (1:=SG1).
        all:zauto.
      + assert (hr=#0 /\ hl=ES #0) by xinv ok. simplify_hyps.
        eelim (rotateRight t d tr H1 c). intros ? ? X.
        all:zauto.
    - assert (hl=#0) by xinv ok. subst.
      case (Gof tr). intros [[|]|] ->.
      + zauto.
        + assert(ho=ES hr) by xinv ok. subst.
          assert (hr=ES #0) by xinv ok. subst.
          zauto.
        + assert (hr=#0) by xinv ok. subst.
          assert (ho=ES #0) by xinv ok. subst.
          apply leaf1 in tr. simplify_hyps. 
          econstructor.
          rewrite group3Eapp.
          econstructor.
          exact t.
          all:eauto.
  Unshelve.
  exact G1. eauto.
  Qed.

  Definition iFitRight{gl gll glr hl fl gr grl grr hr fl0 fr0 gl0 gr0 ho x c}
             (tl : gaptree gl gll glr hl fl)(d : A)
             (tr : gaptree gr grl grr hr (fl0 ++ fr0))
             (t : gaptree SG0 gl0 gr0 (ES hr) (fl0 ++ ^ x ++ fr0))
             (ok : OKNode ho gl hl gr hr)(H : lt d x)(H1 : gapee gl0 gr0)
             (s : Esorted (fl ++ ^ d ++ fl0 ++ fr0))
  : insertResult x # (Some c) ho ((fl ++ ^ d ++ fl0) ++ fr0).
  Proof.
    case (Gof tr). intros [[|]|] ->.
    - assert (ho=ES (ES hr)) by xinv ok. subst.
      econstructor.
      2:zauto.
      zauto.
    - assert (ho=ES hr) by xinv ok. subst.
      case (Gof tl). intros [[|]|] ->.
      + assert (hr=ES hl) by xinv ok. subst.
        eelim (rotateLeft tl d t H1 c). intros ? ? X. all:zauto.
      + assert (hr=hl) by xinv ok. subst.
        econstructor.
        rewrite ?Eapp_assoc.
        econstructor.
        refine (setGap tl). shelve. shelve. shelve.
        eassumption.
        instantiate (1:=SG1).
        instantiate (1:=ES (ES hl)).
        all:zauto.
      + assert (hl=#0 /\ hr=ES #0) by xinv ok. simplify_hyps.
        eelim (rotateLeft tl d t H1 c). intros ? ? X.
        all:zauto.
    - assert (hr=#0) by xinv ok; subst.
      case (Gof tl). intros [[|]|] ->.
      + zauto.
      + assert (ho=ES hl) by xinv ok; subst.
        assert (hl=ES #0) by xinv ok; subst.
        zauto.
      + assert (hl=#0) by xinv ok; subst.
        assert (ho=ES #0) by xinv ok; subst.
        apply leaf1 in tl. simplify_hyps.
        econstructor.
        rewrite ?Eapp_assoc.
        econstructor.
        econstructor.
        exact t.
        all:eauto.
  Unshelve.
  exact G1. eauto.
  Qed.

  Definition insert(x : A){g gl gr h f}(t : gaptree g gl gr h f)
  : insertResult x g h f.
  Proof.
    Recurse t = Node c tl d tr [GoLeft|GoRight].
    - Compare x d.
      + (*x=d*) eauto.        
      + (*x<d*)
        xinv GoLeft.
        * zauto.
        * intros t i.
          rewrite ?Eapp_assoc.
          xinv i; intros; simplify_hyps.
          { zauto. }
          { eapply iFitLeft; eassumption. }
      + (*x>d*)
        xinv GoRight.
        * zauto.
        * intros t' i.
          rewrite group3Eapp.
          xinv i; intros; simplify_hyps.
          { zauto. }
          { eapply iFitRight; eassumption. }
  Qed.

End insertion.

Section deletion.
  
  Inductive dres: forall (gi go : EG)(hi ho : EN), Set :=
  | DSameH{g h} : dres g g h h
  | Lower{g go h} : go<>SG0 -> dres g go (ES h) h.

  Hint Constructors dres.

  Inductive delout (*intermediate result for delmin and delete*)
  : forall (inG : EG)(inH : EN)(contents : EL), Type :=
  | Delout {gi go hi ho gl gr f}
           (t : gaptree go gl gr ho f)(dc : dres gi go hi ho) : delout gi hi f.

  Hint Constructors delout.

  (* "AVLish" is the condition of being AVL-like - at least one child
  doesn't have a gap.*)
  Definition avlish(gl gr : EG) := gl=SG0 \/ gr=SG0.

  Inductive tryLowerResult: EG -> EG -> EN -> EL -> Type :=
  | lowered{h f}(t : gaptree SG0 SG0 SG0 (ES h) f) : tryLowerResult SG1 SG1 (ES (ES h)) f
  | lowerFailed{gl gr h f}: avlish gl gr -> tryLowerResult gl gr h f.

  Hint Constructors tryLowerResult.

  Hint Extern 10 (_ = ngap _ _) => compute.

  Hint Unfold avlish.

  (* If a node's children both have gaps, the node can be lowered by 1. *)
  Definition tryLowering{gl gr h f}
             (t : gaptree SG0 gl gr (ES (ES h)) f)
  : tryLowerResult gl gr (ES (ES h)) f.
  Proof.
    xinv t. intros tl tr ok s.
    case (Gof tl). intros [[|]|] ->.
    - case (Gof tr). intros [[|]|] ->.
      + econstructor.
        econstructor.
        eapply (setGap tl). 
        eapply (setGap tr).
        all:eauto.
      + eauto.
      + exfalso. xinv ok.
    - eauto.
    - assert (gr=SG0) by xinv ok. subst.
      eauto.
  Grab Existential Variables.
  2:eauto. 2:eauto.
  Qed.

  Definition dRotateLeft{gl gll glr grl grr h fl fr}
             (tl : gaptree gl gll glr h fl)(d : A)(tr : gaptree SG0 grl grr (ES (ES h)) fr)
             (go : Gap)(H : avlish grl grr){s : Esorted (fl++^d++fr)}
  : gapnode #(Some go) (ES (ES (ES h))) (fl ++ ^ d ++ fr).
  Proof.
    xinv tr.
    intros.
    unfold avlish in H.
    destruct tl0 eqn:E.
    - assert (grr=SG0).
      { destruct H; simplify_hyps. reflexivity. }
      subst grr.
      assert (hr=ES h) by xinv ok. subst hr.
      assert (h=#0) by xinv ok. subst h.
      assert (gl=#None).
      { xinv tl. intros. xinv ok0. }
      subst gl.
      rewrite group3Eapp.
      econstructor.
      econstructor.
      econstructor.
      exact tl.
      econstructor.
      econstructor.
      eauto.
      refine (setGap tr0). shelve. shelve. shelve.
      all:eauto.
      Unshelve.
      2:eauto.
    - destruct g1.
      + assert (grr=SG0).
        { destruct H; simplify_hyps. reflexivity. }
        subst grr.
        assert (ho=h) by xinv ok. subst ho.
        assert (hr=ES h) by xinv ok. subst hr.
        rewrite group3Eapp.
        econstructor.
        econstructor.
        econstructor.
        exact (regapAs tl tl0).
        exact tl0.
        instantiate (1:=ES (ES h)).
        3:refine (setGap tr0). 5:instantiate(1:=G1). 4:eauto.
        3:instantiate (1:=G0). 3:simpl.
        all:eauto.
      + assert (ho=ES h) by xinv ok. subst ho.
        case (Gof tr0). intros [[|]|] ->.
        * assert (hr=h) by xinv ok. subst hr.
          rewrite ?Eapp_assoc.
          rewrite group3Eapp.
          econstructor.
          econstructor.
          econstructor.
          refine (setGap tl). exact G0. exact (ngap gl G0). reflexivity.
          exact g2.
          instantiate (1:=ES h).
          2:eauto. 4:eauto.
          3:instantiate(3:=G1).
          2:econstructor.
          2:exact g3.
          2:refine (setGap tr0). 2:exact G0. 2:exact SG0. 2:eauto.
          2:instantiate (1:=ES h). 4:instantiate(1:=G1).
          all:eauto.
          destruct gl. destruct o; simpl.
          { xinv tl. intros. xinv ok1. all:eauto. }
          { assert (h=#0) by xinv tl. subst h.
            clear E. assert (gl0=#None/\hl=#0) as Q by xinv ok0.
            decompose [and] Q; subst. clear Q.
            econstructor. }
        * assert (hr=ES h) by xinv ok. subst hr.
          rewrite group3Eapp.
          econstructor.
          econstructor.
          econstructor.
          refine (setGap tl). exact G1. exact (ngap gl G1). reflexivity.
          exact tl0.
          1:instantiate(1:=ES (ES h)).
          2:eauto. 4:eauto.
          3:instantiate (3:=G0).
          3:instantiate (1:=ES h).
          3:instantiate (1:=SG1).
          2:refine (setGap tr0). 2:exact G1.
          all:eauto.
          destruct gl. destruct o; simpl.
          { xinv tl; intros; xinv ok1. }
          { assert (h=#0) by xinv tl. subst. econstructor. }
        * assert (hr=#0) by xinv ok. subst hr.
          assert (h=#0) by xinv ok. subst h.
          clear E.
          assert (hl=#0/\gl0=#None/\hr0=#0/\gr=#None) as Q by xinv ok0.
          decompose [and] Q; subst; clear Q.
          assert (gl=#None).
          { xinv tl. intros. xinv ok1. } subst gl.
          rewrite ?Eapp_assoc.
          rewrite group3Eapp.
          econstructor.
          econstructor.
          econstructor.
          exact tl.
          exact g2.
          econstructor.
          eauto.
          econstructor.
          exact g3.
          exact tr0.
          econstructor.
          eauto.
          econstructor.
          eauto.
  Qed.

  Inductive delminResult 
  : forall (inG : EG)(inH : EN)(contents : EL), Type :=
  | NoMin : delminResult #None #0 []
  | MinDeleted{gi hi f}
              (m : A)(dr : delout gi hi f) : delminResult gi hi (^m++f).

  Hint Constructors delminResult.

  Definition dFitLeft{gl gll glr ho0 fl go gl0 gr0 f gr grl grr hr fr ho}
             (g : Gap)(tl : gaptree gl gll glr (ES ho0) fl)
             (t' : gaptree go gl0 gr0 ho0 f)(d : A)(tr : gaptree gr grl grr hr fr)
             (ok : OKNode ho gl (ES ho0) gr hr)(s : Esorted (f++^d++fr))(e : go<>SG0)
  : delout # (Some g) ho (f ++ ^ d ++ fr).
  Proof.
    case (Gof tr). intros [[|]|] ->.
    - assert (ho=ES (ES hr)) by xinv ok. subst.
      elim (regapAs' t' tl). intros.
      econstructor.
      econstructor.
      exact g0.
      refine (setGap tr). exact G0. 2:eauto.
      2:eauto.
      simpl.
      instantiate (1:=ES hr).
      2:instantiate(1:=G1).
      2:econstructor.
      2:intro; discriminate_erasable.
      destruct o.
      { destruct H; subst. xinv ok.
        - xinv t'.
        - xinv t'. }
      { destruct H; subst. xinv ok.
        xinv t'. intros. xinv ok. }
    - assert (ho=ES hr) by xinv ok. subst.
      case (Gof tl). intros [[|]|] ->.
      + assert (hr=ES (ES ho0)) by xinv ok. subst.
        pose (tryLowering tr) as T.
        xinv T. intros.
        * econstructor.
          econstructor.
          refine (setGap t'). shelve. shelve. shelve.
          exact t.
          instantiate (2:=ES (ES ho0)).
          2:eauto.
          2:instantiate (1:=G1). 2:econstructor.
          2:intro; discriminate_erasable.
          Unshelve.
          4:instantiate(2:=ngap go G1).
          3: reflexivity.
          destruct go. destruct o; simpl.
          { destruct g0.
            - xinv t'. intros. xinv ok0.
            - xinv t'. }
          { xinv t'. }
        * intro W.
          eelim (dRotateLeft t' d tr g W). intros ? ? X.
          econstructor. exact X.
          eauto. 
      + assert (hr=ES ho0) by xinv ok. subst.
        econstructor.
        econstructor.
        exact t'.
        exact tr.
        instantiate (1:=ES (ES ho0)).
        2:eauto. 2:instantiate (1:=g). 2:eauto.
        destruct go. destruct o; simpl.
        { destruct g0.
          - xinv t'. intros. xinv ok0.
          - xinv t'. }
        { xinv t'. }
      + exfalso. xinv ok.
    - assert (hr=#0) by xinv ok. subst.
      assert (ho0=#0) by xinv ok. subst.
      assert (gl=SG0) by xinv ok. subst.
      assert (ho=ES (ES #0)) by xinv ok. subst.
      assert (go=#None).
      { xinv t'. intros. xinv ok0. }
      subst.
      econstructor.
      econstructor.
      eassumption.
      eassumption.
      econstructor.
      2:instantiate(1:=G1).
      all:eauto.
  Grab Existential Variables.
  eauto.
  Qed.

  Definition delmin{gi gl gr h f}(t : gaptree gi gl gr h f) : delminResult gi h f.
  Proof.
    Recurse t = Node g tl d tr [GoLeft|GoRight].
    xinv GoLeft. 
    - rewrite Eapp_nil_l.
      assert (ho=ES hr) by xinv ok. subst ho.
      econstructor.
      econstructor.
      refine (setGap tr). shelve. shelve. shelve.
      econstructor.
      Unshelve.
      instantiate (1:=ngap gr G1). intro. 
      destruct gr. destruct o; simpl in H; discriminate_erasable.
      2: eauto.
    - intro dl. xinv dl.
      intros t' dr.
      rewrite ?Eapp_assoc.
      econstructor.
      xinv dr; intros; subst.
      + econstructor.
        econstructor.
        exact t'.
        eassumption.
        eassumption.
        all:eauto.
      + eapply dFitLeft. all:try eassumption.
        eauto.
  Qed.

  Definition dRotateRight{gr gll glr grl grr h fl fr}
             (tl : gaptree SG0 gll glr (ES (ES h)) fl)(d : A)(tr : gaptree gr grl grr h fr)
             (go : Gap)(H : avlish gll glr){s : Esorted (fl++^d++fr)}
  : gapnode #(Some go) (ES (ES (ES h))) (fl ++ ^ d ++ fr).
  Proof.
    xinv tl.
    intros.
    unfold avlish in H.
    destruct tr0 eqn:E.
    - assert (gll=SG0).
      { destruct H; simplify_hyps. reflexivity. } subst gll.
      assert (hl=ES h) by xinv ok. subst hl.
      assert (h=#0) by xinv ok. subst h.
      assert (gr=#None).
      { xinv tr. intros. xinv ok0. } subst gr.
      rewrite ?Eapp_assoc.
      econstructor.
      econstructor.
      refine (setGap tl0). shelve. shelve. shelve.
      econstructor.
      econstructor.
      exact tr.
      all:eauto.
      Unshelve.
      exact G1.
      compute. reflexivity.
    - destruct g1.
      + assert (gll=SG0).
        { destruct H; simplify_hyps. reflexivity. } subst gll.
        assert (ho=h) by xinv ok. subst ho.
        assert (hl=ES h) by xinv ok. subst hl.
        rewrite 2 Eapp_assoc.
        econstructor.
        econstructor.
        refine(setGap tl0). exact G1. exact SG1. compute. reflexivity.
        econstructor.
        exact tr0.
        exact (regapAs tr tr0).
        instantiate (1:=ES (ES h)).
        3:instantiate (1:=G0).
        xinv ok. all:eauto.
      + assert (ho=ES h) by xinv ok. subst ho.
        case (Gof tl0). intros [[|]|] ->.
        * assert (hl=h) by xinv ok. subst hl.
          rewrite ?Eapp_assoc.
          rewrite group3Eapp.
          econstructor.
          econstructor.
          econstructor.
          refine (setGap tl0). exact G0. exact SG0. compute. reflexivity.
          exact g2.
          shelve. eauto.
          econstructor.
          exact g3.
          refine (setGap tr). exact G0. 2:reflexivity.
          2:eauto. 3:eauto. Unshelve.
          3:instantiate(1:=ES h).
          instantiate(1:=ES h).
          2:instantiate (1:=G1).
          2:instantiate (1:=G1).
          destruct gr. destruct o; simpl.
          { xinv tr. intros. xinv ok1. all:eauto. }
          { assert(h=#0) by xinv tr. subst h.
            clear E. assert(gr0=#None/\hr=#0) as Q by xinv ok0.
            decompose [and] Q; subst. clear Q. econstructor. }
          econstructor.
          clear E. xinv ok0. xinv ok.
        * assert (hl=ES h) by xinv ok. subst hl.
          rewrite 2 Eapp_assoc.
          econstructor.
          econstructor.
          refine (setGap tl0). exact G1. exact SG1. compute. reflexivity.
          econstructor.
          exact tr0.
          refine (setGap tr). exact G1. 2:reflexivity.
          2:eauto. 3:eauto.
          instantiate(1:=ES(ES h)).
          2:instantiate(1:=G0); econstructor.
          destruct gr. destruct o;simpl.
          { xinv tr; intros; xinv ok1. }
          { assert (h=#0) by xinv tr. subst. econstructor. }
        * assert (hl=#0) by xinv ok. subst hl.
          assert (h=#0) by xinv ok. subst h.
          clear E.
          assert (hr=#0/\gr0=#None/\hl0=#0/\gl=#None) as Q by xinv ok0.
          decompose [and] Q; subst; clear Q.
          assert (gr=#None).
          { xinv tr. intros. xinv ok1. } subst gr.
          rewrite ?Eapp_assoc.
          rewrite group3Eapp.
          econstructor.
          econstructor.
          econstructor.
          exact tl0.
          exact g2.
          econstructor.
          eauto.
          econstructor.
          exact g3.
          exact tr.
          econstructor.
          eauto.
          instantiate (1:=G1). instantiate(1:=G1). econstructor.
          eauto.
  Qed.

  Definition dFitRight{gl gll glr hl fl gr grl grr ho0 fr go gl0 gr0 f ho}
             (g : Gap)(tl : gaptree gl gll glr hl fl)(d : A)(tr : gaptree gr grl grr (ES ho0) fr)
             (t' : gaptree go gl0 gr0 ho0 f)(ok : OKNode ho gl hl gr (ES ho0))
             (s : Esorted (fl++^d++f))(e : go <> SG0)
  : delout # (Some g) ho (fl ++ ^ d ++ f).
  Proof.
    case (Gof tl). intros [[|]|] ->.
    - assert (ho=ES(ES hl)) by xinv ok. subst ho.
      elim (regapAs' t' tr). intros.
      econstructor.
      econstructor.
      refine (setGap tl). exact G0. 2:eauto.
      exact g0.
      2:eauto.
      simpl.
      instantiate (1:=ES hl).
      2:instantiate(1:=G1).
      2:econstructor.
      2:intro; discriminate_erasable.
      destruct o.
      { destruct H; subst. xinv ok; xinv t'. }
      { destruct H; subst. xinv ok. xinv t'. intros. xinv ok. }
    - assert (ho=ES hl) by xinv ok. subst ho.
      case (Gof tr). intros [[|]|] ->.
      + assert (hl=ES(ES ho0)) by xinv ok. subst hl.
        pose (tryLowering tl) as T. xinv T. intros.
        * econstructor.
          econstructor.
          exact t.
          refine (setGap t'). shelve. shelve. shelve.
          instantiate (2:=ES(ES ho0)).
          2:eauto.
          2:instantiate(1:=G1). 2:econstructor.
          2:intro; discriminate_erasable.
          Unshelve.
          4:instantiate(2:=ngap go G1); reflexivity.
          destruct go. destruct o; simpl.
          { destruct g0; xinv t'. intros. xinv ok0. }
          { xinv t'. }
        * intro W.
          eelim (dRotateRight tl d t' g W). intros ? ? X.
          econstructor. exact X. eauto.
      + assert(hl=ES ho0) by xinv ok. subst.
        econstructor.
        econstructor.
        exact tl.
        exact t'.
        instantiate (1:=ES(ES ho0)).
        2:eauto. 2:instantiate(1:=g); eauto.
        destruct go. destruct o; simpl.
        { destruct g0; xinv t'. intros. xinv ok0. }
        { xinv t'. }
      + exfalso. xinv ok.
    - assert (hl=#0) by xinv ok. subst.
      assert (ho0=#0) by xinv ok. subst.
      assert (gr=SG0) by xinv ok. subst.
      assert (ho=ES (ES #0)) by xinv ok. subst.
      assert (go=#None).
      { xinv t'. intros. xinv ok0. }
      subst.
      econstructor.
      econstructor.
      eassumption.
      eassumption.
      econstructor.
      eauto.
      econstructor. instantiate(1:=G1). intro. discriminate_erasable.
  Grab Existential Variables.
  eauto.
  Qed.
  
  Inductive delmaxResult 
  : forall (inG : EG)(inH : EN)(contents : EL), Type :=
  | NoMax : delmaxResult #None #0 []
  | MaxDeleted{gi hi f}
              (m : A)(dr : delout gi hi f) : delmaxResult gi hi (f++^m).

  Hint Constructors delmaxResult.

  Definition delmax{gi gl gr h f}(t : gaptree gi gl gr h f) : delmaxResult gi h f.
  Proof.
    Recurse t = Node g tl d tr [GoLeft|GoRight].
    xinv GoRight.
    - rewrite Eapp_nil_r.
      assert (ho=ES hl) by xinv ok. subst ho.
      econstructor.
      econstructor.
      refine (setGap tl). shelve. shelve. shelve.
      econstructor.
      Unshelve.
      instantiate (1:=ngap gl G1). intro.
      destruct gl. destruct o; simpl in H; discriminate_erasable.
      2:eauto.
    - intro dl. xinv dl.
      intros t' dr.
      rewrite group3Eapp.
      econstructor.
      xinv dr; intros; subst.
      + econstructor.
        econstructor.
        eassumption.
        eassumption.
        eassumption.
        eauto.
        eauto.
      + eapply dFitRight. all:try eassumption.
        eauto.
    Qed.
  
  Inductive deleteResult(x : A)(gi : EG)(hi :EN)
  : forall(contents : EL), Type :=
  | DelNotFound{f}{ni : ENotIn x f} : deleteResult x gi hi f
  | Deleted{fl fr}
           (dr : delout gi hi (fl++fr)) : deleteResult x gi hi (fl++^x++fr).

  Hint Constructors deleteResult.

  (* Only 7 cases, not 9, since NoneG1 and G1None are impossible. *)
  Inductive TwoGaps(g1 g2 : EG) : Set :=
  | NoneNone : g1=#None -> g2=#None -> TwoGaps g1 g2
  | G0G0     : g1=SG0   -> g2=SG0   -> TwoGaps g1 g2
  | G1G1     : g1=SG1   -> g2=SG1   -> TwoGaps g1 g2
  | NoneG0   : g1=#None -> g2=SG0   -> TwoGaps g1 g2
  | G1G0     : g1=SG1   -> g2=SG0   -> TwoGaps g1 g2
  | G0None   : g1=SG0   -> g2=#None -> TwoGaps g1 g2
  | G0G1     : g1=SG0   -> g2=SG1   -> TwoGaps g1 g2.

  Hint Constructors TwoGaps.

  Definition Gof2{g1 gl1 gr1 h1 f1 g2 gl2 gr2 h2 f2 ho}
             (t1 : gaptree g1 gl1 gr1 h1 f1)(t2 : gaptree g2 gl2 gr2 h2 f2)
             (ok : OKNode ho g1 h1 g2 h2)
  : TwoGaps g1 g2.
  Proof.
    case (Gof t1). case (Gof t2). intros.
    destruct x0, x; try destruct g0; try destruct g; subst.
    all:eauto.
    all:exfalso; xinv ok.
  Defined.

  (* Decide whether to use delmin or delmax to replace the deleted
  element *)
  Definition delMinOrMax{gl gll glr hl grl grr hr gr ho fl fr}(g : Gap)
             (tl : gaptree gl gll glr hl fl)(d : A)(tr : gaptree gr grl grr hr fr)
             (ok : OKNode ho gl hl gr hr)(s : Esorted (fl ++ ^ d ++ fr))
  : delout # (Some g) ho (fl ++ fr).
  Proof.
    case (Gof2 tl tr ok); intros; subst.
    - assert (ho=ES #0/\hl=#0/\hr=#0) by xinv ok. simplify_hyps.
      assert (fl=[]) by xinv tl. subst.
      assert (fr=[]) by xinv tr. subst.
      rewrite Eapp_nil_l.
      econstructor.
      econstructor.
      econstructor.
      intro. discriminate_erasable.
    - assert (hr=hl) by xinv ok. subst.
      assert (ho=ES hl) by xinv ok. subst.
      Call (delmin tr).
      intro X. xinv X.
      intros t' r.
      xinv r.
      + zauto.
      + intro e.
        econstructor.
        econstructor.
        refine (setGap tl). exact G0. 2:reflexivity.
        eassumption.
        simpl. instantiate(1:=ES(ES ho)).
        3:instantiate (1:=g).
        all:eauto.
        destruct go. destruct o; simpl; eauto.
        assert (g0=G1).
        { destruct g0; simplify_hyps; eauto. } subst.
        xinv t'. intros. xinv ok0.
    - assert (hr=hl) by xinv ok. subst.
      assert (ho=ES(ES hl)) by xinv ok. subst.
      Call (delmin tr).
      intro X. xinv X.
      intros t' r.
      xinv r.
      + zauto.
      + intro e.
        econstructor.
        econstructor.
        refine (setGap tl). exact G0. 2:reflexivity.
        eassumption.
        simpl. instantiate(1:=ES(ES ho)).
        3:instantiate (1:=G1).
        all:eauto.
        destruct go. destruct o; simpl; eauto.
        destruct g0. xinv t'; intros; xinv ok0.
        simplify_hyps.
    - assert (hl=#0/\hr=ES #0/\ho=ES(ES #0)) by xinv ok. simplify_hyps.
      assert (fl=[]) by xinv tl. subst.
      rewrite Eapp_nil_l.
      econstructor.
      refine (setGap tr). exact G1. 2:simpl; reflexivity.
      econstructor. intro. discriminate_erasable.
    - assert (ho=ES hr/\hr=ES hl) by xinv ok. simplify_hyps.
      Call (delmin tr).
      intro X. xinv X.
      intros t' r.
      econstructor.
      econstructor.
      eassumption.
      eassumption.
      instantiate (1:=ES(ES hl)).
      all:eauto.
      xinv r.
      intro e.
      destruct go. destruct o; subst; eauto.
      destruct g0. xinv tl; intros; xinv ok0.
      simplify_hyps.
    - assert (ho=ES hl/\hl=ES #0/\hr=#0) by xinv ok. simplify_hyps.
      assert (fr=[]) by xinv tr. subst.
      rewrite Eapp_nil_r.
      econstructor.
      refine (setGap tl). exact G1. 2:simpl; reflexivity.
      econstructor. intro. discriminate_erasable.
    - assert (hl=ES hr/\ho=ES hl) by xinv ok. simplify_hyps.
      Call (delmax tl).
      intro X. xinv X.
      rewrite Eapp_assoc.
      intros t' r.
      econstructor.
      econstructor.
      eassumption.
      eassumption.
      instantiate (1:=ES(ES hr)).
      all:eauto.
      xinv r. intro e.
      destruct go. destruct o; subst; eauto.
      destruct g0. xinv tr; intros; xinv ok0.
      simplify_hyps.
  Qed.

  Definition delete(x : A){g gl gr h f}(t : gaptree g gl gr h f) : deleteResult x g h f.
  Proof.
    Recurse t = Node g tl d tr [GoLeft|GoRight].
    Compare x d.
    - eapply Deleted.
      eapply delMinOrMax; eassumption.
    - xinv GoLeft.
      + eauto.
      + intro X. xinv X.
        intros t' r.
        rewrite ?Eapp_assoc.
        eapply Deleted.
        rewrite <- Eapp_assoc.
        xinv r; intros; subst.
        * zauto.
        * eapply dFitLeft. all:try eassumption.
          eauto.
    - xinv GoRight.
      + eauto.
      + intro X. xinv X.
        intros t' r.
        rewrite group3Eapp.
        eapply Deleted.
        rewrite ?Eapp_assoc.
        xinv r; intros; subst.
        * zauto.
        *eapply dFitRight. all:try eassumption.
         eauto.
  Qed.
End deletion.

Extract Inductive delout => "( * )" [ "(,)" ].
Set Printing Width 150.
Extraction "gaptree.ml" find insert delmin delete.
