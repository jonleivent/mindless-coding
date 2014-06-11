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

Hint Extern 1 (_ \/ _) => (left + right).

Hint Extern 1 (~(_ = _)) => intro; simplify_hyps.

Lemma OKNode1{h g hl hr}(ok : OKNode h g hl g hr) :  hl=hr.
Proof. xinv ok. Qed.

Lemma OKNode2{h hl gr hr}(ok : OKNode h SG0 hl gr hr) : h=ES hl (*/\ hl<>#0*).
Proof. xinv ok. all:eauto. Qed. 

Lemma OKNode3{h hl gr hr}(ok : OKNode h SG1 hl gr hr) : h=ES(ES hl) (*/\ hl<>#0*).
Proof. xinv ok. all:eauto. Qed.

Lemma OKNode4{h hl gl hr}(ok : OKNode h gl hl SG0 hr) : h=ES hr (*/\ hr<>#0*).
Proof. xinv ok. all:eauto. Qed.

Lemma OKNode5{h hl gl hr}(ok : OKNode h gl hl SG1 hr) : h=ES(ES hr) (*/\ hr<>#0*).
Proof. xinv ok. all:eauto. Qed.

Lemma OKNode6{h hl hr}(ok : OKNode h #None hl #None hr) : h=ES #0 /\ hl=#0 /\ hr=#0.
Proof. xinv ok. Qed.

Lemma OKNode7{h gl gr hr}(ok : OKNode h gl #0 gr hr) : gl=#None.
Proof. xinv ok. Qed.

Lemma OKNode8{h gl gr hl}(ok : OKNode h gl hl gr #0) : gr=#None.
Proof. xinv ok. Qed.

Lemma OKNode9{h hl gr hr}(ok : OKNode h #None hl gr hr) : hl=#0.
Proof. xinv ok. Qed.

Lemma OKNode10{h gl hl hr}(ok : OKNode h gl hl #None hr) : hr=#0.
Proof. xinv ok. Qed.

Lemma OKNode11{h gl gr hr}(ok : OKNode h gl #0 gr (ES hr))
: hr=#0 /\ gr=SG0 /\ gl=#None /\ h=ES (ES #0).
Proof. xinv ok. Qed.

Lemma OKNode12{h gl gr hl}(ok : OKNode h gl (ES hl) gr #0)
: hl=#0 /\ gl=SG0 /\ gr=#None /\ h=ES (ES #0).
Proof. xinv ok. Qed.

Lemma OKNode13{h gl gr hr}(ok : OKNode (ES (ES h)) gl #0 gr hr) : h=#0 /\ gl=#None.
Proof. xinv ok. Qed.

Lemma OKNode14{h gl gr hl}(ok : OKNode (ES (ES h)) gl hl gr #0) : h=#0 /\ gr=#None.
Proof. xinv ok. Qed.

Lemma OKNode15{h hl hr}(ok : OKNode h SG0 hl # None hr) : h=ES (ES #0) /\ hl=ES #0 /\ hr=#0.
Proof. xinv ok. Qed.

Lemma OKNode16{h hl hr}(ok : OKNode h #None hl SG0 hr) : h=ES (ES #0) /\ hr=ES #0 /\ hl=#0.
Proof. xinv ok. Qed.

Lemma OKNode17{hl hr gl gr}(ok : OKNode (ES #0) gl hl gr hr)
: gl=#None /\ gr=#None /\ hl=#0 /\ hr=#0.
Proof. xinv ok. Qed.

Lemma OKNode18{h gr hr}(ok : OKNode h # None # 0 gr hr) : h=ES hr.
Proof. xinv ok. Qed.

Lemma OKNode19{h gl hl}(ok : OKNode h gl hl #None #0) : h=ES hl.
Proof. xinv ok. Qed.

Ltac xpose t := generalize t; intros.

Ltac autoOK := 
  match goal with H:OKNode _ _ _ _ _ |- _ =>
                  progress
                    ((xpose (OKNode1 H)
                     +xpose (OKNode2 H)
                     +xpose (OKNode3 H)
                     +xpose (OKNode4 H)
                     +xpose (OKNode5 H)
                     +xpose (OKNode6 H)
                     +xpose (OKNode7 H)
                     +xpose (OKNode8 H)
                     +xpose (OKNode9 H)
                     +xpose (OKNode10 H)
                     +xpose (OKNode11 H)
                     +xpose (OKNode12 H)
                     +xpose (OKNode13 H)
                     +xpose (OKNode14 H)
                     +xpose (OKNode15 H)
                     +xpose (OKNode16 H)
                     +xpose (OKNode17 H)
                     +xpose (OKNode18 H)
                     +xpose (OKNode19 H)
                     ); simplify_hyps) end.

Hint Extern 100 (OKNode _ _ _ _ _) =>
match goal with H : (OKNode _ _ _ _ _) |- _ =>  xinv H end.

(* The gaptree type exposes the gaps of each child as indices in the
parent to make the "gapee" and "avlish" props easier to work with. *)

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

Lemma leaf2{gl gr h f}(t : gaptree #None gl gr h f) : gl=#None /\ gr=#None /\ h=#0 /\ f=[].
Proof.
  xinv t.
Qed.

Ltac leaves :=
  match goal with 
    | H:gaptree _ _ _ #0 _ |- _ => apply leaf1 in H; simplify_hyps
    | H:gaptree #None _ _ _ _ |- _ => apply leaf2 in H; simplify_hyps
  end.

Hint Extern 1 => leaves.

(* Simplify gaps and heights as much as possible. *)
Ltac gh := repeat (leaves || autoOK).

Lemma OKNode20{h gl hl gr hr}(ok : OKNode h gl hl gr hr) : exists h', h=ES h'.
Proof. xinv ok; eexists; reflexivity. Qed.

Lemma OKNode21{h g hl gr hr}(ok : OKNode h #(Some g) hl gr hr) : exists hl', hl=ES hl'.
Proof. xinv ok; eexists; reflexivity. Qed.

Lemma OKNode22{h gl hl g hr}(ok : OKNode h gl hl #(Some g) hr) : exists hr', hr=ES hr'.
Proof. xinv ok; eexists; reflexivity. Qed.

Lemma nodeh{g gl gr h f}(t : gaptree #(Some g) gl gr h f) : exists h', h=ES h'.
Proof. xinv t. intros. eapply OKNode20. eassumption. Qed.

Ltac es h := 
  match goal with 
    | t : gaptree #(Some _) _ _ h _ |- _ => generalize (nodeh t)
    | ok : OKNode h _ _ _ _ |- _ => generalize (OKNode20 ok)
    | ok : OKNode _ #(Some _) h _ _ |- _ => generalize (OKNode21 ok)
    | ok : OKNode _ _ _ #(Some _) h |- _ => generalize (OKNode22 ok)
  end; intros [? ->].

(************************************************************************)

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

  Inductive RegapR(g gi gl gr : EG)(h : EN)(f : EL) : Type :=
  | regapR{go} : gaptree go gl gr h f -> gi=#None/\go=#None\/gi<>#None/\go=g
                 -> RegapR g gi gl gr h f.

  Definition regapAs{g h h' gi gl gr gl' gr' f f'}
             (t : gaptree gi gl gr h f)(ast : gaptree g gl' gr' (ES h') f')
  : RegapR g gi gl gr h f.
  Proof.
    case (Gof ast). intros [g0|] ->.
    - econstructor.
      eapply setGap. eassumption. reflexivity.
      destruct gi as [[|]]; simpl.
      + right. split; eauto.
      + tauto.
    - eauto.
  Qed.
  
  Definition Gofis{g gl gr h f}
    (t : gaptree g gl gr h f)(isg : Gap) : {g = #(Some isg)} + {g <> #(Some isg)}.
  Proof.
    destruct isg; case (Gof t); intros [[|]|] ->. all:eauto.
  Qed.

  Inductive gapnode(g : EG)(h : EN)(f : EL) : Type :=
  | Gapnode{gl gr}(t : gaptree g gl gr h f) : gapnode g h f.

End gapping.

Hint Constructors gapnode.

Hint Extern 1 (#(Some ?G) = ngap _ ?V) => is_evar V; instantiate (1:=G).

Hint Extern 0 (gaptree _ _ _ _ _) => eassumption.

(* Some common tactic abbreviations: *)
Ltac ec := econstructor.
Ltac ea := eassumption.
Ltac se := solve_esorted.
Ltac re := reflexivity.
Ltac sg := eapply setGap.
Ltac sh := simplify_hyps.

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
    destruct tl2 as [ |? ? ? ? ? ? ? ? ? ? ? [|] tl2l d1 tl2r ok0 s0] eqn:E; clear E; gh.
    - ec.
      rewrite ?Eapp_assoc.
      ec. ea. ec. ec. ec. ec. se. ec. se.
    - rewrite 2 Eapp_assoc.
      ec. ec. ea. ec. sg. ea. re. sg. ea. re.
      instantiate(1:=G0). instantiate(1:=G0). instantiate (1:=ES ho). es ho. 
      destruct g as [[|]]; simpl. ec. gh. se. instantiate (1:=G0). xinv ok; ec. se.
    - rewrite ?Eapp_assoc.
      rewrite group3Eapp.
      ec. ec. ec. sg. ea. re. ea.
      instantiate (2:=ES h). instantiate (1:=G0). destruct gll as [[|]]; simpl.
      xinv ok. xinv ok0; ec. gh. ec. ec. se. ec. ea. sg. ea. re.
      instantiate (2:=ES h). instantiate (1:=G0). destruct g as [[|]]; simpl. es h.
      xinv ok0; ec. gh. ec. ec. se. ec. se.
  Qed.

  Definition rotateLeft{h fl g gll glr grl grr fr}
             (tl : gaptree g gll glr h fl)(d : A)(tr : gaptree SG0 grl grr (ES (ES h)) fr)
             (gg: gapee grl grr)(go : Gap)(s : Esorted (fl++^d++fr))
  : gapnode #(Some go) (ES (ES h)) (fl++^d++fr).
  Proof.
    xinv tr. intros tr1 tr2 ok sr.
    unfold gapee in gg.
    destruct tr1 as [ |? ? ? ? ? ? ? ? ? ? ? [|] tr2l d1 tr2r ok0 s0] eqn:E; clear E; gh.
    - ec.
      rewrite group3Eapp.
      ec. ec. ec. ec. ec. se. ea. ec. se.
    - rewrite group3Eapp.
      ec. ec. ec. sg. ea. re. sg. ea. re.
      instantiate (1:=G0). instantiate(1:=G0). instantiate (1:=ES ho). es ho.
      destruct g as [[|]]; simpl. ec. gh. se. ea. instantiate (1:=G0). xinv ok; ec. se.
    - rewrite ?Eapp_assoc.
      rewrite group3Eapp.
      ec. ec. ec. sg. ea. re. ea.
      instantiate (2:=ES h). instantiate (1:=G0). destruct g as [[|]]; simpl. es h. xinv ok0; ec.
      gh. ec. se. ec. ea. sg. ea. re.
      instantiate (2:=ES h). instantiate (1:=G0). destruct grr as [[|]]; simpl. xinv ok.
      xinv ok0; ec. gh. ec. se. ec. se.
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
    case (Gofis tl G0); intro; subst; gh.
    - case (Gofis tr G0); intro; subst.
      + gh. ec. rewrite group3Eapp. ec. ea. sg. ea. re.
        instantiate (1:=G1). simpl. instantiate (1:=ES(ES hr)). es hr. ec.
        se. ec. re. simpl. eauto.
      + assert (hl=ES hr) by xinv ok. subst.
        eelim (rotateRight t d tr H1 c). intros. zauto. se.
    - destruct tr eqn:E; clear E.
      + gh. ec. rewrite group3Eapp. ec. ea. ec. xinv ok. ec. se. ec. re. eauto.
      + ec. rewrite group3Eapp. ec. ea. ea. instantiate (1:=ho). xinv ok. se. ec. re.
  Qed.

  Definition iFitRight{gl gll glr hl fl gr grl grr hr fl0 fr0 gl0 gr0 ho x c}
             (tl : gaptree gl gll glr hl fl)(d : A)
             (tr : gaptree gr grl grr hr (fl0 ++ fr0))
             (t : gaptree SG0 gl0 gr0 (ES hr) (fl0 ++ ^ x ++ fr0))
             (ok : OKNode ho gl hl gr hr)(H : lt d x)(H1 : gapee gl0 gr0)
             (s : Esorted (fl ++ ^ d ++ fl0 ++ fr0))
  : insertResult x # (Some c) ho ((fl ++ ^ d ++ fl0) ++ fr0).
  Proof.
    case (Gofis tr G0); intro; subst; gh.
    - case (Gofis tl G0); intro; subst.
      + gh. ec. rewrite ?Eapp_assoc. ec. sg. ea. re. ea.
        instantiate (1:=G1). simpl. instantiate (1:=ES (ES hr)). es hr. ec.
        se. ec. re. simpl. eauto.
      + assert (hr=ES hl) by xinv ok. subst. 
        eelim (rotateLeft tl d t H1 c). intros. zauto. se.
    - destruct tl eqn:E; clear E.
      + gh. ec. rewrite ?Eapp_assoc. ec. ec. ea. xinv ok. ec. se. ec. re. eauto.
      + ec. rewrite ?Eapp_assoc. rewrite group3Eapp. ec. ea. ea. instantiate (1:=ho). xinv ok.
        se. ec. re.
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
          xinv i; intros; sh.
          { zauto. }
          { eapply iFitLeft; ea. }
      + (*x>d*)
        xinv GoRight.
        * zauto.
        * intros t' i.
          rewrite group3Eapp.
          xinv i; intros; sh.
          { zauto. }
          { eapply iFitRight; ea. }
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
    case (Gofis tl G1); intro; subst.
    - case (Gofis tr G1); intro; subst.
      + ec. ec. sg. ea. re. sg. ea. re. xinv ok. se.
      + ec. unfold avlish. right. xinv ok.
    - ec. unfold avlish. xinv ok.
  Qed.

  Definition dRotateLeft{gl gll glr grl grr h fl fr}
             (tl : gaptree gl gll glr h fl)(d : A)(tr : gaptree SG0 grl grr (ES (ES h)) fr)
             (go : Gap)(H : avlish grl grr){s : Esorted (fl++^d++fr)}
  : gapnode #(Some go) (ES (ES (ES h))) (fl ++ ^ d ++ fr).
  Proof.
    xinv tr. intros tl0 tr0 ok sr.
    unfold avlish in H.
    destruct tl0 as [ |? ? ? ? ? ? ? ? ? ? ? g0 tl0l d1 tl0r ok0 s0] eqn:E; clear E.
    - assert (grr=SG0) by (sh; re). subst grr. gh.
      rewrite group3Eapp.
      ec. ec. ec. ec. ec. ec. se. sg. ea. re. ec. se.
    - case (Gofis tr0 G0); intro; subst; gh.
      + rewrite group3Eapp.
        ec. ec. ec. sg. ea. re. ea.
        instantiate (1:=G1). instantiate (1:=ES(ES h)). destruct gl as [[|]]; simpl. es h.
        xinv ok. gh. ec. xinv ok. se. sg. ea. re. ec. se.
      + rewrite ?Eapp_assoc.
        rewrite group3Eapp.
        ec. ec. ec. sg. ea. re. ea.
        instantiate (1:=G0). instantiate (1:=ES hr). destruct gl as [[|]]; simpl. es h. xinv ok.
        xinv ok0. gh. xinv ok. se. ec. ea. sg. ea. re.
        instantiate (1:=G0). instantiate(1:=ES hr). xinv ok. xinv ok0. gh. ec. se. xinv ok. se.
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
    case (Gofis tr G0); intro; subst; gh.
    - case (Gofis tl G1); intro; subst.
      + gh. pose (tryLowering tr) as T. xinv T.
        * intro t.
          ec. ec. ea. ea.
          instantiate (1:=ES (ES ho0)).
          destruct go as [[[|]|]]. es ho0. ec. sh. gh. ec. se. ec.
          instantiate (1:=G1). eauto.
        * intro W.
          eelim (dRotateLeft t' d tr g W). intros. eauto.
      + ec. ec. ea. ea. instantiate (1:=ES hr). xinv ok. destruct go as [[[|]|]]. es ho0. ec.
        sh. gh. ec. se. ec.
    - elim (regapAs t' tl). intros go0 t ?.
      ec. ec. exact t. sg. ea. re.
      instantiate (1:=G0). instantiate (1:=ES hr). sh. gh. xinv ok. xinv ok. simpl. es ho0. ec.
      gh. se. instantiate (1:=G1). assert (ho=ES(ES hr)) by xinv ok. subst. ec. eauto.
  Grab Existential Variables.
  se.
  Qed.

  Definition delmin{gi gl gr h f}(t : gaptree gi gl gr h f) : delminResult gi h f.
  Proof.
    Recurse t = Node g tl d tr [GoLeft|GoRight].
    xinv GoLeft. 
    - rewrite Eapp_nil_l.
      gh. ec. ec. sg. ea. re. ec.
      instantiate (1:=G1). intro. 
      destruct gr as [[|]]; simpl in H; discriminate_erasable.
    - intro dl. xinv dl.
      intros t' dr.
      rewrite ?Eapp_assoc.
      ec.
      xinv dr; intros; subst.
      + eauto.
      + eapply dFitLeft. all:try ea. se.
  Qed.

  Definition dRotateRight{gr gll glr grl grr h fl fr}
             (tl : gaptree SG0 gll glr (ES (ES h)) fl)(d : A)(tr : gaptree gr grl grr h fr)
             (go : Gap)(H : avlish gll glr){s : Esorted (fl++^d++fr)}
  : gapnode #(Some go) (ES (ES (ES h))) (fl ++ ^ d ++ fr).
  Proof.
    xinv tl. intros tl0 tr0 ok sl.
    unfold avlish in H.
    destruct tr0 as [ |? ? ? ? ? ? ? ? ? ? ? g0 tr0l d1 tr0r ok0 s0] eqn:E; clear E.
    - assert (gll=SG0) by (sh; re). subst gll. gh.
      rewrite ?Eapp_assoc.
      ec. ec. sg. ea. re. ec. ec. ec. ec. se. ec. se.
    - case (Gofis tl0 G0); intro; subst; gh.
      + rewrite 2 Eapp_assoc.
        ec. ec. sg. ea. re. ec. ea. sg. ea. re.
        instantiate (1:=G1). instantiate(1:=ES(ES h)). destruct gr as [[|]]; simpl.
        es h. xinv ok. gh. xinv ok. ec. se. ec. se.
      + rewrite ?Eapp_assoc.
        rewrite group3Eapp.
        ec. ec. ec. sg. ea. re. ea.
        instantiate (1:=G0). instantiate (1:=ES hl). xinv ok; simpl. xinv ok0. gh. ec.
        se. ec. ea. sg. ea. re.
        instantiate (1:=G0). instantiate(1:=ES h). destruct gr as [[|]]; simpl. es h. xinv ok.
        xinv ok0. gh. ec. se. xinv ok. se.
  Qed.
  
  Definition dFitRight{gl gll glr hl fl gr grl grr ho0 fr go gl0 gr0 f ho}
             (g : Gap)(tl : gaptree gl gll glr hl fl)(d : A)(tr : gaptree gr grl grr (ES ho0) fr)
             (t' : gaptree go gl0 gr0 ho0 f)(ok : OKNode ho gl hl gr (ES ho0))
             (s : Esorted (fl++^d++f))(e : go <> SG0)
  : delout # (Some g) ho (fl ++ ^ d ++ f).
  Proof.
    case (Gofis tl G0); intro; subst; gh.
    - case (Gofis tr G1); intro; subst.
      + gh. pose (tryLowering tl) as T. xinv T.
        * intro t.
          ec. ec. ea. ea.
          instantiate (1:=ES(ES ho0)).
          destruct go as [[[|]|]]; simpl. es ho0. ec. gh. gh. ec. se. ec.
          instantiate(1:=G1). eauto.
        * intro W.
          eelim (dRotateRight tl d t' g W). intros. eauto.
      + ec. ec. ea. ea.
        instantiate (1:=ES hl). destruct go as [[[|]|]]. xinv ok. es ho0. ec. sh. gh. xinv ok. se. ec.
    - elim (regapAs t' tr). intros go0 t ?.
      ec. ec. sg. ea. re. ea.
      instantiate (1:=G0). instantiate (1:=ES hl). sh; simpl.
      gh. xinv ok. destruct gr as [[|]]. xinv ok. es ho0. ec.
      gh. xinv ok. se. assert (ho=ES(ES hl)) by xinv ok. subst. ec.
      instantiate(1:=G1). eauto.
  Grab Existential Variables.
  se.
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
      gh. ec. ec. sg. ea. re. ec.
      instantiate (1:=G1). destruct gl as [[[|]|]]; intro; sh.
    - intro dl. xinv dl.
      intros t' dr.
      rewrite group3Eapp.
      ec.
      xinv dr; intros; subst.
      + eauto.
      + eapply dFitRight. all:try ea. se.
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
    case (Gof t1). case (Gof t2). intros [g2'|] -> [g1'|] ->.
    destruct g1', g2'; eauto.
    assert (g2'=G0) by xinv ok. subst. eauto.
    assert (g1'=G0) by xinv ok. subst. eauto.
    eauto.
    all:exfalso; xinv ok.
  Defined.

  (* Decide whether to use delmin or delmax to replace the deleted
  element *)
  Definition delMinOrMax{gl gll glr hl grl grr hr gr ho fl fr}(g : Gap)
             (tl : gaptree gl gll glr hl fl)(d : A)(tr : gaptree gr grl grr hr fr)
             (ok : OKNode ho gl hl gr hr)(s : Esorted (fl ++ ^ d ++ fr))
  : delout # (Some g) ho (fl ++ fr).
  Proof.
    case (Gof2 tl tr ok); intros; subst; gh.
    - eauto.
    - Call (delmin tr). intro X. xinv X. intros t' r. xinv r.
      + zauto.
      + intro e.
        ec. ec. ea. ea.
        instantiate(1:=ES(ES ho)). destruct go as [[[|]|]]; simpl.
        es ho. ec. sh. gh. ec. se. ec.
    - Call (delmin tr). intro X. xinv X. intros t' r. xinv r.
      + zauto.
      + intro e.
        ec. ec. sg. ea. re. ea.
        instantiate (1:=G0). simpl. instantiate(1:=ES(ES ho)).
        destruct go as [[[|]|]]; simpl. es ho. ec. sh. gh. ec. se. ec.
        instantiate (1:=G1). eauto.
    - rewrite Eapp_nil_l.
      ec. sg. ea. re. ec.
      instantiate (1:=G1). eauto.
    - Call (delmin tr). intro X. xinv X. intros t' r.
      ec. ec. ea. ea.
      instantiate (1:=ES(ES hl)). xinv r. intro e. destruct go as [[[|]|]]; subst.
      es hl. ec. sh. gh. se. ec.
    - rewrite Eapp_nil_r.
      ec. sg. ea. re. ec. instantiate (1:=G1). eauto.
    - Call (delmax tl). intro X. xinv X. intros t' r.
      rewrite Eapp_assoc.
      ec. ec. ea. ea.
      instantiate (1:=ES(ES hr)). es hr. xinv r. intro e. destruct go as [[[|]|]]; subst.
      ec. sh. gh. se. ec.
  Qed.

  Definition delete(x : A){g gl gr h f}(t : gaptree g gl gr h f) : deleteResult x g h f.
  Proof.
    Recurse t = Node g tl d tr [GoLeft|GoRight].
    Compare x d.
    - eapply Deleted.
      eapply delMinOrMax; ea.
    - xinv GoLeft.
      + eauto.
      + intro X. xinv X. intros t' r.
        rewrite ?Eapp_assoc.
        eapply Deleted.
        rewrite <- Eapp_assoc.
        xinv r; intros; subst.
        * zauto.
        * eapply dFitLeft. all:try ea. se.
    - xinv GoRight.
      + eauto.
      + intro X. xinv X. intros t' r.
        rewrite group3Eapp.
        eapply Deleted.
        rewrite ?Eapp_assoc.
        xinv r; intros; subst.
        * zauto.
        * eapply dFitRight. all:try ea. se.
  Qed.
End deletion.

Extract Inductive delout => "( * )" [ "(,)" ].
Extract Inductive sumbool => "bool" [ "true" "false" ].
Extraction Implicit iFitLeft [x].
Extraction Implicit iFitRight [x].
Set Printing Width 110.
Extraction "gaptree.ml" find insert delmin delete.
