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

(*

A slight reformularization of gaptree.v.  Move the gap bits to the
parents, because that might simplify things enough to make proofs more
automatic.

Well, maybe only for insertion, mostly.  It's hitting some Coq bugs
with respect to automation - specifically, 3381, but also 3378 - which
are making it hard to get automation to work in cases where it has
done so before, as in avl.v and redblack.v.

*)

Require Import common.
Typeclasses eauto := 9.

(* Some common tactic abbreviations: *)
Ltac ec := econstructor.
Ltac ea := eassumption.
Ltac re := reflexivity.
Ltac sh := simplify_hyps.

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

Definition gS := fun (g : Gap) =>
match g with
| G1 => ES
| G0 => fun n => n
end.

Ltac gsplit g := destruct g; simpl in *; sh.

Lemma gS0{g n}(e : #0 = gS g n) : n=#0 /\ g=G0.
Proof.
  gsplit g. tauto.
Qed.

Hint Extern 5 => match goal with H: ?n=S ?n |- _ =>
                                 contradict (n_Sn n H) end.
Hint Extern 5 => match goal with H: ?n=ES ?n |- _ =>
                                 exfalso; unerase; contradict (n_Sn n H) end.
Hint Extern 5 => match goal with H: S ?n=?n |- _ =>
                                 symmetry in H; contradict (n_Sn n H) end.
Hint Extern 5 => match goal with H: ES ?n=?n |- _ => 
                                 symmetry in H; exfalso; unerase; contradict (n_Sn n H) end.

Lemma ES0{n}(e : #0 = ES n) : False.
Proof. discriminate_erasable. Qed.

Hint Extern 5 => match goal with H: #0=ES _ |- _ =>
                                 exfalso; contradict(ES0 H) end.
Hint Extern 5 => match goal with H: ES _ = #0 |- _ =>
                                 exfalso; symmetry in H; contradict (ES0 H) end.

Lemma gSn{g n}(e : n = gS g n) : g=G0.
Proof.
  destruct g; simpl in e; eauto.
Qed.

Lemma gSS{g n}(e : ES n = gS g n) : g=G1.
Proof.
  destruct g; simpl in e; eauto.
Qed.

Ltac dogs :=
  repeat match goal with
           | H : _ = gS G0 _ |- _ => simpl gS in H; sh
           | H : gS G0 _ = _ |- _ => simpl gS in H; sh
           | H : _ = gS G1 _ |- _ => simpl gS in H; sh
           | H : gS G1 _ = _ |- _ => simpl gS in H; sh
           | H : _ = gS _ _ |- _ => first [apply gS0 in H|apply gSn in H|apply gSS in H]; sh
           | H : gS _ _ = _ |- _ => symmetry in H;
                                    first [apply gS0 in H|apply gSn in H|apply gSS in H]; sh
         end.

Hint Extern 2 (_ = gS ?G _) => (unify G G0 + unify G G1); simpl gS.
Hint Extern 2 (gS ?G _ = _) => (unify G G0 + unify G G1); simpl gS.
Hint Extern 10 (gS ?X _ = gS ?Y _) =>
(re + (unify X G0; unify Y G1) + (unify X G1; unify Y G0)); solve[simpl;re].
Hint Extern 0 (ES _ = ES _) => f_equal.

Lemma sgsg{g1 g2 : Gap}(e : #(Some g1)<>#(Some g2)) : g1<>g2.
Proof. intro. subst. contradict e. re. Qed.

Lemma nG1{g}(e : g<>G1) : g=G0.
Proof. destruct g; sh. re. Qed.

Lemma nG0{g}(e : g<>G0) : g=G1.
Proof. destruct g; sh. re. Qed.

Lemma nesym{T}{x y : T}(ne : x<>y) : y<>x.
Proof. intro. subst. contradict ne. re. Qed.

Hint Extern 5 => match goal with H : #(Some ?G1)<>#(Some ?G2) |- _ =>
                                 apply sgsg in H end.

Hint Extern 5 => match goal with H : _<>G1 |- _ => apply nG1 in H; sh end.
Hint Extern 5 => match goal with H : _<>G0 |- _ => apply nG0 in H; sh end.
Hint Extern 5 => match goal with H : G1<>_ |- _ => apply nesym in H; apply nG1 in H; sh end.
Hint Extern 5 => match goal with H : G0<>_ |- _ => apply nesym in H; apply nG0 in H; sh end.
Hint Extern 2 (_ \/ _) => (ea + left + right).
Hint Extern 10 (~(_=_)) => intro; sh.

(* The gaptree type exposes the gaps of each child as indices in the
parent to make the "gapee" and "avlish" props easier to work with. *)

Inductive gaptree : forall (logap rogap : EG)(height : EN)(contents : EL), Type :=
| Leaf : gaptree #None #None #0 []
| Node{ho hl fl hr fr gll glr grl grr}
      (gl : Gap)(tl : gaptree gll glr hl fl)(d : A)(gr : Gap)(tr : gaptree grl grr hr fr)
      {okl : ho=gS gl hl}{okr : ho=gS gr hr}{x : hl=#0 -> hr=#0 -> ho=#0}
      {s : Esorted (fl++^d++fr)} (*contents are properly sorted*)
  : gaptree #(Some gl) #(Some gr) (ES ho) (fl++^d++fr).

Hint Constructors gaptree.

(************************************************************************)

(*some prettifying tactic notation*)

Tactic Notation 
  "Recurse" hyp(t) "=" "Node" ident(gl) ident(tl) ident(d) ident(gr) ident(tr)
  "[" ident(xl) "|" ident(xr) "]"
  := induction t as [ |? ? ? ? ? ? ? ? ? gl tl xl d gr tr xr]; [zauto| ].

Tactic Notation "Compare" hyp(x) hyp(y) := case (compare_spec x y); intros; subst.

Ltac Call x := let Q := fresh in assert (Q:=x); xinv Q.

(************************************************************************)

Section Find.

  Inductive findResult(x : A) : forall (contents : EL), Type :=
  | Found{fl fr} : findResult x (fl++^x++fr)
  | NotFound{f}{ni : ENotIn x f} : findResult x f.

  Hint Constructors findResult.

  Definition find(x : A){gl gr h f}(t : gaptree gl gr h f) : findResult x f.
  Proof.
    Recurse t = Node gl tl d gr tr [GoLeft|GoRight].
    Compare x d.
    - (*x=d*) eauto.
    - (*x<d*) xinv GoLeft. all:zauto.
    - (*x>d*) xinv GoRight. all:zauto.
  Qed.

End Find.

(************************************************************************)

(*Only Esorted and lt props are needed when solving Esorted props - so
convert all rbtree hyps into Esorted hyps prior to solving Esorted
(sorted, when unerased) props. *)

Definition Sof{gl gr h f}(t : gaptree gl gr h f) : Esorted f.
Proof. destruct t. all:unerase. all:eauto. Qed.

Ltac SofAll :=
  repeat match goal with
             H : gaptree _ _ _ _ |- _ => apply Sof in H
         end.

Ltac solve_esorted := SofAll; unerase; solve_sorted.
Ltac se := solve_esorted.

Hint Extern 20 (Esorted _) => solve_esorted.

(************************************************************************)

Lemma leaf1{gl gr f}(t : gaptree gl gr #0 f) : gl=#None /\ gr=#None /\ f=[].
 Proof. xinv t. Qed.

Ltac leaves :=
  match goal with 
    | H:gaptree _ _ #0 _ |- _ => apply leaf1 in H; simplify_hyps
  end.

Hint Extern 1 => leaves.

Definition isLeaf{gl gr h f}(t : gaptree gl gr h f) : {h=#0} + {h<>#0}.
Proof. xinv t. intros. right. intro. simplify_hyps. Qed.

Inductive gapnode(h : EN)(f : EL) : Type :=
| Gapnode{gl gr}(t : gaptree gl gr h f) : gapnode h f.

Hint Constructors gapnode.

Section insertion.

  (* Gapee: one child has (or can have) a gap while the other doesn't.  *)
  Notation gapee gl gr h := (h=#0 \/ gl<>gr) (only parsing).

  Inductive ires(gl gr : EG) : EN -> EN ->  Set :=
  | ISameH{h} : ires gl gr h h
  | Higher{h} : gapee gl gr h -> ires gl gr h (ES h).

  Inductive insertResult(x : A)
  : forall(inH : EN)(contents : EL), Type :=
  | FoundByInsert{h fl fr} : insertResult x h (fl++^x++fr)
  | Inserted{gl gr hi ho fl fr}
      (t : gaptree gl gr ho (fl++^x++fr))(i : ires gl gr hi ho)
      : insertResult x hi (fl++fr).

  Hint Extern 1 (insertResult _ #0 []) =>
    rewrite <- Eapp_nil_l; eapply Inserted; [econstructor|].

  Hint Constructors insertResult ires.
  Hint Extern 100 (ires _ _ _ _) => match goal with |- context[gS G0 _] => simpl end.
  Hint Extern 100 (ires _ _ _ _) => match goal with |- context[gS G1 _] => simpl end.

  Definition iRotateRight{gll glr h fl fr grl grr}
             (tl : gaptree gll glr (ES (ES h)) fl)(d : A)(tr : gaptree grl grr h fr)
             (s : Esorted (fl++^d++fr))(H : gll <> glr)
  : gapnode (ES (ES h)) (fl++ ^ d ++ fr).
  Proof.
    xinv tl. intros tll tlr **.
    gsplit gr.
    - zauto.
    - xinv tlr. intros. zauto.
  Qed.

  Definition ign2ins{hi fl x fr}(i : gapnode hi (fl++^x++fr))
  : insertResult x hi (fl++fr).
  Proof.
    destruct i. eauto.
  Defined.

  Hint Resolve ign2ins iRotateRight.

  Definition iFitLeft{hl fl0 fr0 gll glr x gl gr grl grr hr fr}
             (t : gaptree gll glr (ES hl) (fl0 ++ ^ x ++ fr0))
             (d : A)(tr : gaptree grl grr hr fr)(H : lt x d)(okr : gS gl hl = gS gr hr)
             (s : Esorted ((fl0 ++ fr0) ++ ^ d ++ fr))(H0 : gapee gll glr hl)
  : insertResult x (ES (gS gl hl)) ((fl0 ++ fr0) ++ ^ d ++ fr).
  Proof.
    gsplit gl.
    - zauto.
    - gsplit gr. all:zauto.
  Qed.

  Hint Extern 100 (_=_) => match goal with G : Gap |- _ => gsplit G end.

  Definition iRotateLeft{gll glr h fl grl grr fr}
             (tl : gaptree gll glr h fl)(d : A)(tr : gaptree grl grr (ES (ES h)) fr)
             (s : Esorted(fl++^d++fr))(H : grl<>grr)
  : gapnode (ES (ES h)) (fl++^d++fr).
  Proof.
    xinv tr. intros trl trr **.
    gsplit gl.
    - zauto.
    - xinv trl. intros.
      rewrite ?Eapp_assoc. rewrite group3Eapp. zauto.
  Qed.

  Hint Resolve iRotateLeft.

  Definition iFitRight{gll glr hl fl grl grr hr fr0 x fr1 gl gr}
             (tl : gaptree gll glr hl fl)(d: A)(tr : gaptree grl grr (ES hr)(fr0++^x++fr1))
             (s : Esorted (fl++^d++fr0++fr1))(H : lt d x)
             (H0 : gapee grl grr hr)(okl : gS gl hl = gS gr hr)
  : insertResult x (ES (gS gl hl)) ((fl++^d++fr0)++fr1).
  Proof.
    gsplit gr.
    - zauto.
    - gsplit gl. all:zauto.
  Qed.

  Hint Resolve iFitLeft iFitRight.

  Definition insert(x : A){gl gr h f}(t : gaptree gl gr h f)
  : insertResult x h f.
  Proof.
    Recurse t = Node gl tl d gr tr [GoLeft|GoRight].
    - Compare x d.
      + (*x=d*) eauto.
      + (*x<d*)
        xinv GoLeft.
        * zauto.
        * intros t i. xinv i. all:zauto.
      + (*x>d*)
        xinv GoRight.
        * zauto.
        * intros t i. xinv i. 
          { zauto. }
          { intro. rewrite group3Eapp. eauto. }
  Qed.

End insertion.

Section deletion.

  Inductive dres: forall (hi ho : EN), Set :=
  | DSameH{h} : dres h h
  | Lower{h} : dres (ES h) h.

  Hint Constructors dres.
  
  Inductive delout (*intermediate result for delmin and delete*)
  : forall (inH : EN)(contents : EL), Type :=
  | Delout {hi ho f}(t: gapnode ho f){dr: dres hi ho} : delout hi f.

  Hint Constructors delout.

  (* "AVLish" is the condition of being AVL-like - at least one child *)
  (* doesn't have a gap.*)
  Definition avlish(gl gr : EG) := gl=SG0 \/ gr=SG0.

  Inductive tryLowerResult: EG -> EG -> EN -> EL -> Type :=
  | lowered{h f}(t : gaptree SG0 SG0 (ES h) f) : tryLowerResult SG1 SG1 (ES (ES h)) f
  | lowerFailed{gl gr h f}: avlish gl gr -> tryLowerResult gl gr h f.

  Hint Constructors tryLowerResult.

  Hint Unfold avlish.

  (* If a node's children both have gaps, the node can be lowered by 1. *)
  Definition tryLowering{gl gr h f}(t : gaptree gl gr (ES h) f)
  : tryLowerResult gl gr (ES h) f.
  Proof.
    generalize_eqs t.
    case t.
    - intros H. discriminate_erasable.
    - intros ho hl fl hr fr gll glr grl grr gl0 tl d gr0 tr okl okr x s H.
      gsplit gl0.
      + gsplit gr0.
        * eauto.
        * eauto.
      + eauto.
  Qed.

  Definition gflip(g : Gap) :=
    match g with G0=>G1|G1=>G0 end.

  Definition dRotateLeft{gl0 gr0 ho fl grl grr fr}
             (tl : gaptree gl0 gr0 ho fl)(d : A)(tr : gaptree grl grr (ES (ES ho)) fr)
             (s : Esorted (fl ++ ^ d ++ fr))(H : avlish grl grr)
  : gapnode (ES (ES (ES ho))) (fl ++ ^ d ++ fr).
  Proof.
    unfold avlish in H.
    generalize_eqs tr.
    destruct tr as [|ho0 hl fl0 hr fr0 gll glr grl0 grr0 gl trl d0 gr trr ok1 ok2 x sr] eqn:E; clear E.
    { intro. sh. }
    intro.
    gsplit gr.
    - assert (gl=G0) by (sh;re). subst.
      simpl gS in ok2. subst.
      xinv trl. intros tl0 tr0 okl okr x0 s0. subst.
      rewrite ?Eapp_assoc. rewrite group3Eapp. ec. ec. ec. ea. ea. re. zauto. zauto. se. ec.
      ea. ea. re. zauto. intros. subst. leaves. dogs. re. se.
      instantiate (1:=G1). simpl. re. instantiate(1:=G1). simpl. f_equal. f_equal. ea.
      simpl gS. intros. zauto. se.
    - rewrite group3Eapp. ec. ec. ec. ea. ea. 5:ea. 6:instantiate (1:=G1);zauto.
      4:se. 6:se. instantiate(1:=gflip gl). 2:zauto. 2:zauto.
      2:instantiate (1:=gl). 2:gsplit gl; re. 2:intros;sh.
      gsplit gl; re.
  Qed.

  Inductive delminResult 
  : forall (inH : EN)(contents : EL), Type :=
  | NoMin : delminResult #0 []
  | MinDeleted{hi f}(m : A)(dr : delout hi f) : delminResult hi (^m++f).

  Hint Constructors delminResult.

  Definition dFitLeft{gl0 gr0 ho f grl grr hr fr gl gr}
             (tl : gaptree gl0 gr0 ho f)(d : A)(tr : gaptree grl grr hr fr)
             (s : Esorted (f ++ ^ d ++ fr))(ok : gS gl (ES ho) = gS gr hr)(H : hr <> # 0)
  : delout (ES (gS gl (ES ho))) (f ++ ^ d ++ fr).
  Proof.
    gsplit gl.
    - assert (hr=ES (gS (gflip gr) ho)) by (gsplit gr; re). subst.
      gsplit gr.
      + ec. ec. ec. ea. ea. re. zauto. zauto. se. ec.
      + Call (tryLowering tr).
        * intro t. clear tr.
          ec. ec. ec. ea. ea. re. zauto. zauto. se. ec. 
        * intro A. ec. 2:eapply DSameH. eapply dRotateLeft; ea.
    - ec. 2:ec. ec. ec. ea. ea. instantiate (1:=G1). re. ea.
      intros. subst. sh. se.
  Qed.

  Definition delmin{gl gr h f}(t : gaptree gl gr h f) : delminResult h f.
  Proof.
    Recurse t = Node gl tl d gr tr [GoLeft|GoRight].
    xinv GoLeft. 
    - rewrite Eapp_nil_l.
      ec. ec. ec. ea. rewrite okl. 
      assert (gr=G0).
      { gsplit gr. gsplit gl. unerase. injection okl. intros ->.
        specialize (x eq_refl eq_refl). unerase_hyp x. discriminate x. re. } subst.
      simpl in okl. subst. ec.
    - intro dl. xinv dl. rewrite ?Eapp_assoc.
      intros [? ? t] dr. xinv dr.
      + eauto.
      + case (isLeaf tr); intros; subst.
        * leaves. 
          assert (ho=#0/\gl=G0/\gr=G1). 
          { clear s. gsplit gl; gsplit gr. unerase. eauto. } sh. leaves. simpl gS.
          ec. ec. ec. ec. ec. ec. re. 2:zauto. re. se. ec.
        * ec. eapply dFitLeft. ea. ea. se. ea. ea.
  Qed.

  Definition dRotateRight{gll glr ho gl0 gr0 f fl}
             (tl : gaptree gll glr (ES (ES ho)) fl)(d : A)(tr : gaptree gl0 gr0 ho f)
             (s : Esorted (fl ++ ^ d ++ f))(H : avlish gll glr)
  : gapnode (ES (ES (ES ho))) (fl ++ ^ d ++ f).
  Proof.
    unfold avlish in H.
    generalize_eqs tl.
    destruct tl as [|ho0 hl fl0 hr fr0 gll glr grl0 grr0 gl tll d0 gr tlr ok1 ok2 x sr] eqn:E; clear E.
    { intro. sh. }
    intro.
    gsplit gl.
    - assert (gr=G0) by (sh;re). subst.
      simpl gS in ok2. subst.
      xinv tlr. intros tl0 tr0 okl okr x0 s0. subst.
      rewrite ?Eapp_assoc. rewrite group3Eapp. ec. ec. ec. ea. ea. re. zauto. zauto. se. ec.
      ea. ea. re. zauto. intros. subst. leaves. dogs. re. se.
      instantiate (1:=G1). simpl. re. instantiate(1:=G1). simpl. f_equal. f_equal. ea.
      simpl gS. intros. zauto. se.
    - rewrite ?Eapp_assoc. ec. ec. ea. ec. ea. ea. 5:instantiate(1:=G1);zauto.
      4:se. 6:se. zauto. instantiate(1:=gflip gr). 2:zauto.
      2:instantiate(1:=gr). 2:gsplit gr;re. 2:intros;sh.
      gsplit gr; re.
  Qed.

  Definition dFitRight{gll glr hl fl gl0 gr0 ho f gl gr}
             (tl : gaptree gll glr hl fl)(d : A)(tr : gaptree gl0 gr0 ho f)
             (s : Esorted (fl ++ ^ d ++ f))(okr : gS gl hl = gS gr (ES ho))(H : hl <> # 0)
  : delout (ES (gS gl hl)) (fl ++ ^ d ++ f).
  Proof.
    gsplit gr.
    - assert (hl=ES (gS (gflip gl) ho)) by (gsplit gl; re). subst.
      gsplit gl.
      + ec. ec. ec. ea. ea. re. zauto. zauto. se. ec.
      + Call (tryLowering tl).
        * intro t. clear tl.
          ec. ec. ec. ea. ea. re. zauto. zauto. se. ec.
        * intro A. ec. 2:eapply DSameH. eapply dRotateRight; ea.
    - ec. 2:ec. ec. ec. ea. ea. re. instantiate (1:=G1). ea.
      intros. subst. sh. se.
  Qed.

  Inductive delmaxResult 
  : forall (inH : EN)(contents : EL), Type :=
  | NoMax : delmaxResult #0 []
  | MaxDeleted{hi f}(m : A)(dr : delout hi f) : delmaxResult hi (f++^m).

  Hint Constructors delmaxResult.

  Definition delmax{gl gr h f}(t : gaptree gl gr h f) : delmaxResult h f.
  Proof.
    Recurse t = Node gl tl d gr tr [GoLeft|GoRight].
    xinv GoRight.
    - rewrite Eapp_nil_r.
      ec. ec. ec. ea. rewrite okr.
      assert (gl=G0).
      { clear s. gsplit gl. gsplit gr. unerase. injection okr. intros ->.
        specialize (x eq_refl eq_refl). unerase_hyp x. discriminate x. re. } subst.
      simpl in okr. subst. ec.
    - intro dl. xinv dl. rewrite group3Eapp.
      intros [? ? t] dr. xinv dr.
      + eauto.
      + case (isLeaf tl); intros; subst.
        * leaves.
          assert (ho=#0/\gr=G0/\gl=G1).
          { clear s. gsplit gl; gsplit gr. unerase. injection okr. eauto. } sh. leaves. simpl gS.
          ec. ec. ec. ec. ec. ec. re. 2:zauto. re. se. ec.
        * ec. eapply dFitRight. ea. ea. se. ea. ea.
  Qed.

  Definition delMinOrMax{gll glr hl fl grl grr hr fr gl gr}
             (tl : gaptree gll glr hl fl)(d : A)(tr : gaptree grl grr hr fr)
             (s : Esorted (fl ++ ^ d ++ fr))(ok : gS gl hl = gS gr hr)
             (x0 : hl = # 0 -> hr = # 0 -> gS gl hl = # 0)
  : delout (ES (gS gl hl)) (fl ++ fr).
  Proof.
    gsplit gl; gsplit gr.
    - Call (delmin tr).
      { specialize (x0 eq_refl eq_refl). sh. }
      intro X. xinv X. intros [? ? t'] r. xinv r.
      + ec. ec. ec. ea. ea. 3:ea. instantiate (1:=G1). zauto. instantiate (1:=G1). zauto. se. ec.
      + ec. ec. ec. ea. ea. 5:eapply Lower. zauto. instantiate(1:=G1). re. zauto. se.
    - Call (delmin tr). intro X. xinv X. intros [? ? t'] r. xinv r.
      + ec. ec. ec. ea. ea. instantiate (1:=G1). re. zauto. zauto. se. ec.
      + ec. ec. ec. ea. ea. instantiate (1:=G0). re. zauto. zauto. se. ec.
    - Call (delmax tl). intro X. xinv X. intros [? ? t'] r. xinv r.
      + rewrite ?Eapp_assoc. ec. ec. ec. ea. ea. re. zauto. zauto. se. ec.
      + rewrite ?Eapp_assoc. ec. ec. ec. ea. ea. re. re. zauto. se. ec.
    - Call (delmin tr).
      { rewrite Eapp_nil_r. ec. leaves. leaves. ec. ec. ec. }
      intro X. xinv X. intros [? ? t'] r. xinv r.
      + ec. ec. ec. ea. ea. re. re. zauto. se. ec.
      + ec. ec. ec. ea. ea. re. zauto. zauto. se. ec.
  Qed.

  Inductive deleteResult(x : A)(hi :EN)
  : forall(contents : EL), Type :=
  | DelNotFound{f}{ni : ENotIn x f} : deleteResult x hi f
  | Deleted{fl fr}
           (dr : delout hi (fl++fr)) : deleteResult x hi (fl++^x++fr).

  Hint Constructors deleteResult.

  Definition delete(x : A){gl gr h f}(t : gaptree gl gr h f) : deleteResult x h f.
  Proof.
    Recurse t = Node gl tl d gr tr [GoLeft|GoRight].
    Compare x d.
    - eapply Deleted.
      eapply delMinOrMax.  all:ea.
    - xinv GoLeft.
      + eauto.
      + intro X. xinv X. intros [? ? t'] r.
        rewrite ?Eapp_assoc.
        eapply Deleted.
        rewrite <- Eapp_assoc.
        xinv r; intros; subst.
        * zauto.
        * case (isLeaf tr); intros; subst.
          { leaves.
            assert (ho=#0/\gl=G0/\gr=G1).
            { clear s. gsplit gl; gsplit gr. unerase. eauto. } sh. leaves. simpl gS.
            ec. ec. ec. rewrite H3. ec. ec. re. 2:zauto. re. se. ec. }
          { eapply dFitLeft. all:try ea. se. }
    - xinv GoRight.
      + eauto.
      + intro X. xinv X. intros [? ? t'] r.
        rewrite group3Eapp.
        eapply Deleted.
        rewrite ?Eapp_assoc.
        xinv r; intros; subst.
        * zauto.
        * case (isLeaf tl); intros; subst.
          { leaves.
            assert (ho=#0/\gr=G0/\gl=G1).
            { clear s. gsplit gr; gsplit gl. unerase. injection okr. eauto. } sh. leaves. simpl gS.
            ec. ec. ec. ec. rewrite H3. ec. re. 2:zauto. re. se. ec. }
          { eapply dFitRight. all:try ea. se. }
  Qed.

End deletion.

Require Import Arith Omega Min Max Psatz natsind.

Definition unS(n : nat){pn}(H : ES pn=#n) : {n' : nat | pn=#n'}.
Proof.
  destruct n.
  - sh. 
  - exists n. change (#(S n)) with (ES #n) in H. sh. re.
Defined.

Definition g2h{ph g h}(H : ES (gS g h) = #ph) : {h' : nat | #h'=h}.
Proof.
  destruct g; simpl in H.
  - exists (pred (pred ph)). unerase. omega.
  - exists (pred ph). unerase. omega.
Qed.

Ltac ses := match goal with
                |- context[#(S ?X)] => change (#(S X)) with (ES #X) end.

Section joining.
  
  Inductive jres(gl gr: EG)(hil hih : EN) : EN -> Set :=
  | JSameH : jres gl gr hil hih hih
  | JHigher : (hil<>hih -> gl<>gr) -> jres gl gr hil hih (ES hih).

  Inductive joinResult(hil hih : EN)(f : EL) : Type :=
  | JoinResult(h : nat){gl gr} : gaptree gl gr #h f -> jres gl gr hil hih #h -> joinResult hil hih f.

  Hint Constructors joinResult jres.

  Definition joinle(h1 : nat){g1l g1r f1}(t1 : gaptree g1l g1r # h1 f1)(d : A)
             (h2: nat){g2l g2r f2}(t2 : gaptree g2l g2r # h2 f2)
             (s : Esorted (f1 ++ ^ d ++ f2))(H : h1 <= h2)
  : joinResult #h1 #h2 (f1++^d++f2).
  Proof.
    generalize_eqs_vars t2.
    induction t2 eqn:E.
    - intros. sh.
      assert (h1=0) by omega. subst. leaves.
      ec. instantiate (1:=1). ses. ec. ec. ec.
      eauto. eauto. tauto. ea. ec. tauto.
    - intros. clear E IHg2. subst ho.
      case (eq_nat_dec h1 h2); intros.
      + subst.
        ec. instantiate (1:=S h2). ses. ec. ea. ea. eauto. eauto. tauto. ea. ec. tauto.
      + assert (h1<h2) by omega. clear H H1.
        case (eq_nat_dec (S h1) h2); intros.
        * subst. clear H2.
          ec. instantiate (1:=S(S h1)). ses. ec. ea. ea. 
          instantiate(1:=G1). re. rewrite H0. eauto. rewrite H0. tauto. se. ec. eauto.
        * assert (S h1<h2) by omega. clear H H2.
          destruct gl eqn:E.
          { simpl gS in *.
            elim (unS h2 H0). intros h2m1 Hh2m1. elim (unS h2m1 Hh2m1). intros h2m2 Hh2m2.
            eelim (IHg1 g1 eq_refl t1 h2m2 _ _ Hh2m2). intros h ? ? g j. clear IHg1.
            simple inversion j.
            - rewrite <-H in *.
              rewrite group3Eapp. ec. instantiate (1:=h2). rewrite <-H0. ec. ea. ea.
              instantiate (1:=gl). subst. simpl. re. ea. intros. rewrite H2 in g.
              simple inversion g. exfalso. unerase. contradict H7. apply app_cons_not_nil.
              discriminate_erasable. se. ec.
            - rewrite <-H2 in *.
              rewrite group3Eapp. ec. instantiate (1:=h2). rewrite <-H0. ec. ea. ea.
              instantiate (1:=G0). simpl. unerase. omega. ea. eauto. se. ec. }
          { simpl gS in *.
            elim (unS h2 H0). intros h2m1 Hh2m1.
            eelim (IHg1 g1 eq_refl t1 h2m1 _ _ Hh2m1). intros h ? ? g j. clear IHg1.
            simple inversion j.
            - rewrite <-H in *.
              rewrite group3Eapp. ec. instantiate (1:=h2). rewrite <-H0. ec. ea. ea.
              instantiate (1:=G0). simpl. ea. ea. rewrite Hh2m1. tauto. se. ec.
            - intro X. rewrite <-H2 in *.
              rewrite <-Hh2m1 in *.
              destruct gr.
              + simpl gS in *. subst.
                elim (iRotateRight g d0 g2). intros. rewrite group3Eapp.
                ec. instantiate (1:=h). rewrite <-H2. ea. 
                rewrite <-H2. rewrite H0. ec. se. apply X. unerase. omega.
              + simpl gS in *. subst.
                rewrite group3Eapp. ec. instantiate (1:=S h2). ses. ec. ea. ea.
                eauto. instantiate (1:=G1). simpl. eauto. eauto. se. ec. intro. eauto. }
  Grab Existential Variables.
  { se. }
  { unerase; omega. }
  { se. }
  { unerase; omega. }
  Qed.

  Definition joinge(h1 : nat){g1l g1r f1}(t1 : gaptree g1l g1r# h1 f1)(d : A)
             (h2: nat){g2l g2r f2}(t2 : gaptree g2l g2r # h2 f2)
             (s : Esorted (f1 ++ ^ d ++ f2))(H : h1 >= h2)
  : joinResult #h2 #h1 (f1++^d++f2).
  Proof.
    generalize_eqs_vars t1.
    induction t1 eqn:E.
    - intros. sh.
      assert (h2=0) by omega. subst. leaves.
      ec. instantiate (1:=1). change (#1) with (ES #0). ec. ec. ec.
      eauto. eauto. tauto. ea. ec. tauto.
    - intros. clear E. clear IHg1. subst ho.
      case (eq_nat_dec h1 h2); intros.
      + subst.
        ec. instantiate (1:=S h2). change (#(S h2)) with (ES #h2). ec. ea. ea. eauto. eauto. tauto. 
        ea. ec. tauto.
      + assert (h1>h2) by omega. clear H H1.
        case (eq_nat_dec (S h2) h1); intros.
        * subst. clear H2.
          ec. instantiate (1:=S(S h2)). change (#(S(S h2))) with (ES(ES #h2)). ec. ea. ea. 
          rewrite H0. eauto. instantiate(1:=G1). re. rewrite H0. tauto. se. ec. eauto.
        * assert (S h2<h1) by omega. clear H H2.
          rewrite okr in H0.
          destruct gr eqn:E.
          { simpl gS in *.
            elim (unS h1 H0). intros h1m1 Hh1m1. elim (unS h1m1 Hh1m1). intros h1m2 Hh1m2.
            eelim (IHg2 g2 eq_refl h1m2 t2 _ _ Hh1m2). intros h ? ? g j. clear IHg2.
            simple inversion j.
            - rewrite <-H in *.
              rewrite ?Eapp_assoc. ec. instantiate (1:=h1). rewrite <-H0. ec. ea. ea.
              symmetry in okr. exact okr.
              instantiate (1:=gr). subst. simpl. re. intros. rewrite H3 in g.
              simple inversion g. exfalso. unerase. contradict H7. apply app_cons_not_nil.
              discriminate_erasable. se. ec.
            - rewrite <-H2 in *.
              rewrite ?Eapp_assoc. ec. instantiate (1:=h1). rewrite <-H0. ec. ea. ea.
              symmetry in okr. exact okr.
              instantiate (1:=G0). simpl. unerase. omega. eauto. se. ec. }
          { simpl gS in *.
            elim (unS h1 H0). intros h1m1 Hh1m1.
            eelim (IHg2 g2 eq_refl h1m1 t2 _ _ Hh1m1). intros h ? ? g j. clear IHg2.
            simple inversion j.
            - rewrite <-H in *.
              rewrite ?Eapp_assoc. ec. instantiate (1:=h1). rewrite <-H0. ec. ea. ea.
              symmetry in okr. exact okr.
              instantiate (1:=G0). simpl. ea. rewrite Hh1m1. tauto. se. ec.
            - intro X. rewrite <-H2 in *.
              rewrite <-Hh1m1 in *.
              destruct gl.
              + simpl gS in *. subst.
                elim (iRotateLeft g1 d0 g). intros. rewrite ?Eapp_assoc.
                ec. instantiate (1:=h). rewrite <-H2. ea. 
                rewrite <-H2. rewrite H0. ec. se. apply X. unerase. omega.
              + simpl gS in *. subst.
                rewrite ?Eapp_assoc. ec. instantiate (1:=S h1). ses. ec. ea. ea.
                instantiate (1:=G1). simpl. eauto. eauto. eauto. se. ec. intro. eauto. }
  Grab Existential Variables.
  { se. }
  { unerase; omega. }
  { se. }
  { unerase; omega. }
  Qed.
  
  Definition join(h1 : nat){g1l g1r f1}(t1 : gaptree g1l g1r# h1 f1)(d : A)
             (h2: nat){g2l g2r f2}(t2 : gaptree g2l g2r # h2 f2)
             (s : Esorted (f1 ++ ^ d ++ f2))
  : joinResult #(min h1 h2) #(max h1 h2) (f1++^d++f2).
  Proof.
    case (lt_dec h1 h2); intro.
    - assert (min h1 h2=h1) as H0.
      { apply min_l. omega. }
      rewrite H0.
      assert (max h1 h2=h2) as H1.
      { apply max_r. omega. }
      rewrite H1.
      eapply joinle. ea. ea. ea. omega.
    - assert (min h1 h2=h2) as H0.
      { apply min_r. omega. }
      rewrite H0.
      assert (max h1 h2=h1) as H1.
      { apply max_l. omega. }
      rewrite H1.
      eapply joinge. ea. ea. ea. omega.
  Qed.

End joining.

Require tctree.

(* Glue logic to instantiate the Tree typeclass using gaptrees *)

Inductive gaphtree(f : EL) : Type := (* gaptree with height of root *)
Gaphtree(h : nat){gl gr}(t : gaptree gl gr #h f) : gaphtree f.

Instance gaphtree_tree : tctree.Tree A := { tree := gaphtree }.
{ ec. apply Leaf. }
{ intros f t. destruct t. xinv t. eauto. }
{ intros f t. destruct t. generalize_eqs t. destruct t eqn:E.
  - ec. re.
  - intros H. subst.
    elim (g2h H). intros hl' <-. generalize H. rewrite okr. intro Hr. elim (g2h Hr). intros hr' <-.
    eapply tctree.BreakNode. 3:re. ec. ea. ec. ea. }
{ intros x f t. destruct t.
  Call (insert x t).
  - ec. re.
  - intros t0 i. simple inversion i.
    + subst h0 ho. eapply tctree.Inserted. ec. ea. re.
    + intro. subst h0 ho. eapply tctree.Inserted. ec. ea. re. }
{ intros fl tl d fr tr s.
  destruct tl, tr.
  elim (join h t d h0 t0 s). intros h1 gl1 gr1 g j.
  ec. ea. }
{ intros f t.
  destruct t.
  Call (delmin t).
  - ec. re.
  - intros dr.
    xinv dr. 
    intros t0 dr0.
    xinv dr0.
    + destruct t0. eapply tctree.DelminNode. ec. 2:re. ea.
    + destruct t0. elim (unS _ H). intros ho' ->.
      eapply tctree.DelminNode. ec. 2:re. ea. }
{ intros f t.
  destruct t.
  Call (delmax t).
  - ec. re.
  - intros dr.
    xinv dr. 
    intros t0 dr0.
    xinv dr0.
    + destruct t0. eapply tctree.DelmaxNode. ec. 2:re. ea.
    + destruct t0. elim (unS _ H). intros ho' ->.
      eapply tctree.DelmaxNode. ec. 2:re. ea. }
{ intros x f t.
  destruct t.
  Call (delete x t).
  - ec. ea.
  - intros dr.
    xinv dr.
    intros t0 dr0.
    xinv dr0.
    + destruct t0. eapply tctree.Deleted. ec. 2:re. ea.
    + destruct t0. elim (unS _ H). intros ho' ->.
      eapply tctree.Deleted. ec. 2:re. ea. }
Defined.

Set Printing Width 114.
Require Import ExtrOcamlBasic.
Extraction Inline ign2ins.
Extraction Implicit iFitLeft [x].
Extraction Implicit iFitRight [x].
Extract Inductive delout => "( * )" [ "(,)" ].
Extract Inlined Constant eq_nat_dec => "(=)".
Extract Inlined Constant lt_dec => "(<)".
Extract Inlined Constant plus => "(+)".

Extraction "gaptreeb.ml" find insert delmin delmax delete join gaphtree_tree.

