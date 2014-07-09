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

(* A Set library built on generic trees (the Tree typeclass), which
should work with all tree varieties (AVL, Red-Black, Gap, etc.) *)

Require Import common.
Require Import tctree.
Typeclasses eauto := 9.

(* Some common tactic abbreviations: *)
Ltac ec := econstructor.
Ltac ea := eassumption.
Ltac re := reflexivity.
Ltac sh := simplify_hyps.

Context {A : Type}.
Context {ordA : Ordered A}.
Context {treeA : Tree A}.

Opaque tree.

Require Import Arith Omega natsind.

Notation EL := (##(list A)).

Definition Elength(f : EL) : EN := (lift1 (@length A)) f.

Ltac revert_all := repeat match goal with H:_|-_=> revert H end.

(* Some very nice tactics about using strong induction on EN's (erased
nats) to allow for almost-general-purpose recursion on anything
measurable with nats, erased or not.  We exploit the fact that generic
trees (typeclass Tree) provide an erased view of their flattened
contents, to which we can apply Elength to as a measure.  This also
results in very easy measure obligations to solve
(solve_recursive_measure handles them all). *)

Ltac RecursiveAll term :=
  let R:=fresh in
  let E:=fresh in
  match type of (term) with
    | EL => remember (Elength term) as R eqn:E
    | EN => remember term as R eqn:E
  end;
    move E at top; move R at top; revert_all;
    intro R; induction R as [R Recurse] using enat_xrect;
    intros; rewrite E in *; clear E R.

Ltac RecursiveOver term hyps :=
  let R:=fresh in
  let E:=fresh in
  match type of (term) with
    | EL => remember (Elength term) as R eqn:E
    | EN => remember term as R eqn:E
  end;
    move R at top; revert E; revert hyps;
    induction R as [R Recurse] using enat_xrect;
    intros; rewrite E in *; clear E R.

Tactic Notation "Recursive" constr(term) := RecursiveAll term.
Tactic Notation "Recursive" constr(term) "over" ne_hyp_list(hyps) := RecursiveOver term hyps.

Ltac solve_recursive_measure := 
  subst; clear; unerase; rewrite ?app_length; simpl; omega.

Tactic Notation "Compare" hyp(x) hyp(y) := case (compare_spec x y); intros; subst.

(* Get all Esorted terms for trees that don't have them yet. *)
Ltac Esorteds := repeat
  match goal with 
    | T : tree ?F |- _ => 
      match goal with
        | S : Esorted F |- _ => fail 1
        | _ => let s:=fresh "s" T in
               generalize(isSorted T); intro s
      end
  end.

(* Obtain is a way to "declare" the output type one wants and then try
to get it automatically, including via recursion. *)
Ltac obtain1 := match goal with H:_ |- _ => eapply H end.

Ltac obtain := trivial; try (obtain1; obtain); try solve_recursive_measure.

Tactic Notation "Obtain" constr(term) "as" simple_intropattern(i) :=
  assert term as i; [obtain|..].

Tactic Notation "Obtain" constr(term) := assert term; [obtain..].

Tactic Notation "Obtain" := obtain.

Ltac solve_esorted := Esorteds; unerase; solve_sorted.
Ltac se := solve_esorted.

Hint Extern 20 (Esorted _) => solve_esorted.

Section finding.

  (* It is possible to define find for generic trees: *)
  
  Inductive findResult(x : A)(f : EL) : Type :=
  | Found{fl fr} : f=fl++^x++fr -> findResult x f
  | NotFound{ni : ENotIn x f} : findResult x f.

  Hint Constructors findResult.

  Definition find(x : A){f}(t : tree f) : findResult x f.
  Proof.
    Recursive f over f t.
    Esorteds.
    case (break t).
    - intros ->. eauto.
    - intros fl tl d fr tr ->. Esorteds.
      Compare x d.
      + eauto.
      + Obtain (findResult x fl) as [? ? ->|ni]. all:zauto.
      + Obtain (findResult x fr) as [? ? ->|ni]. all:zauto.
  Defined.
End finding.

Section splitting.

  (* Given a pivot element, split a tree into two parts (< pivot, >
  pivot), and also return if that pivot element was found in the
  tree. *)

  Inductive splitResult(x : A)(f : EL) : Type :=
  | Split(found : bool){fx f1 f2}
         (ef : f=f1++fx++f2)
         {efx : if found then fx=^x else fx=[]}
         (t1 : tree f1)(t2 : tree f2)
         {s : Esorted (f1++^x++f2)}
         {ni : found=false -> ENotIn x (f1++f2)}
    : splitResult x f.

  (* Note that I switched to index-less Result types - mostly just
  because "case" generates nicer OCaml code than does inversion. *)
  
  Hint Constructors splitResult.
  Hint Resolve join.

  Hint Extern 10 => match goal with H: ?A = ?A ->_|-_=>specialize (H eq_refl) end.

  Definition split(x : A){f}(t : tree f) : splitResult x f.
  Proof.
    Recursive f over f t.
    Esorteds.
    case (break t).
    - intros ->.
      do 2 rewrite <-Eapp_nil_l. eapply (Split _ _ false eq_refl). all:eauto.
    - intros fl tl d fr tr ->. Esorteds.
      Compare x d.
      + eapply (Split _ _ true eq_refl). all:eauto. discriminate.
      + Obtain (splitResult x fl) as [found fx f1 f2 -> efx t1 t2 s ni].
        rewrite ?Eapp_assoc.
        eapply (Split _ _ found eq_refl).
        ea. eauto. destruct found;subst;eauto.
        destruct found;subst;eauto.
        rewrite <-Eapp_assoc.
        intros ->. subst. eauto.
      + Obtain (splitResult x fr) as [found fx f1 f2 -> efx t1 t2 s ni].
        rewrite group3Eapp.
        eapply (Split _ _ found eq_refl).
        eauto. ea. destruct found;subst;eauto. rewrite ?Eapp_assoc.
        intros ->. subst. eauto.
    Grab Existential Variables.
    all:simpl; trivial.
  Qed.

End splitting.

Definition EIn(x : A) := liftP1 (In x).

(* A bunch of lemmas that should eventually get rolled into
solvesorted, or something like it - they use the lts and slt
predicates, which really should remain local to solvesorted.  However,
they provide a very easy way to simplify sorted/In/lt goals.  Maybe
eventually turn solvesorted into a general rewrite-based solver over
sorted/In/lt/logical-connectives.  *)

Lemma ltsin2lt{a d f} : In a f -> lts f d -> lt a d.
Proof.
  revert a d.
  induction f.
  - intros. contradiction.
  - intros a0 d H H0.
    simple inversion H0; subst.
    + inversion H1.
    + inversion H2. subst.
      destruct H.
      * subst. tauto.
      * contradiction.
    + intros H1 H2 H3.
      change ([a1]++l)%list with (a1::l) in H4. inversion H4. subst.
      destruct H.
      * subst. ea.
      * apply IHf. ea. ea.
Qed.

Lemma sltin2lt{a d f} : In a f -> slt d f -> lt d a.
Proof.
  revert a d.
  induction f.
  - intros. contradiction.
  - intros a0 d H H0.
    simple inversion H0; subst.
    + inversion H2.
    + inversion H3. subst.
      destruct H.
      * subst. tauto.
      * contradiction.
    + intros H1 H2 H3.
      change ([b]++l)%list with (b::l) in H5. inversion H5. subst.
      destruct H.
      * subst. ea.
      * apply IHf. ea. 
        eapply slt_trans. ea. ea.
Qed.

Hint Resolve ltsin2lt sltin2lt.

Ltac genlts :=
  repeat match goal with 
           | I : In ?A ?F, S : slt ?B ?F |- _ => 
             match goal with 
               | L : lt B A |- _ => fail 1
               | _ => generalize (sltin2lt I S); intro
             end
           | I : In ?A ?F, S : lts ?F ?B |- _ =>
             match goal with
               | L : lt A B |- _ => fail 1
               | _ => generalize (ltsin2lt I S); intro
             end
         end.

Ltac specall a :=
  repeat match goal with | H : _ |- _ => specialize (H a) end.

Lemma in_single{T}{a b : T} : In a [b]%list <-> a=b.
Proof.
  split.
  - intro H. destruct H as [->|]; [|contradiction]. re.
  - intros ->. ec. re.
Qed.

Lemma in_nil_rw{T}{a : T} : In a nil <-> False.
Proof.
  split.
  - apply in_nil.
  - contradiction.
Qed.

Hint Extern 10 => match goal with H:lt ?X ?X |- _ => contradict H; apply irreflexivity end.

Hint Extern 10 => match goal with
                      H1:lt ?X ?Y, H2:lt ?Y ?X |- _ =>
                      exfalso; generalize (transitivity H1 H2); apply irreflexivity end.

Lemma ltsin{a f} : In a f -> lts f a -> False.
Proof.
  revert a.
  induction f.
  - intros. contradiction.
  - intros a0 H H0.
    simple inversion H0.
    + inversion H1.
    + injection H2. intros. subst.
      destruct H. subst. eauto. eauto.
    + intros H1 H2 H3. subst.
      destruct H.
      * change ([a1]++l)%list with (a1::l) in H4. injection H4. intros. subst.
        eauto.
      * change ([a1]++l)%list with (a1::l) in H4. injection H4. intros. subst.
        specialize (IHf a0 H H2). contradiction.
Qed.

Lemma sltin{a f} : In a f -> slt a f -> False.
Proof.
  revert a.
  induction f.
  - intros. contradiction.
  - intros a0 H H0.
    simple inversion H0.
    + inversion H2.
    + injection H3. intros. subst.
      destruct H. subst. eauto. eauto.
    + intros H1 H2 H3. subst.
      change ([b]++l)%list with (b::l) in H5. injection H5. intros. subst.
      destruct H.
      * subst. eauto.
      * specialize (IHf a0 H). contradict IHf. solve_sorted.
Qed.

Hint Extern 10 => match goal with H1:In ?A ?F, H2:lts ?F ?A |- _ =>
                                  exfalso; apply (ltsin H1 H2) end.

Hint Extern 10 => match goal with H1:In ?A ?F, H2:slt ?A ?F |- _ =>
                                  exfalso; apply (sltin H1 H2) end.

Lemma ltsinlts{d f1 f2} : lts f1 d -> (forall a, In a f2 -> In a f1) -> sorted f2 -> lts f2 d.
Proof.
  revert d f1.
  induction f2.
  - intros d f1 H H0 H1.
    ec.
  - intros d f1 H H0 H1.
    ec.
    + Obtain (In a f1) as H2. ec. re. eapply ltsin2lt. ea. ea.
    + eapply IHf2. ea. intros a0 H2. eapply H0. apply in_cons. ea. eapply sortedtail. ea.
    + ea.
Qed.

Lemma lts2inlts{d f1 f2 f3} : lts f1 d -> lts f2 d -> (forall a, In a f3 -> In a f1 \/ In a f2) ->
                              sorted f3 -> lts f3 d.
Proof.
  revert d f1 f2.
  induction f3.
  - intros d f1 f2 H H0 H1 H2. ec.
  - intros d f1 f2 H H0 H1 H2. ec.
    + Obtain (In a f1 \/ In a f2) as H3. ec. re. destruct H3.
      * eapply ltsin2lt. ea. ea.
      * eapply ltsin2lt. ea. ea.
    + eapply IHf3. exact H. exact H0. intros a0 H3. apply H1. apply in_cons. ea. eapply sortedtail. ea.
    + ea.
Qed.

Lemma sltinslt{d f1 f2} : slt d f1 -> (forall a, In a f2 -> In a f1) -> sorted f2 -> slt d f2.
Proof.
  revert d f1.
  induction f2.
  - intros d f1 H H0 H1.
    ec.
  - intros d f1 H H0 H1.
    ec.
    + Obtain (In a f1) as H2. ec. re. eapply sltin2lt. ea. ea.
    + eapply sorted2slt. ea.
    + ea.
Qed.

Lemma slt2inslt{d f1 f2 f3} : slt d f1 -> slt d f2 -> (forall a, In a f3 -> In a f1 \/ In a f2) ->
                              sorted f3 -> slt d f3.
Proof.
  revert d f1 f2.
  induction f3.
  - intros d f1 f2 H H0 H1 H2. ec.
  - intros d f1 f2 H H0 H1 H2. ec.
    + Obtain (In a f1 \/ In a f2) as H3. ec. re. destruct H3.
      * eapply sltin2lt. ea. ea.
      * eapply sltin2lt. ea. ea.
    + eapply sorted2slt. ea.
    + ea.
Qed.

(* Unlift should eventually be part of unerase - but it can't be
automated currently because of a Coq bug (3410) which causes failed
setoid_rewrites to die in an uncatchable way.  So it has to be applied
only to hypotheses where it won't fail.  A possible workaround is to
use Notation instead of Definition for all lifted predicates (lik EIn
and ENotIn) so that something like "context[liftP1]" can be used to
determine if a hypothesis has something to be unlifted before applying
setoid_rewrite there. *)

Lemma unliftP1{T}{P : T -> Prop}{x : T} : (liftP1 P) #x <-> P x.
Proof.
  split.
  - intros. unerase. ea.
  - intros. unerase. ea.
Qed.

Require Coq.Setoids.Setoid.

Ltac unlift H := repeat setoid_rewrite unliftP1 in H.

(* If 3410 isn't fixed soon, maybe use something like this in unerase:
*)

Ltac unlift_all_work_around_3410 :=
  repeat match goal with 
             H:?T|-_ =>
             match eval lazy delta - [liftP1] in T with
                 context[liftP1] => unlift H
             end
         end;
  repeat setoid_rewrite unliftP1.

(* Some automation for solving goals featuring formulas of In's *)

Ltac rewrite_ins :=
  repeat setoid_rewrite in_app_iff;
  repeat setoid_rewrite in_single;
  repeat setoid_rewrite in_nil_rw.

Ltac siors := match goal with
               | |- lts _ _ => eapply ltsinlts
               | |- slt _ _ => eapply sltinslt
             end;
             [ |intros ? I;unlift_all_work_around_3410;
                 match goal with H:_|-_ => eapply H in I; intuition eauto end| ];ea.

Ltac siands := match goal with
               | |- lts _ _ => eapply lts2inlts
               | |- slt _ _ => eapply slt2inslt
             end;
            [ | |intros ? I; unlift_all_work_around_3410;
                 match goal with H:_|-_ => eapply H;[exact I|..] end|..];ea.

Ltac si := 
  try unerase;
  unlift_all_work_around_3410;
  rewrite_ins;
  solve_sorted;
  genlts;
  intuition (subst;auto);
  congruence.

Ltac debool := repeat match goal with H:bool |- _ => destruct H;subst end.

Ltac sia := let a:=fresh in intro a; specall a; debool; si.

Section union.

  Inductive unionResult(f1 f2 : EL) : Type :=
  | UnionResult{f}(t : tree f)
               {u : forall a, EIn a f <-> EIn a f1 \/ EIn a f2}
    : unionResult f1 f2.

  Definition union{f1}(t1 : tree f1){f2}(t2 : tree f2) : unionResult f1 f2.
  Proof.
    Recursive (f1++f2).
    Esorteds.
    case (break t1).
    - intros ->. ec. exact t2. si.
    - intros fl tl d fr tr ->.
      case (split d t2). intros found fx f2l f2r -> efx t2l t2r s ni.
      Obtain (unionResult fl f2l) as [f t u].
      Obtain (unionResult fr f2r) as [f0 t0 u0].
      assert (Esorted(f++^d++f0)) by (Esorteds; se; siands).
      ec. eapply (join t d t0). sia.
  Grab Existential Variables.
      all:eauto.
  Qed.

End union.

Section merging.

  (* Merge is like union, but reqires that the two trees be sorted
  with respect to each other. *)
  
  Hint Resolve join.

  Definition delete_free_delmin{f}(t : tree f) : delminResult tree f.
  Proof.
    Recursive f.
    Esorteds.
    case (break t).
    - intros ->. ec. re.
    - intros fl tl d fr tr ->.
      Obtain (delminResult tree fl) as dr.
      case dr.
      + intros ->. rewrite Eapp_nil_l.
        eapply DelminNode. 2:re. ea.
      + intros m f' t0 ->.
        rewrite ?Eapp_assoc.
        eapply DelminNode. 2:re.
        eauto.
  Qed.

  (* Merge is just a join using delmin to get the "middle" datum.  It
  is the only function in this sets library that would use any variety
  of delete.  Alternatively, as shown above, we can write a version of
  delmin which itself doesn't use any variety of delete.  Not using
  delete has the benefit for gaptrees of not adding any non-AVL nodes
  to the tree - which keeps the worst-case search time at 1.44logN
  instead of 2logN.  However, the tradeoff is that the above
  delete_free_delmin will do extra rotations - as it re-joins the tree
  it breaks apart - it essentially mimmics the AVL delmin.  Both
  delmins are O(logN), so it's just the constant factors that would
  differ.

  Of course, if we're using gaptrees instead of AVL trees, then it is
  probably because we want the higher delete performance.  So, just
  use the tree-provided delmin instead of the above one:  *)

  Notation delmin_for_merge := delmin.
  
  Definition merge
             {f1}(t1 : tree f1){f2}(t2 : tree f2){s : Esorted(f1++f2)} : tree (f1++f2).
  Proof.
    Esorteds.
    case (delmin_for_merge t2).
    - intros ->. eauto.
    - intros m fr tr ->. eauto.
  Qed.

End merging.

Section intersection.

  Inductive intersectResult(f1 f2 : EL) : Type :=
  | IntersectResult{f}(t : tree f)
               {u : forall a, EIn a f <-> EIn a f1 /\ EIn a f2}
    : intersectResult f1 f2.

  Definition intersection{f1}(t1 : tree f1){f2}(t2 : tree f2) : intersectResult f1 f2.
  Proof.
    Recursive (f1++f2).
    Esorteds.
    case (break t1).
    - intros ->. ec. apply leaf. si.
    - intros fl tl d fr tr ->.
      case (split d t2). intros found fx f2l f2r -> efx t2l t2r s ni.
      Obtain (intersectResult fl f2l) as [f t u].
      Obtain (intersectResult fr f2r) as [f0 t0 u0].
      assert(Esorted (f++^d++f0)) by (Esorteds; se; siors).
      destruct found.
      + subst fx. ec. eapply (join t d t0). sia.
      + subst fx. ec. eapply (merge t t0). sia.
  Grab Existential Variables.
        all:eauto.
  Qed.

End intersection.

Section setdifference.

  Inductive setdiffResult(f1 f2 : EL) : Type :=
  | SetDiffResult{f}(t : tree f)
               {u : forall a, EIn a f <-> EIn a f1 /\ ~EIn a f2}
    : setdiffResult f1 f2.

  Definition setdifference{f1}(t1 : tree f1){f2}(t2 : tree f2) : setdiffResult f1 f2.
  Proof.
    Recursive (f1++f2).
    Esorteds.
    case (break t1).
    - intros ->. ec. apply leaf. si.
    - intros fl tl d fr tr ->.
      case (split d t2). intros found fx f2l f2r -> efx t2l t2r s ni.
      Obtain (setdiffResult fl f2l) as [f t u].
      Obtain (setdiffResult fr f2r) as [f0 t0 u0].
      assert(Esorted (f++^d++f0)) by (Esorteds; se; siors).
      destruct found.
      + subst fx. ec. eapply (merge t t0). sia.
      + subst fx. ec. eapply (join t d t0). sia.
  Grab Existential Variables.
        all:eauto.
  Qed.

End setdifference.

Section filtering.

  Inductive filterResult(filt : A -> bool)(f : EL) : Type :=
  | Filtered{fo}(t : tree fo)
            {u : forall a, EIn a fo <-> EIn a f /\ (filt a=true)}
    : filterResult filt f.

  Definition filter(filt : A -> bool){f}(t : tree f) : filterResult filt f.
  Proof.
    Recursive f over f t.
    Esorteds.
    case (break t).
    - intros ->. ec. apply leaf. si.
    - intros fl tl d fr tr ->.
      Obtain (filterResult filt fl) as [flo tlo ulo].
      Obtain (filterResult filt fr) as [fro tro uro].
      assert (Esorted (flo++^d++fro)) by (Esorteds; se; siors).
      case_eq (filt d).
      + intro FT. ec. eapply (join tlo d tro). sia.
      + intro FF. ec. eapply (merge tlo tro). sia.
  Grab Existential Variables.
        all:eauto.
  Qed.

End filtering.

Section partitioning.

  Inductive partitionResult(filt : A -> bool)(f : EL) : Type :=
  | Partitioned{fy}(ty : tree fy){fn}(tn : tree fn)
            {uy : forall a, EIn a fy <-> EIn a f /\ filt a=true}
            {un : forall a, EIn a fn <-> EIn a f /\ filt a=false}
    : partitionResult filt f.

  Definition partition(filt : A -> bool){f}(t : tree f) : partitionResult filt f.
  Proof.
    Recursive f over f t.
    Esorteds.
    case (break t).
    - intros ->. ec. apply leaf. apply leaf. all:si.
    - intros fl tl d fr tr ->.
      Obtain (partitionResult filt fl) as [fl1 tl1 fl0 tl0 ul1 ul0].
      Obtain (partitionResult filt fr) as [fr1 tr1 fr0 tr0 ur1 ur0].
      assert (Esorted(fl1++^d++fr1)) by (Esorteds; se; siors).
      assert (Esorted(fl0++^d++fr0)) by (Esorteds; se; siors).
      case_eq (filt d).
      + intro FT. ec. eapply (join tl1 d tr1). eapply (merge tl0 tr0). all:sia.
      + intro FF. ec. eapply (merge tl1 tr1). eapply (join tl0 d tr0). all:sia.
  Grab Existential Variables.
        all:eauto.
Qed.

End partitioning.

Set Printing Width 80.
Require Import ExtrOcamlBasic.
Extract Inlined Constant eq_nat_dec => "(=)".
Extract Inlined Constant lt_dec => "(<)".
Extract Inlined Constant plus => "(+)".

(* Well-founded induction in Coq produces strange-looking local
functions if enat_xrect is inlined - so turn off its inlining to make
the code more readable: *)
Extraction NoInline enat_xrect.

Extraction "sets.ml" find delete_free_delmin union intersection setdifference filter partition.
