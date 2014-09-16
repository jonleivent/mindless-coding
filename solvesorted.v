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

(* A crude "decision" procedure over certain kinds of sorted lists -
those with singleton deliminters between sublists, such as
sorted(p++[x]++q++[y]++r).  It has some limited ability to work even
in cases without such singleton delimiters.  One advantage is that
associativity is disposed of by decomposing sorted lists into pairs
over the "slt" and "lts" relations (singleton-lt and lt-singleton,
respectively).  If needed, it could probably be made into a full
decision procedure by noting that a term such as sorted(p++q) can be
converted into sorted(p) and sorted(p++[x]++q) by destructing q. *)

Require Import sorted.
Import ListNotations.

Section defs.
  Context {A : Set}.
  Context {ordA : Ordered A}.

  Inductive slt : A -> list A -> Prop :=
  | slt0(a : A) : slt a []
  | slt1(a b : A) : lt a b -> slt a [b]
  | sltN(a b : A)(l : list A) : lt a b -> slt b l -> sorted (b::l) -> slt a (b::l).

  Hint Constructors slt.

  Infix "!<" := slt (at level 70) : list_scope.

  Lemma sorted2slt : forall l a, sorted (a::l) <-> a !< l.
  Proof.
    induction l as [|a' l IHl].
    - intros a. split.
      + intros H. constructor.
      + intros H. simpl. constructor.
    - intros a. split.
      + intros H. constructor.
        * inversion H. assumption.
        * eapply IHl. inversion H. assumption.
        * inversion H. assumption.
      + intros H. constructor.
        * eapply IHl. inversion H; subst.
          { constructor. }
          { assumption. }
        * inversion H; assumption.
  Qed.

  Inductive lts : list A -> A -> Prop :=
  | lts0(a : A) : lts [] a
  | lts1(a b : A) : lt a b -> lts [a] b
  | ltsN(a b : A)(l : list A) : lt a b -> lts l b -> sorted(a::l) -> lts (a::l) b.

  Hint Constructors lts.

  Infix "<!" := lts (at level 70) : list_scope.

  Lemma sorted2lts : forall l a, sorted(l++[a]) <-> l <! a.
  Proof.
    induction l as [|a' l IHl].
    - intros a. split.
      + intros H. constructor.
      + intros H. simpl. constructor.
    - intros a. split.
      + intros H. constructor. 
        * simpl in H. apply desort in H. exact H.
        * apply IHl. inversion H.
          { exfalso. eapply app_cons_not_nil. eassumption. }
          { assumption. }
        * apply sortedl in H. assumption.
      + intros H. destruct l.
        * subst. simpl. constructor.
          { constructor. }
          { inversion H; assumption. }
        * simpl. constructor.
          { apply IHl. inversion H. assumption. }
          { inversion H. subst. eapply desort. 
            instantiate (2:=nil). eassumption. }
  Qed.

  Lemma sorted2both : forall l1 l2 a, sorted (l1++a::l2) <-> l1 <! a /\ a !< l2.
  Proof.
    intros l1 l2 a.
    split.
    - intro H.
      split.
      + rewrite <- sorted2lts.
        eapply sortedl.
        rewrite <- app_assoc.
        simpl. eassumption.
      + rewrite <- sorted2slt.
        eapply sortedr.
        eassumption.
    -intros (H1 & H2).
     rewrite <- sorted2lts in H1.
     rewrite <- sorted2slt in H2.
     generalize dependent l1. induction l1.
     + intro. assumption.
     + intro H.
       destruct l1.
       * constructor.
         { assumption. }
         { inversion H. assumption. }
       * simpl in *.
         constructor.
         { apply IHl1. eapply sortedtail. eassumption. }
         { inversion H. assumption. }
  Qed.
  
  Ltac appify H := repeat match type of H with
                       context [?a::?X] => 
                       first [constr_eq X (@nil A); fail 1
                             |change (a::X) with ([a]++X) in H] end.
  
  Ltac appify_goal := repeat match goal with 
                          |- context [?a::?X] => 
                          first [constr_eq X (@nil A); fail 1
                                |change (a::X) with ([a]++X)] end.

  Lemma redlts : forall l a b, (a::l) <! b <-> a !< l /\ l <! b /\ lt a b.
  Proof.
    split.
    - intros H.
      inversion H; subst.
      + repeat split; eauto.
      + repeat split; eauto.
        apply sorted2slt. assumption.
    - intros (H1 & H2 & H3).
      econstructor; eauto.
      rewrite sorted2slt. assumption.
  Qed.

  Lemma redslt : forall l a b, a !< (b::l) <-> lt a b /\ b !< l.
  Proof.
    split.
    - intros H.
      inversion H; subst.
      + repeat split; eauto.
      + repeat split; eauto.
    - intros (H1 & H2).
      econstructor; eauto.
      rewrite sorted2slt. assumption.
  Qed.

  Lemma rwslts : forall a b l2 l3, a !< l2++b::l3 <-> a !< l2  /\ lt a b /\ l2 <! b /\ b !< l3.
  Proof.
    intros a b l2 l3.
    rewrite <- sorted2slt.
    split.
    - intro H. appify H.
      pose (sortedr H) as H1.
      pose (sortedr H1) as H2. simpl in H2.
      rewrite sorted2slt in H2.
      rewrite app_assoc in H1.
      apply sortedl in H1.
      rewrite sorted2lts in H1.
      pose (desort H) as H3.
      pose H as H4.
      rewrite app_assoc in H4.
      apply sortedl in H4.
      simpl in H4. rewrite sorted2slt in H4.
      tauto.
    - intros (H1 & H2 & H3).
      rewrite <- sorted2slt in H1.
      rewrite <- sorted2both in H3.
      apply (@sortins _ _ [] l2 l3 a b H1 H3 H2).
  Qed.

  Lemma slt_trans : forall a b l, lt a b -> b !< l -> a !< l.
  Proof.
    intros a b l H H0.
    inversion H0; subst.
    - constructor.
    - constructor. transitivity b; assumption.
    - constructor.
      + transitivity b; assumption.
      + assumption.
      + assumption.
  Defined.

  Lemma lts_trans : forall l a b, lt a b -> l <! a -> l <! b.
  Proof.
    induction l as [| a b IHl].
    - intros. constructor.
    - intros a0 b0 H0 H1.
      constructor.
      + inversion H1; subst; transitivity a0; assumption.
      + inversion H1; subst.
        * constructor.
        * eapply IHl; eassumption.
      + inversion H1; subst.
        * simpl. constructor.
        * assumption.
  Defined.

  Lemma sorted2both2 : forall l0 l1 l2 a, sorted (l0++l1++a::l2) <-> (l0++l1) <! a /\ a !< l2.
  Proof.
    intros.
    rewrite app_assoc.
    apply sorted2both.
  Defined.

  Lemma ltssorted : forall l a, l <! a -> sorted l.
  Proof.
    intros l a H.
    inversion H; subst.
    - constructor.
    - constructor.
    - assumption.
  Qed.

  Lemma sltsorted : forall l a, a !< l -> sorted l.
  Proof.
    intros l a H.
    inversion H; subst.
    - constructor.
    - constructor.
    - assumption.
  Qed.

  Lemma ltsleft : forall l0 l1 a, (l0++l1) <! a -> l0 <! a.
  Proof.
    intros l0 l1 a H.
    rewrite <- sorted2lts in *.
    rewrite <- app_assoc in H.
    apply (sortedm H).
  Qed.

  Lemma ltsright : forall l0 l1 a, (l0++l1) <! a -> l1 <! a.
  Proof.
    intros l0 l1 a H.
    rewrite <- sorted2lts in *.
    rewrite <- app_assoc in H.
    apply (sortedr H).
  Defined.

  Lemma ltsmk2 : forall l0 l1 a, sorted(l0++l1) -> l0 <! a -> l1 <! a -> (l0++l1) <! a.
  Proof.
    induction l0 as [|a l0 IHl0].
    - intros. simpl. assumption.
    - intros l1 a0 H H0 H1. simpl in *.
      constructor.
      + inversion H0; subst.
        * inversion H0; subst; assumption.
        * assumption.
      + apply IHl0.
        * eapply sortedtail. eassumption.
        * inversion H0; subst; try constructor; try assumption.
        * assumption.
      + assumption.
  Qed.

  Lemma ltssplit : forall l0 l1 a, (l0++l1) <! a <-> sorted(l0++l1) /\ l0 <! a /\ l1 <! a.
  Proof.
    intros. split.
    - intro H.
      repeat split.
      + eapply ltssorted; eassumption.
      + eapply ltsleft; eassumption.
      + eapply ltsright; eassumption.
    - intros (H1 & H2 & H3).
      apply ltsmk2; assumption.
  Qed.

  Lemma sltleft: forall l0 l1 a, a !< (l0++l1) -> a !< l0.
  Proof.
    intros l0 l1 a H.
    rewrite <- sorted2slt in *.
    appify H. rewrite app_assoc in H.
    apply (sortedl H).
  Qed.   

  Lemma sltright: forall l0 l1 a, a !< (l0++l1) -> a !< l1.
  Proof.
    intros l0 l1 a H.
    rewrite <- sorted2slt in *.
    appify H. apply (sortedm H).
  Qed.

  Lemma ltsright1 : forall l a b, a !< ([b]++l) -> lt a b.
  Proof.
    intros l a b H.
    inversion H; subst; assumption.
  Qed.

  Lemma sltlts2sorted : forall a p q, p <! a -> a !< q -> sorted (p++q).
  Proof.
    intros a p q H H0.
    assert (sorted (p++[a]++q)) as H1.
    - apply sorted2both. tauto.
    - apply (sortedm H1).
  Qed.
  
  Lemma sltapp : forall q r a b, a !< q -> q <! b -> b !< r -> lt a b -> a !< q ++ r.
  Proof.
    intros q r a b H H0 H1 H2.
    assert (q <! b /\ b !< r) as H3 by tauto.
    rewrite <- sorted2both in H3.
    rewrite <- sorted2slt in *.
    pose (@sortins _ _ [] q r a b H H3 H2) as H4.
    rewrite app_nil_l in H4.
    appify_goal. rewrite app_assoc.
    eapply sortedm.
    rewrite <- app_assoc.
    appify H4.
    eassumption.
  Qed.

  Lemma lts2lt : forall a b, [a] <! b <-> lt a b.
  Proof.
    intros a b.
    split.
    - intros H.
      inversion H; subst; assumption.
    - intros H.
      constructor.
      assumption.
  Qed.

  Lemma slt2lt : forall a b, a !< [b] <-> lt a b.
  Proof.
    intros a b.
    split.
    - intros H.
      inversion H; subst; assumption.
    - intros H.
      constructor.
      assumption.
  Qed.

End defs.

Create HintDb SolveSortedDB discriminated.

Hint Rewrite @redlts @redslt
     @ltssplit @sorted2both @rwslts @sorted2lts @sorted2slt @sorted2both2 @lts2lt @slt2lt
: solveSortedDB.

Hint Rewrite <- app_assoc : solveSortedDB.
Hint Rewrite <- app_comm_cons : solveSortedDB.

Hint Constructors LocallySorted lts slt : solveSortedDB.

Hint Resolve lts_trans slt_trans sltleft sltright ltsright1 sltlts2sorted sltapp : solveSortedDB.

Ltac solve_sorted := 
  intros; subst; simpl in *;
  autorewrite with solveSortedDB in *;
  try (progress (intuition (simpl in *; eauto with solveSortedDB)); solve_sorted).

Hint Extern 10 (sorted ?X) => match goal with 
                                | H : lts X _ |- _ => apply (ltssorted _ _ H)
                                | H : slt _ X |- _ => apply (sltsorted _ _ H) end
                              : solveSortedDB.

Hint Extern 20 =>
match goal with H : sorted (?L0++?L1++[?A]++?L2) |- _ => 
                apply sorted2both2 in H; solve_sorted end : solveSortedDB.

Hint Extern 10 (lt _ _) => eapply transitivity : solveSortedDB.

(************************************************************************)

Section Examples.
  Context {A : Set}.
  Context {ordA : Ordered A}.

  Goal forall p q r s t u v a b c d e f,
         sorted(p++[a]++(q++[b])++r++([c]++(s++[d])++t++[e])++(u++[f])++v) ->
         sorted(q++([c]++t)++[e]++v).
  Proof. solve_sorted. Qed.

  Goal forall p q r a b, 
         sorted ((p++q++[b])++r) -> sorted (p++[a]++q) -> lt a b ->
         sorted (p++([a]++q++[b])++r).
  Proof. solve_sorted. Qed.

  Goal forall p q r a b, sorted (p++[a]++q++[b]++r) -> sorted(p++q++[b]++r).
  Proof. solve_sorted. Qed.

  Goal forall p q r a b, sorted (p++[a]++q++[b]++r) -> sorted(p++[a]++q++r).
  Proof. solve_sorted. Qed.

  Goal forall p q a b, sorted ((p++[a])++[b]++q) -> sorted(p++[a]++q).
  Proof. solve_sorted. Qed.

  Goal forall p q r a b, sorted ((p++a::q)++b::r) -> sorted (q++b::r).
  Proof. solve_sorted. Qed.

  Goal forall p q r s a b c, sorted ((p++a::(q++b::r))++c::s) ->
                             sorted (p++a::((q++b::r)++c::s)).
  Proof. solve_sorted. Qed.

  Goal forall l a, lts l a -> sorted l.
  Proof. solve_sorted. Qed.

  Goal forall l a, slt a l -> sorted l.
  Proof. solve_sorted. Qed.

End Examples.
