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

(* Useful lemmas about sorted lists. *)

Require Export List.
Import ListNotations.

Require Export ordered.
Require Export Sorted.

Notation sorted := (LocallySorted lt).

Hint Constructors LocallySorted.

Section defs.
  Context {A : Type}.
  Context {A_ordered : Ordered A}.

  Lemma sortedl : forall {l1 l2 : list A}, sorted (l1++l2) -> sorted l1.
  Proof.
    induction l1; eauto. intros l2 H.
    destruct l1; eauto.
    inversion H. subst. eauto.
  Qed.

  Lemma sortedr : forall {l1 l2 : list A}, sorted (l1++l2) -> sorted l2.
  Proof.
    induction l1; eauto. intros l2 H.
    destruct l1.
    - destruct l2; eauto.
      inversion H. subst. eauto.
    - inversion H. subst. eauto.
  Qed.

  Lemma sortedtail : forall {l : list A}{a : A}, sorted (a::l) -> sorted l.
  Proof.
    intros l a H.
    destruct l.
    - eauto.
    - inversion H. eauto.
  Qed.

  Lemma sortins : forall {l1 l2 l3 : list A}{a b : A},
                    sorted(l1++a::l2) ->
                    sorted(l2++b::l3) -> lt a b ->
                    sorted(l1++a::l2++b::l3).
  Proof.
    induction l1.
    - intros l2 l3 a b H H0 H1.
      destruct l2; simpl in *.
      + inversion H0; subst; eauto.
      + inversion H; subst; eauto.
    - intros l2 l3 a0 b H H0 H1.
      destruct l1; simpl in *.
      + inversion H; subst; eauto using sortedtail.
      + inversion H; subst; eauto using sortedtail.
  Qed.

  Lemma desort : forall {l1 l2 : list A}{a b : A},
                     sorted (a::l1++b::l2) -> lt a b.
  Proof.
    induction l1.
    - intros l2 a b H.
      inversion H; subst; eauto.
    - intros l2 a0 b H.
      inversion H; subst; transitivity a; eauto.
  Qed.

  Lemma sortedm : forall {l1 l2 l3 : list A},
                    sorted (l1++l2++l3) -> sorted (l1++l3).
  Proof.
    induction l1.
    - intros l2 l3 H.
      eauto using sortedr.
    - intros l2 l3 H.
      destruct l1.
      + destruct l3; simpl in *; eauto using sortedtail, desort.
      + simpl in *.
        inversion H; subst; eauto.
  Qed.

  Definition NotIn(x : A)(l : list A) := ~In x l.

  Lemma NotInNil: forall (x : A), NotIn x [].
  Proof.
    intro x.
    apply in_nil.
  Qed.

  Lemma NotInCons: forall {l : list A}{x d : A},
                     lt x d -> sorted (d::l) -> NotIn x (d::l).
  Proof.
    induction l as [|y l IHl].
    - intros x d H H0.
      destruct 1; subst; eauto.
      contradict H.
      apply irreflexivity.
    - intros x d H H0.
      inversion H0; subst.
      destruct 1; subst.
      + contradict H. apply irreflexivity.
      + eapply (IHl x y); eauto.
        transitivity d; eauto.
  Qed.

  Lemma NotInl: forall {x d : A}{l1 l2:list A},
                  NotIn x l1 -> lt x d -> sorted(l1++d::l2) ->
                  NotIn x (l1++d::l2).
  Proof.
    induction l1 as [|y l1 IHl1].
    - intros l2 H H0 H1.
      simpl in *.
      auto using NotInCons.
    - intros l2 H H0 H1.
      destruct 1 as [|H2]; subst.
      + elim H.
        apply in_eq.
      + eapply IHl1 in H2; eauto.
        * intro. elim H. simpl. auto.
        * eauto using sortedtail.
  Qed.

  Lemma NotInr: forall {x d : A}{l1 l2 : list A},
                  NotIn x l2 -> lt d x -> sorted(l1++d::l2) ->
                  NotIn x (l1++d::l2).
  Proof.
    induction l1 as [|y l1 IHl1].
    - intros l2 H H0 H1.
      destruct 1; subst.
      + contradict H0.
        apply irreflexivity.
      + contradiction.
    - intros l2 H H0 H1.
      destruct 1 as [|H2]; subst.
      + apply desort in H1.
        contradict (irreflexivity (transitivity H1 H0)).
      + contradict H2.
        eapply IHl1; eauto using sortedtail.
  Qed.

End defs.

Hint Resolve NotInNil NotInl NotInr.
