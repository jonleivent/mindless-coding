(*

It is inconsistent in Coq to have Erasable, with its injectivity
axiom, work over all Types.  This is shown using Hurkens paradox, as
pointed out by Robert Dockins on the Coq-club email list.  Below is a
version of his proof.

However, note that this proof won't work if Erasable is Set->Prop
insetead of Type->Prop, as then Erasable Prop wouldn't be valid.  Hugo
Herbelin, also on the Coq-club email list, suggested limiting Erasable
to Set->Prop and using -impredicative-set.  It turns out that all of
the mindless-coding results work just as well when Erasable is limited
to Set, whether or not one uses -impredicative-set.  Adding
-impredicative-set increases the expressiveness of Set, so it might be
useful in the future.

*)

(*Erasable must be over Type, not Set, for Hurkens to show an inconsistency:*)
Inductive Erasable(A : Type) : Prop := erasable: A -> Erasable A.
Arguments erasable [A] _.
Axiom Erasable_inj : forall {A : Type}{a b : A}, erasable a=erasable b -> a=b.

Require Hurkens.

Definition Hurkens_paradox := 
  Hurkens.NoRetractFromSmallPropositionToProp.paradox.

Definition er_out (X:Erasable Prop) : Prop := 
  exists P:Prop, (X = erasable P) /\ P.

Theorem inconsistent : False.
Proof.
  apply (Hurkens_paradox (Erasable Prop) (@erasable Prop) er_out).
  - intros A H.
    red in H.
    destruct H as [P [H1 H2]].
    apply Erasable_inj in H1.
    subst A.
    exact H2.
  - intros A H.
    red.
    exists A.
    split. 
    + reflexivity.
    + exact H.
Qed.

Check inconsistent.
Print Assumptions inconsistent.

