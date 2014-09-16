(*

It is inconsistent in Coq to mix Erasable, even when restricted to
Set->Prop, with proof irrelevance of any Prop that has an extractable
non-Prop field - as with Foo in the following proof.

Fortunately, no results in mindless-coding require proof irrelevance
of any kind.

*)


Inductive Erasable(A : Set) : Prop :=
  erasable: A -> Erasable A.
Arguments erasable [A] _.
Axiom Erasable_inj : forall {A : Set}{a b : A}, erasable a=erasable b -> a=b.

Inductive Foo : Prop :=
  foo: nat -> Foo.

Axiom Foo_irrelevance : forall x y, foo x = foo y.

Definition foo2erasable(f : Foo) : Erasable nat :=
  match f with
    | foo x => erasable x
  end.

Theorem inconsistent: False.
Proof.
  assert (foo 0 = foo 1) as H by (apply Foo_irrelevance).
  apply f_equal with (f := foo2erasable) in H.
  simpl in H.
  apply Erasable_inj in H.
  discriminate H.
Qed.

Check inconsistent.
Print Assumptions inconsistent.

