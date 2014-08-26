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

Inductive Erasable(A : Type) : Prop :=
  erasable: A -> Erasable A.

Arguments erasable [A] _.

Hint Constructors Erasable.

Scheme Erasable_elim := Induction for Erasable Sort Prop.

Module ErasableNotation.
  Notation "## T" := (Erasable T) (at level 1, format "## T") : Erasable_scope.
  Notation "# x" := (erasable x) (at level 1, format "# x") : Erasable_scope.
  Open Scope Erasable_scope.
End ErasableNotation.

Import ErasableNotation.

(*This Erasable_inj axiom is the key enabler of erasability beyond
what Prop already provides.  Note that it can't be mixed with general
proof irrelevance, although it should work with less general proof
irrelevance, such as irrelevance for equivalnce proofs.*)
Axiom Erasable_inj : forall (A : Type)(a b : A), #a=#b -> a=b.

Require Setoid. (*needed for Erasable_rw users*)

Lemma Erasable_rw : forall (A: Type)(a b : A), (#a=#b) <-> (a=b).
Proof.
  intros A a b.
  split.
  - apply Erasable_inj.
  - congruence.
Qed.

Ltac unerase_hyp H :=
  hnf in H; try simpl in H;
  first [match type of H with _=_ => apply Erasable_inj in H end
        |induction H as [H] using Erasable_elim
        |let X := fresh H in 
           induction H as [W] using Erasable_elim; clear H; rename W into H
        |match type of H with
             ex _ =>
             let H1 := fresh in
             let H2 := fresh in
             let H3 := fresh in
             destruct H as [H1 [H2 H3]];
               try unerase_hyp H1;
               unerase_hyp H2;
               rewrite H2 in H3; clear H2 H1 H; rename H3 into H
         end].

Ltac unerase0 :=
  match goal with
    | H : _ |- _ => unerase_hyp H
    | |- _ => hnf; try simpl; 
              first[rewrite Erasable_rw
                   |progress apply erasable
                   |eexists; rewrite Erasable_rw; split; [reflexivity|]
                   |let H := fresh in intro H; unerase0; try revert H]
  end; try unerase0.

Inductive Already_Unerased : Type :=
  already_unerased : Already_Unerased.

(*This unerase tactic "unlifts" erasable types and values for
Prop-context goals.  It attempts to keep all unerased hyps named as
the erased ones were named, and to otherwise maintain the structure of
the goal. *)
Ltac unerase := 
  lazymatch goal with
    | H : Already_Unerased |- _ => fail "Already Unerased!"
    | |- ?G => lazymatch type of G with 
                 | Prop => pose already_unerased; unerase0
                 | _ => fail "Only works in a Prop context!"
               end
  end.

(* Erasable+Prop is a monad, and appE is application within that monad
of lifted functions.  But, the result would then need the "f $ x $ y"
syntax, and would also make operators ugly... *)
Definition appE{T1 T2}(f : ##(T1 -> T2))(x : ## T1) : ## T2.
Proof.
  unerase.
  exact (f x).
Defined.

(*Infix "$" := appE (left associativity, at level 98) : ELN_scope.*)

(* ... So, instead of lifting functions with # alone, we use lifters
that leave the normal application syntax intact.  This means we need
to do a little more work to lift, but end up with a much more readable
result. *)
Definition lift1{A B : Type}(f : A -> B)(a : ##A) : ##B.
Proof.
  unerase.
  exact (f a).
Defined.

Definition lift2{A B C : Type}(f : A -> B -> C)(a : ##A)(b : ##B) : ##C.
Proof.
  unerase.
  exact (f a b).
Defined.

(* For Props, instead of a normal lifting of the entire signature,
which would result in ##Prop type instead of a more usable Prop type,
the Prop is wrapped in an existential to accept the erasable arg. *)
Definition liftP1{A : Type}(p : A -> Prop)(ea : ##A) : Prop :=
  exists (a : A), #a=ea /\ p a.

Definition liftP2{A B : Type}(p : A -> B -> Prop)(ea : ##A)(eb : ##B) : Prop :=
  exists (a : A), #a=ea /\ exists (b : B), #b=eb /\ p a b.

Ltac discriminate_erasable :=
  repeat intro; exfalso; unerase; discriminate.

Ltac discriminate_erasable_hyp H :=
  exfalso; unerase; discriminate H.

(*Erasable injection for 1 arg functions - multi-arg cases can be
added as needed.*)
Lemma Einjection : forall (T T' : Type)(f : T -> T'),
                     (forall (a b : T), f a = f b -> a=b) ->
                     forall (ea eb : ##T), lift1 f ea = lift1 f eb -> ea=eb.
Proof.
  intros.
  unerase.
  eauto.
Qed.

Ltac simplify_1hyp := match goal with
           | H : False |- _ => contradict H
           | H : _ /\ _ |- _ => decompose [and] H; clear H
           | H : _ \/ _ |- _ => decompose [or] H; clear H
           | H : ?X = ?X |- _ => clear H
           | H : ?X = ?X -> False |- _ => contradict H; reflexivity
           | H : ?X <> ?X |- _ => contradict H; reflexivity
           | H : ?X = ?Y |- _ =>
             first [subst X
                   |subst Y
                   |apply Einjection in H; [|solve [clear H; intros ? ? H; injection H; trivial]]
                   |discriminate_erasable_hyp H
                   |discriminate H
                   |injection H; clear H; intro H
                   |unerase_hyp H]
         end.

Ltac simplify_hyps :=
  repeat simplify_1hyp.

(* A "good enough" general purpose inversion tactic for when erasable
types are involved.  Maybe later, consider generalizing further using
things like generalize_eqs_vars. *)
Ltac xinv H :=
    simple inversion H; clear H; simplify_hyps;
    try discriminate; try discriminate_erasable; try trivial; try tauto.

