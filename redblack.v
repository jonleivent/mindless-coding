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

This is a demonstration of Erasability in Coq.  This demonstration
generates verified code for Red/Black tree insert, find, delete
minimum (delmin) and delete functions, where all proof-related aspects
of the code have been erased.  The current state of the code is that
the keys are nats - but this should be easy to genericize without much
impact.

The Red/Black trees and functions used in the demonstrate feature very
elaborate specifications that attempt to formalize all
non-performance-related constraints.

- Why Coq, why not Agda or Idris?  Coq's Prop universe is almost a
  fully functional erasability mechanism as is - it just needs a
  single injectivity axiom on a single Prop (Erasable) to be fully
  functional.  As far as I can tell, something similar isn't possible
  with Agda's irrelevance notations because they already incorporate
  proof irrelevance (whereas in Coq, proof irrelevance is an
  additional axiom that isn't - and can't be - used here).  Idris is
  still experiencing growing pains at this point in time, but may
  become the most hospitable environment for erasability in the future
  (a built-in erasability mechanism is being developed for it).

- Functions are implemented in Coq using tactics in proof mode for
  three reasons: to benefit from the interactive-ness of proof mode,
  to enable the usage of tactics, and to avoid the complexity behind
  successfully using the match-with construct in Coq in complex
  dependently-typed-with-indices contexts.

- Why explicit erasability?  Why not allow the compiler to do it all
  for you?  This is an on-going debate.  Note that there is nothing
  about this demonstration that requires that the compiler not find
  more to erase, and erase it.  The opinion of the author is that
  having erasability work as a type constraint during implementation
  of functions helps to prevent the programmer from "cheating" by
  accidentally raiding should-be-erased code and using any information
  obtained in run-time (unerased) code, thus destroying the
  erasable-ness of the former.  It has a similar effect on tactics -
  they can't cheat either, so a more liberal usage of tactics is not
  discouraged.  One point of the demonstration here is that explicit
  erasability doesn't imply messy development - for example, it
  doesn't require re-implementation of any existing types or
  functions.

- Why a Red/Black tree?  It's well known, useful, and difficult to get
  right.  Hence, the ability here to "mindlessly" implement the
  insert, find, delmin, and especially the delete function for
  Red/Black trees with full erasability of all proof-related
  paraphernalia is a non-trivial accomplishment.  By "mindless", we
  refer to the nature of implementing these functions once their type
  specifications, as well as that of rbtree itself, are made
  sufficiently complete so as to constrain any implementation that
  type-checks to be fully correct.  The author did not use existing
  implementations of Red/Black trees for reference.

- What's the goal?  Explore the potential of "mindless" programming,
  as described above.  Erasability is important because it liberates
  specification from the concerns of burdening executable code with
  proof-related paraphernalia.  That's important because highly
  constraining specifications, in the form of very proof-laden
  dependent types, are needed guide the implementation to the point
  where the function implementer can just be concerned with satisfying
  small incremental goals, (mostly) without carrying around the
  cognitive load of the algorithm's details.

- What next?  Generalize the Red/Black tree for more than just nat
  elements.  Modularize it.  Maybe fit it into the MSet framework?
  Investigate other algorithms besides Red/Black trees.  Also, clean
  up and generalize the tactics, and investigate speeding up the eauto
  calls (which are burdened by usage of Hint Extern).  Try again in
  Idris when its built-in erasability is ready.

- Suggestions for language developers: Make room for erasability,
  instead of just Prop or irrelevance.  In Coq, that might mean
  insulating Erasable from the possible usage of proof_irrelevance
  somehow.  Specific to this development - a unifier that understands
  the associativeness of monoids (lists in this case) would be nice.
  Also - provide a way to automate partial inversion tactics - see
  autoOKNode, autoOKins, autoOKd and the lemmas they apply - also some
  other tactics (such as Einjection) - these tactics are used for
  getting useful information out of an inductively-typed hypothesis
  without case-splitting it in an unerased context - either because
  case-splitting at that point would produce a corresponding case
  analysis in the extracted code, or because case-splitting of a Prop
  isn't allowed in a non-Prop context.

***********************************************************************)

Require Import List Arith.
Import ListNotations.

Inductive Erasable(A : Type) : Prop :=
  erasable: A -> Erasable A.

Arguments erasable [A] _.

Hint Constructors Erasable.

Scheme Erasable_elim := Induction for Erasable Sort Prop.

Notation "## T" := (Erasable T) (at level 89) : Erasable_scope.
Notation "# x" := (erasable x) (at level 59) : Erasable_scope.
Open Scope Erasable_scope.

(*This Erasable injection axiom is the 'secret sauce' that enables
much of the erasure demonstrated below.  Note that it can't be mixed
with general proof_irrelevance and its kin, although it should work
just fine with less generic proof irrelevance, like irrelevance for
equivalences. *)
Axiom Erasable_inj : forall (A : Type)(a b : A), #a=#b -> a=b.

Ltac expose_erased_types := 
  repeat match goal with
           | V : ?T |- _ => 
             match T with 
               | (## _) => fail 1
               | _ => idtac
             end;
               hnf in V; match type of V with (## _) => idtac end
         end.

Ltac Prop_context_check := 
  lazymatch goal with
  | _:_ |- ?G => lazymatch type of G with 
                 | Prop => idtac
                 | _ => fail "Only works in a Prop context!"
                 end
  end.

Ltac unerase :=
  Prop_context_check;
  expose_erased_types;
  repeat match goal with
           | X : ## _ |- _ => induction X as [X] using Erasable_elim 
         end.

Ltac discriminate_erasable H := 
  exfalso;
  unerase;
  simpl in H;
  apply Erasable_inj in H;
  solve [simplify_eq H
        |contradict H; auto].

Ltac collect_inj_eqs X :=
  match goal with
      | |- ?A=?B -> ?C=?D -> ?E=?F -> ?G=?H -> _ =>
        instantiate (1:=A=B/\C=D/\E=F/\G=H) in (Value of X)
      | |- ?A=?B -> ?C=?D -> ?E=?F -> _ =>
        instantiate (1:=A=B/\C=D/\E=F) in (Value of X)
      | |- ?A=?B -> ?C=?D -> _ =>
        instantiate (1:=A=B/\C=D) in (Value of X)
      | |- ?A=?B -> _ =>
        instantiate (1:=A=B) in (Value of X)
  end.

(* The "Prop-smuggling" technique used in Einjection - where a Prop
evar is used to gather info produced in a Prop context and ship it to
a non-Prop context - isn't fully general, and is actually quite
fragile - because of what happens during the instantiations in
collect_inj_eqs (where sometimes Coq adds # to some terms that don't
need it, and other times doesn't add # to terms that do).  If it can
be made fully general, then we could dispense with those autoOKX
partial inverters in most cases. *)
Ltac Einjection H :=
  let P := fresh in
  let Q := fresh in
  evar (P:Prop);
  assert P as Q; [
    unerase;
    hnf in H;
    try simpl in H;
    apply Erasable_inj in H;
    injection H;
    collect_inj_eqs P;
    subst P;
    let R := fresh in repeat (intro R; rewrite R; clear R); tauto
  |subst P; revert Q].

Ltac injection_erasable H A B := 
  let W := fresh in
  assert (W:A=B) by (unerase;
                     hnf in H; try simpl in H;
                     apply Erasable_inj in H;
                     inversion H;
                     subst;
                     reflexivity);
  inversion W;
  subst;
  clear H.

Ltac auto_erasable :=
  expose_erased_types;
  repeat match goal with
           | H : ?X = ?X |- _ => clear H
           | H : ?X = _ |- _ =>
             match type of X with
                 (## _) => discriminate_erasable H
             end
           | H : (# ?A)=(# ?B) |- _ => injection_erasable H A B
           | A : (## ?T), B : (## ?T), H : ?C = ?D |- _ => 
             match C with
                 context[A] => 
                 match D with
                     context[B] => injection_erasable H A B
                 end
             end
         end.

Ltac simplify_hyps :=
  repeat match goal with
           | H : ?X /\ ?Y |- _ => decompose [and] H; clear H
           | H : ?X \/ ?Y |- _ => decompose [or] H; clear H
           | H : ?X = ?Y |- _ =>
             first [is_var(X); subst X
                   |is_var(Y); subst Y
                   |apply Erasable_inj in H
                   |discriminate_erasable H
                   |Einjection H; intros; try subst
                   |simplify_eq H]
         end.

Ltac bind_and_return := unerase; apply erasable.

(* Erasable+Prop is a monad, and appE is application within that monad
of lifted functions.  But, the result would then need the "f $ x $ y"
syntax, and would also make operators ugly... *)
Definition appE{T1 T2}(f : ##(T1 -> T2))(x : ## T1) : ## T2.
Proof.
  bind_and_return.
  exact (f x).
Defined.

Infix "$" := appE (left associativity, at level 98) : ELN_scope.

(* ... So, instead of lifting functions with # alone, we use lifters
that leave the normal application syntax intact.  This means we need
to do a little more work to lift, but end up with a much more readable
result. *)
Definition lift1{A B : Type}(f : A -> B)(a : ##A) : ##B.
Proof.
  bind_and_return.
  exact (f a).
Defined.

Definition lift2{A B C : Type}(f : A -> B -> C)(a : ##A)(b : ##B) : ##C.
Proof.
  bind_and_return.
  exact (f a b).
Defined.

(* For Props, instead of a normal lifting of the entire signature,
which would result in ##Prop type instead of a more usable Prop type,
the Prop is wrapped in an existential to accept the erasable arg.
*)
Definition liftP1{A : Type}(p : A -> Prop)(ea : ##A) : Prop :=
  exists (a : A), #a=ea /\ p a.

Ltac inexist := eexists; split; [reflexivity|].

Ltac deexist := match goal with
                    H : ex _ |- _ => decompose record H; clear H
                end.

Ltac dolift := 
  intros;
  hnf in *;
  try unerase;
  try simpl in *;
  repeat deexist;
  auto_erasable;
  try inexist.

Ltac lift_lemma r :=  (*doesn't always work in Coq trunk*)
  dolift;
  try first [eapply r|rewrite r];
  eauto; try simpl; try eassumption.

(**********************************************************************)
(* Sorted list facts.  Just ordinary stuff - nothing erasable here.
We'll use sorted lists as one of the correctness constraints for
Red/Black trees. *)

Inductive sorted : list nat -> Prop :=
| sorted0 : sorted []
| sorted1 : forall (n : nat), sorted [n]
| sortedN : forall (n1 n2 : nat)(l : list nat),
              lt n1 n2 -> sorted(n2::l) -> sorted(n1::n2::l).

Hint Constructors sorted.

Lemma sortedl : forall {l1 l2 : list nat}, sorted (l1++l2) -> sorted l1.
Proof.
  induction l1; eauto. intros l2 H.
  destruct l1; eauto.
  inversion H. subst. eauto.
Qed.

Lemma group3app : forall {A}(l1 l2 l3 l4 : list A),
                    l1++l2++l3++l4 = (l1++l2++l3)++l4.
Proof.
  intros A l1 l2 l3 l4.
  rewrite <- ?app_assoc.
  reflexivity.
Qed.

Lemma sortedl3 : forall {l1 l2 l3 l4 : list nat},
                    sorted (l1++l2++l3++l4) -> sorted (l1++l2++l3).
Proof.
  intros l1 l2 l3 l4 H.
  rewrite group3app in H.
  apply sortedl in H.
  assumption.
Qed.

Lemma sortedr : forall {l1 l2 : list nat}, sorted (l1++l2) -> sorted l2.
Proof.
  induction l1; eauto. intros l2 H.
  destruct l1.
  - destruct l2; eauto.
    inversion H. subst. eauto.
  - inversion H. subst. eauto.
Qed.

Lemma sortedr1 : forall {l : list nat}{a : nat}, sorted (a::l) -> sorted l.
Proof.
  intros l a H.
  change (a::l) with ([a]++l) in H.
  apply sortedr in H.
  assumption.
Qed.

Lemma sortedr2 : forall {l1 l2 l3 : list nat},
                   sorted ((l1++l2)++l3) -> sorted (l2++l3).
Proof.
  intros l1 l2 l3 H.
  rewrite <- app_assoc in H.
  apply sortedr in H.
  assumption.
Qed.

Lemma sortedr3 : forall {l1 l2 l3 l4 : list nat},
                   sorted ((l1++l2++l3)++l4) -> sorted (l2++l3++l4).
Proof.
  intros l1 l2 l3 l4 H.
  rewrite <- ?app_assoc in H.
  apply sortedr in H.
  assumption.
Qed.

Lemma sortins : forall {l1 l2 l3 : list nat}{a b : nat},
                  sorted(l1++[a]++l2) ->
                  sorted(l2++[b]++l3) -> lt a b ->
                  sorted(l1++[a]++l2++[b]++l3).
Proof.
  induction l1.
  - intros l2 l3 a b H H0 H1.
    destruct l2; simpl in *.
    + inversion H0; subst; eauto.
    + inversion H; subst; eauto.
  - intros l2 l3 a0 b H H0 H1.
    destruct l1; simpl in *.
    + econstructor; eauto.
      * inversion H; subst; eauto.
      * eauto using sortedr1.
    + econstructor; eauto.
      * inversion H; subst; eauto.
      * eauto using sortedr1.
Qed.

Lemma sortins2 : forall {l1 l2 l3 : list nat}{a b : nat},
                   sorted(l1++[a]++l2) ->
                   sorted(l2++[b]++l3) -> lt a b ->
                   sorted((l1++[a]++l2)++[b]++l3).
Proof.
  intros l1 l2 l3 a b H H0 H1.
  rewrite <- ?app_assoc.
  apply sortins; assumption.
Qed.

Lemma desort : forall {l1 l2 : list nat}{a b : nat},
                   sorted (a::l1++b::l2) -> lt a b.
Proof.
  induction l1.
  - intros l2 a b H.
    inversion H; subst; eauto.
  - intros l2 a0 b H.
    inversion H; subst; transitivity a; eauto.
Qed.

Lemma sortedm : forall {l1 l2 l3 : list nat},
                  sorted (l1++l2++l3) -> sorted (l1++l3).
Proof.
  induction l1.
  - intros l2 l3 H.
    eauto using sortedr.
  - intros l2 l3 H.
    destruct l1.
    + destruct l3; simpl in *; eauto.
      eauto using sortedr1, desort.
    + simpl in *.
      inversion H; subst; eauto.
Qed.

Definition NotIn(x : nat)(l : list nat) := ~In x l.

Lemma NotInNil: forall (x : nat), NotIn x [].
Proof.
  intro x.
  apply in_nil.
Qed.

Lemma NotInCons: forall {l : list nat}{x d : nat},
                   lt x d -> sorted (d::l) -> NotIn x (d::l).
Proof.
  induction l as [|y l IHl].
  - intros x d H H0.
    destruct 1; subst; eauto.
    contradict H.
    apply lt_irrefl.
  - intros x d H H0.
    inversion H0; subst.
    destruct 1; subst.
    + contradict H. apply lt_irrefl.
    + eapply (IHl x y); eauto.
      transitivity d; eauto.
Qed.

Lemma NotInl: forall {x d : nat}{l1 l2:list nat},
                NotIn x l1 -> lt x d -> sorted(l1++[d]++l2) ->
                NotIn x (l1++[d]++l2).
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
      * intro.
        elim H.
        simpl.
        auto.
      * eauto using sortedr1.
Qed.

Lemma NotInr: forall {x d : nat}{l1 l2 : list nat},
                NotIn x l2 -> lt d x -> sorted(l1++[d]++l2) ->
                NotIn x (l1++[d]++l2).
Proof.
  induction l1 as [|y l1 IHl1].
  - intros l2 H H0 H1.
    destruct 1; subst.
    + contradict H0.
      apply lt_irrefl.
    + contradiction.
  - intros l2 H H0 H1.
    destruct 1 as [|H2]; subst.
    + contradict H0.
      apply desort in H1.
      apply lt_asym.
      assumption.
    + contradict H2.
      eapply IHl1; eauto using sortedr1.
Qed.

Hint Resolve NotInNil NotInl NotInr.

(* Keep list append opaque, because simpl-ing down to cons would just
require even more work. *)
Opaque app.

(* A very ugly tactic to apply the above sorted lemmas at the
appropriate times.  Hint Resolve didn't work well.  Also note that we
have multiple flavors of some lemmas - the ones with numeric suffixes
- this helps deal with the absence of associative unification - as
will some later tactics (xauto, zauto). *)
Ltac Sorter := 
  match goal with
    | H : sorted(?X++_) |- sorted(?X) => 
      apply sortedl in H; exact H
    | H : sorted(?X++?Y++?Z++_) |- sorted(?X++?Y++?Z) =>
      apply sortedl3 in H; exact H
    | H : sorted(_++?X) |- sorted(?X) =>
      apply sortedr in H; exact H
    | H : sorted(_++_++?X) |- sorted(?X) =>
      do 2 apply sortedr in H; exact H
    | H : sorted((_++?X)++?Y) |- sorted(?X++?Y) =>
      apply sortedr2 in H; exact H
    | H : sorted((_++?X++?Y)++?Z) |- sorted(?X++?Y++?Z) =>
      apply sortedr3 in H; exact H
    | H : sorted(?X++_++?Y) |- sorted(?Z++?Y) =>
      apply sortedm in H; exact H
    | |- sorted(?L1++[?A]++?L2++[?B]++?L3) =>
      eapply sortins
    | |- sorted((?L1++[?A]++?L2)++[?B]++?L3) =>
      eapply sortins2
  end.

(**********************************************************************)
(* Lifting sorted to erasable lists.  By convention, the "E" prefix
will imply erasability of something that isn't Prop all the way down. *)

Definition Esorted := (liftP1 sorted).

Definition Eapp := (lift2 (@app nat)).

(* Some nice syntax for erasable lists.  Note the use of ^x instead
of [x] - because for some reason [x] wouldn't work in all cases. *)
Infix "++" := Eapp (right associativity, at level 60) : ELN_scope.
Notation " [ ] " := (# nil) : ELN_scope.
Notation "^ x" := (# (cons x nil)) (at level 59) : ELN_scope.
Delimit Scope ELN_scope with eln.
Bind Scope ELN_scope with Erasable.
Bind Scope list_scope with list.
Open Scope ELN_scope.

Definition ELN := (## list nat).

Definition ENotIn(x : nat) := liftP1 (NotIn x).

Hint Extern 20 (ENotIn _ _) => dolift; eauto.

(* It's convenient to have associativity to be established both for
normal and erasable lists. *)
Lemma Eapp_assoc: forall {p q r : ELN}, (p++q)++r=p++(q++r).
Proof.
  dolift.
  rewrite app_assoc.
  reflexivity.
Qed.

(* There's some kind of strange behavior in Coq where sometimes
rewrite Foo in * won't rewrite a hypothesis H, but rewrite Foo in H
will.  So, get around that: *)
Ltac grew0 R :=
  match goal with H : _ |- _ => rewrite R in H; try grew0 R end.

Ltac grew R := rewrite ?R; try grew0 R.

(* Eappnorm will normalize all erasable lists in a goal. *)
Ltac Eappnorm := grew Eapp_assoc.

Lemma group3Eapp: forall (p q r s : ELN), p++q++r++s=(p++q++r)++s.
Proof.
  intros.
  Eappnorm.
  reflexivity.
Qed.

(* Eapp3 will denormalize all erasable lists in a goal such that their
3 leftmost appendands are grouped together.  Note that the 'grew' hack
isn't needed here. *)
Ltac Eapp3 := rewrite group3Eapp in *.

(**********************************************************************)

Definition EN := (## nat).

Definition ES := (lift1 S).

Definition E0 := (# 0).

Inductive color : Set :=
| Red : color
| Black : color.

Definition EC := (## color).
Definition EBlack := (# Black).
Definition ERed := (# Red).

(* OKNode captures the allowed relationships between color and
black-height of a node and its children. *)
Inductive OKNode : EC -> EN -> EC -> EC -> EN -> Type :=
| OKRed{n : EN} : OKNode ERed n EBlack EBlack n
| OKBlack{n : EN}{cl cr : EC} : OKNode EBlack (ES n) cl cr n.

(* OKNode is a Type instead of a Prop because it becomes the unerased
color bit in each node, as all of its fields are erased. *)

Hint Constructors OKNode.

Ltac sinv H := 
  simple inversion H; clear H; try subst; auto_erasable;
  try discriminate; try trivial; try tauto.

Lemma OKNode1(no ni : EN)(cl cr : EC) : OKNode ERed no cl cr ni -> no=ni/\cl=EBlack/\cr=EBlack.
Proof.
  intro ok. sinv ok.
Qed.

Lemma OKNode2(no ni : EN)(cl cr : EC) : OKNode EBlack no cl cr ni -> no=ES ni.
Proof.
  intro ok. sinv ok.
Qed.

Lemma OKNode3(no ni : EN)(co cr : EC) : OKNode co no ERed cr ni -> co=EBlack/\no=ES ni.
Proof.
  intro ok. sinv ok.
Qed.

Lemma OKNode4(no ni : EN)(co cl : EC) : OKNode co no cl ERed ni -> co=EBlack/\no=ES ni.
Proof.
  intro ok. sinv ok.
Qed.

(*The above OKNodeN lemmas, and the following autoOKNode tactic, allow
us to get constraint information out of an OKNode without destructing
it.  By not destructing an OKNode when we don't have to, we reduce the
number of case analyses in the extracted code.  It would be nice if
there was an automatic way of generating this. *)
Ltac autoOKNode :=
  match goal with 
      H: OKNode _ _ _ _ _ |- _ =>
      first [apply OKNode1 in H
            |apply OKNode2 in H
            |apply OKNode3 in H
            |apply OKNode4 in H];
        simplify_hyps
  end.

(* Red-Black Tree, with erasable indices color (c), black height (n),
and "flattening" (f), which is a flattened list of the full contents
of the tree.  This specification contains the Red/Black constraints
(OKNode) and ordering constraints. *)
Inductive rbtree : forall (c : EC)(n : EN)(f : ELN), Type :=
| Leaf : rbtree EBlack E0 []
| Node : forall {co no cl cr ni fl fr}(ok : OKNode co no cl cr ni)
                (tl : rbtree cl ni fl)(d : nat)(tr : rbtree cr ni fr)
                (s : Esorted (fl++^d++fr)), rbtree co no (fl++^d++fr).

Hint Constructors rbtree.

(* Convert a red node into a black one.*)
Definition r2b{n : EN}{f : ELN}(t : rbtree ERed n f) : rbtree EBlack (ES n) f.
Proof.
  sinv t. intros.
  (*If we use "sinv ok" instead of "autoOKNode" here, we end up with a
  solution, but one that contains one extra match that doesn't really
  accomplish anything.  That's the point to autoOKNode: invert an
  OKNode in certain cases without any runtime cost.*)
  autoOKNode.
  eauto.
Defined.

(* Convert any node into a black one.  The resulting node's black
height can vary as a result, so capture the relationship between the
input and output black heights in a Prop:*)
Inductive N2N : EC -> bool -> EN -> EN -> Prop :=
| N2NF(n : EN) : N2N ERed false n (ES n)
| N2NT(n : EN) : N2N EBlack true n n.

(* Why is N2N a Prop with a bool arg instead of Type without a bool
arg?  Because that bool becomes useful later as a way to prevent
having to case analyze an N2N when the goal also has a bool arg
corresponding to black height incrementing. *)

(* Note that the EC arg in N2N is needed so that which N2N ctor gets used
is constrained by the color of the input tree.  Otherwise, both
constructors are considered viable options regardless of the color,
which is incorrect. *)

Hint Constructors N2N.

Inductive blkn(c : EC)(n : EN)(f : ELN) : Type :=
  mkblkn(b : bool)(no : EN) : N2N c b n no -> rbtree EBlack no f -> blkn c n f.

Hint Constructors blkn.

Definition blacken{c}{n}{f}(t : rbtree c n f) : blkn c n f.
Proof.
  sinv t; eauto.
  intro ok; sinv ok; eauto.
Defined.

(* Allow case analysis of the color of a node without destructing the node. *)
Definition Cof{c}{n}{f}(t : rbtree c n f) : { c' : color | c=#c' }.
Proof.
  sinv t; [|intro ok; sinv ok]; econstructor; reflexivity.
Defined.

Ltac csplit t := (* split on the color of t *)
  let H := fresh in
    case (Cof t); [intros [|] H|..]; rewrite H in *; clear H; eauto.

(* Sometimes, we can benefit (in terms of generated code complexity)
from comparing two nodes directly by color, instead of case analyzing
the color of each separately. *)
Inductive CComp(c1 c2: EC) : Type :=
| CCompEQ : c1=c2 -> CComp c1 c2
| CCompRB : c1=ERed -> c2=EBlack -> CComp c1 c2 
| CCompBR : c1=EBlack -> c2=ERed -> CComp c1 c2.

Hint Constructors CComp.

Definition ccomp{c1 c2 : EC}{n1 n2 : EN}{f1 f2 : ELN}
           (t1 : rbtree c1 n1 f1)(t2 : rbtree c2 n2 f2) : CComp c1 c2.
Proof.
  csplit t1; csplit t2.
Defined.

(* Allow access to the "Esorted" constraint in the node without destructing. *)
Definition Sof{c}{n}{f}(t : rbtree c n f) : Esorted f.
Proof.
  destruct t; dolift; eauto.
Defined.

Hint Resolve Sof.

Ltac Sofem :=
  repeat match goal with
             H : rbtree _ _ _ |- _ => apply Sof in H
         end.

Hint Extern 20 (Esorted _) => Sofem; dolift; repeat Sorter; eauto.

Ltac xauto := (* a poor man's associative unifier *)
  intros; try subst;
  try solve [eauto
            |Eappnorm; eauto
            |Eapp3; eauto
            |Eappnorm; Eapp3; eauto].

(* Balancing functions.  The functions bal1..4 were found by
trial-and-error - basically just attempting to prove
insert/delmin/delete until an rbtree goal is reached without any
direct way (without inversions) for it to be constructed from the
rbtrees in the hypotheses.  Later, bal0 was added to simplify bal1 and
bal2. *)
Definition bal0{n : EN}{cl cr : EC}{fl fm fr : ELN}{x y : nat}
           (tl : rbtree cl n fl)
           (tm : rbtree ERed n fm)
           (tr : rbtree cr n fr)
           (s : Esorted (fl++^x++fm++^y++fr)) :
  rbtree ERed (ES n) (fl++^x++fm++^y++fr).
Proof.
  sinv tm.
  intro ok.
  autoOKNode.
  xauto.
Defined.

Hint Extern 40 (rbtree _ _ (_++_++_++_++_)) => eapply bal0.

Hint Resolve r2b.

(* CT is a specific sigT that erases down to just t alone.  If sigT
were used instead, c would get erased, but the underlying pair would
still exist, just with "_" as the contents of the first arg. *)
Inductive CT(n : EN)(f : ELN) : Type :=
  mkCT(c : EC)(t : rbtree c n f) : CT n f.

Hint Extern 30 (CT _ (_++_++_)) => 
  solve [econstructor; xauto].

(* Note the symmetry : bal1<->bal2, bal3<->bal4 *)

Definition bal1{n : EN}{fl fr : ELN}{cr : EC}
         (tl : rbtree EBlack (ES n) fl)(d : nat)(tr : rbtree cr n fr)
         (s : Esorted (fl++^d++fr)) : CT (ES n) (fl++^d++fr).
Proof.
  sinv tl.
  intros ok tll trl.
  autoOKNode.
  auto_erasable.
  csplit trl.
  csplit tll.
Defined.

Definition bal2{n : EN}{fl fr : ELN}{cl : EC}
           (tl : rbtree cl n fl)(d : nat)(tr : rbtree EBlack (ES n) fr)
           (s : Esorted (fl++^d++fr)) : CT (ES n) (fl++^d++fr).
Proof.
  sinv tr.
  intros ok tlr trr.
  autoOKNode.
  csplit trr.
  csplit tlr.
Defined.

Definition bal3{n : EN}{fl fr : ELN}
           (tl : rbtree EBlack n fl)(d : nat)
           (tr : rbtree ERed (ES n) fr)
           (s : Esorted (fl++^d++fr)) :
  rbtree EBlack (ES (ES n)) (fl++^d++fr).
Proof.
  sinv tr. intros.
  autoOKNode.
  Eapp3. eelim bal2; eauto.
Defined.

Hint Resolve bal3.

Definition bal4{n : EN}{fl fr : ELN}
           (tl : rbtree ERed (ES n) fl)(d : nat)
           (tr : rbtree EBlack n fr)
           (s : Esorted (fl++^d++fr)) :
  rbtree EBlack (ES (ES n)) (fl++^d++fr).
Proof.
  sinv tl.  intros.
  autoOKNode.
  Eappnorm. eelim bal1; eauto.
Defined.

Hint Resolve bal4.

Lemma Eapp_nil_l : forall (l : ELN), []++l=l.
Proof.
  dolift.
  reflexivity.
Qed.

Lemma Eapp_nil_r : forall (l : ELN), l++[]=l.
Proof.
  dolift.
  rewrite app_nil_r.
  reflexivity.
Qed.

Hint Extern 500 => rewrite app_nil_l in *; eauto.
Hint Extern 500 => rewrite app_nil_r in *; eauto.
Hint Extern 600 => rewrite Eapp_nil_l in *; eauto.
Hint Extern 600 => rewrite Eapp_nil_r in *; eauto.

Definition comp(x y : nat): CompareSpecT (x=y) (x<y) (y<x) (nat_compare x y).
Proof.
  intros.
  apply CompareSpec2Type.
  apply nat_compare_spec.
Defined.

Ltac splitor :=
  match goal with H : _ \/ _ |- _ => destruct H end.

Hint Extern 200 => splitor; try subst; eauto.

(************************************************************************)

(* Find is pretty trivial, as one would expect:*)

Inductive fnd(x : nat)(f : ELN) : Type :=
| Found : forall {fl fr : ELN}, f=fl++^x++fr -> fnd x f
| NotFound : ENotIn x f -> fnd x f.

Hint Constructors fnd.

Definition find(x : nat){c}{n}{f}(t : rbtree c n f) : fnd x f.
Proof.
  induction t as [ |? ? ? ? ? ? ? ? ? IHtl d ? IHtr]; eauto.
  elim (comp x d); [|sinv IHtl|sinv IHtr]; xauto.
Defined.

(* OKins is a Prop that captures the input/output relationship of
Red-Black tree properties surrounding an insert operation.  OKinsFnd
represents finding the key already in the tree.  OKinsEQ represents an
insertion that leaves the color/black-height the same.  OKinsBR and
OKinsRB represent red->black and black->red conversions as a result of
the insertion.  The bool arg represents "found", and so is true only n
OKinsFnd.  The ELN arg is used by the ins return type to "build" the
input flattening. *)

Inductive OKins(x : nat) : bool -> ELN -> EC -> EN -> EC -> EN -> Prop :=
| OKinsFnd(c : EC)(n : EN) : OKins x true (^x) c n c n
| OKinsEQ(c : EC)(n : EN) : OKins x false [] c n c n
| OKinsBR(n : EN) : OKins x false [] EBlack n ERed n
| OKinsRB(n : EN) : OKins x false [] ERed n EBlack (ES n).

Hint Constructors OKins.

Lemma OKins1(x : nat)(fnd : bool)(fx : ELN)(n1 n2 : EN) :
  OKins x fnd fx EBlack n1 ERed n2 -> fnd=false /\ fx=[] /\ n1=n2.
Proof.
  intro oki. sinv oki.
Qed.

Lemma OKins2(x : nat)(fnd : bool)(fx : ELN)(n1 n2 : EN) :
  OKins x fnd fx ERed n1 EBlack n2 -> fnd=false /\ fx=[] /\ n2=ES n1.
Proof.
  intro oki. sinv oki.
Qed.

Lemma OKins3(x : nat)(fnd : bool)(fx : ELN)(c : EC)(n1 n2 : EN) :
  OKins x fnd fx c n1 c n2 -> n1=n2 /\ (fnd=true/\fx=^x \/ fnd=false/\fx=[]).
Proof.
  intro oki. sinv oki.
Qed.

Ltac autoOKins :=
  match goal with
      H : OKins _ _ _ _ _ _ _ |- _ =>
      first [apply OKins1 in H
            |apply OKins2 in H
            |apply OKins3 in H];
        simplify_hyps
  end.

(* Unlike OKNode, OKins is a Prop, and so has no runtime impact.  So,
why autoOKins?  Because it allows us to "invert" an OKins in a
non-Prop context in certain cases.  There are other ways to do this,
such as asserting the resulting conjunction of facts, which then
induces a Prop context where they can be proved.  The autoOKins tactic
just makes that more readable. *)


(* Inserting into a Red-Black tree, while requiring that the result
reflect the insertion properly.*)
Inductive ins(x : nat)(ci : EC)(ni : EN)(fi : ELN) : Type :=
  mkins(f1 fx f2 : ELN)(co : EC)(no : EN)(found : bool)
        (feq : fi=f1++fx++f2)
        (to : rbtree co no (f1++^x++f2))
        (oki : OKins x found fx ci ni co no)
  : ins x ci ni fi.

Hint Constructors ins.

Definition insert(x : nat){c : EC}{n : EN}{f : ELN}(t : rbtree c n f) :
  ins x c n f.
Proof.
  induction t as [ |? ? ? ? ? ? ? ok tl IHtl d tr IHtr].
  - change [] with ([]++[]++[]); eauto.
  - case (comp x d); intro; subst; eauto.
    + inversion IHtl as [? ? ? ? ? ? ? tl' oki]. subst. Eappnorm.
      case (ccomp tl tl'); intros; subst; autoOKins.
      * econstructor; [eauto|Eapp3; econstructor|]; simplify_hyps; eauto.
      * eelim (bal1 tl' d tr); eauto. intros c' t'. autoOKNode.
        econstructor; [eauto|xauto|csplit t'].
      * econstructor; [eauto|xauto|sinv ok; subst].
    + inversion IHtr as [? ? ? ? ? ? ? tr' oki]. subst. Eapp3.
      case (ccomp tr tr'); intros; subst; autoOKins.
      * econstructor; [eauto|xauto|sinv ok; simplify_hyps; eauto].
      * Eappnorm. eelim (bal2 tl d tr'); [|eauto]. intros c' t'. autoOKNode.
        Eapp3. econstructor; [eauto|xauto|csplit t'].
      * econstructor; [eauto|xauto|sinv ok; subst].
Defined.

(* OKd is a prop that captures the input/output relationship of
Red-Black tree properties surrounding a delete operation.  OKdEQ
represents no change in color/black-height.  OKdRB represents
red->black conversion.  OKdBS represents a decrease in black-height
while staying black.  These are the only combinations needed (found by
trial-and-errror) - adding or removing combinations results in
unprovable subgoals. *)
Inductive OKd : bool -> EC -> EN -> EC -> EN -> Prop :=
| OKdEQ(c : EC)(n : EN) : OKd false c n c n
| OKdRB(n : EN) : OKd false ERed n EBlack n
| OKdBS(n : EN) : OKd true EBlack (ES n) EBlack n.

Hint Constructors OKd.

Lemma OKd1(ni no : EN)(co : EC)(b : bool) : OKd b ERed ni co no -> ni=no /\ b=false.
Proof.
  intro ok. sinv ok.
Qed.

Lemma OKd2(ni no : EN)(co : EC) : OKd false EBlack ni co no -> ni=no/\co=EBlack.
Proof.
  intro ok. sinv ok.
Qed.

Lemma OKd3(ni no : EN)(co : EC) : OKd true EBlack ni co no -> ni=ES no/\co=EBlack.
Proof.
  intro ok. sinv ok.
Qed.

Lemma OKd4(ni no : EN)(ci : EC)(b : bool) : OKd b ci ni ERed no -> ni=no/\ci=ERed/\b=false.
Proof.
  intro ok. sinv ok.
Qed.

Lemma OKd5(ni no : EN)(ci co : EC) : OKd true ci ni co no -> ci=EBlack/\co=EBlack/\ni=ES no.
Proof.
  intro ok. sinv ok.
Qed.

Lemma OKd6(ni no : EN)(ci co : EC) : OKd false ci ni co no -> ni=no.
Proof.
  intro ok. sinv ok.
Qed.

Ltac autoOKd :=
  match goal with
      H : OKd _ _ _ _ _ |- _ =>
      first [apply OKd1 in H
            |apply OKd2 in H
            |apply OKd3 in H
            |apply OKd4 in H
            |apply OKd5 in H
            |apply OKd6 in H
            ];
        simplify_hyps
  end.

(*Deleting the minimum element from a Red-Black tree, if there is one.*)
Inductive dmin : EC -> EN -> ELN -> Type :=
  | nodmin : dmin EBlack E0 []
  | mkdmin(m : nat)(ci : EC)(ni : EN){co : EC}{no : EN}{f : ELN}(incbh : bool)
          (t : rbtree co no f)(ok : OKd incbh ci ni co no) : dmin ci ni (^m++f).

Hint Constructors dmin.

Definition delmin{c}{n}{f}(t : rbtree c n f) : dmin c n f.
Proof.
  induction t as [ |? ? ? ? ? ? ? ok tl IHtl d tr ?]; eauto.
  sinv IHtl.
  - csplit tr; try autoOKNode; eauto. sinv ok; subst; eauto.
  - intros to okdo. case (ccomp tl to); intros; subst;
    Eappnorm; try autoOKNode; try autoOKd; eauto.
    destruct incbh; autoOKd; eauto.
    csplit tr; try autoOKNode; eauto.
    elim (bal2 to d tr); eauto; intros c' t'. sinv ok; subst.
    + econstructor; eauto. csplit t'; eauto.
    + elim (blacken t'); intros ? ? n2n ?.
      econstructor; eauto. sinv n2n; subst; eauto.
Defined.

(*Deleting an arbitrary element from a Red-Black tree, if it exists in
the tree.*)
Inductive del(x : nat)(c : EC)(n : EN) : ELN -> Type :=
| delfnd{co : EC}{no : EN}{fl fr : ELN}(incbh : bool) : 
    rbtree co no (fl++fr) -> OKd incbh c n co no -> del x c n (fl++^x++fr)
| delnot{f : ELN} : ENotIn x f -> del x c n f.

Hint Constructors del.

(* Another attempt at automation with something like associative
unification - this one a bit more rigorous than xauto: *)
Ltac pauto := progress eauto.
Ltac zauto := 
  intros; try subst;
  solve [eauto
        |Eappnorm; pauto; zauto
        |Eapp3; pauto; zauto
        |Eappnorm; Eapp3; pauto; zauto
        |rewrite <- Eapp_assoc; pauto; zauto
        |econstructor; zauto
        |Eappnorm; econstructor; zauto
        |Eapp3; econstructor; zauto
        |Eappnorm; Eapp3; econstructor; zauto
        |rewrite <- Eapp_assoc; econstructor; zauto].

Definition delete(x : nat){c}{n}{f}(t : rbtree c n f) : del x c n f.
Proof.
  induction t as [ |? ? ? ? ? ? ? ? tl IHtl d tr IHtr]; eauto.
  elim (comp x d); intros; subst.
  - assert (D:=delmin tr). sinv D.
    + sinv ok; subst; eauto.
      elim (blacken tl). intros ? ? n2n ?. econstructor; eauto. sinv n2n; subst; eauto.
    + intros td okd. destruct incbh.
      * autoOKd. csplit tl; try autoOKNode; eauto.
        sinv ok; subst; eelim (bal1 tl m td); eauto; intros cb tb.
        { econstructor; eauto. csplit tb. }
        { eelim (blacken tb). intros ? ? n2n ?. econstructor; eauto. sinv n2n; subst; eauto. }
      * sinv ok; subst; autoOKd; eauto.
  - sinv IHtl; subst; eauto. intros td okd.
    case (ccomp tl td); intros; subst; Eappnorm.
    * destruct incbh; autoOKd.
      { csplit tr.
        - autoOKNode. econstructor; [rewrite <- Eapp_assoc; eapply bal3|]; xauto.
        - eelim (bal2 td d tr); Eappnorm; eauto. intros c' t'. sinv ok; subst.
          + econstructor; eauto. csplit t'.
          + elim (blacken t'). intros ? ? n2n ?. econstructor; eauto. sinv n2n; subst; eauto. }
      { zauto. }
    * autoOKNode. autoOKd. zauto.
    * autoOKd.
  - sinv IHtr; subst; eauto. intros td okd.
    case (ccomp tr td); intros; subst; Eapp3.
    * destruct incbh; autoOKd.
      { csplit tl.
        - autoOKNode. econstructor; [Eappnorm; eapply bal4|]; xauto.
        - eelim (bal1 tl d td); Eapp3; eauto. intros c' t'. sinv ok; subst.
          + econstructor; eauto. csplit t'.
          + elim (blacken t'). intros ? ? n2n ?. econstructor; eauto. sinv n2n; subst; eauto. }
      { zauto. }
    * autoOKNode. autoOKd. zauto.
    * autoOKd.
Defined.

(*The only assumption should be the Erasable_inj axiom:*)
Print Assumptions insert.
Print Assumptions find.
Print Assumptions delmin.
Print Assumptions delete.

(*The fully erased generated code:*)
Extraction Language Ocaml.
Set Printing Width 100.
Extraction "redblack.ml" insert find delmin delete.
