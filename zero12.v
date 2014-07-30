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

(* The main example is below - skip these preliminaries by searching
down to "main act" *)

Require Import ZArith.
Require Import ExtrOcamlBasic.
Require Export erasable.
Import ErasableNotation.
Open Scope Z_scope.
Opaque Z.mul.

Infix "^" := Zpower_nat : Z_scope. (*let's just use boring nat exponents*)

(* A comprehension notation for erasable terms, still a work in
progress.  It certainly looks nicer than a bunch of nested lets, and
orgainizes things in the right order - the principle term comes first.
I'm not sure if the notations are compatible with other things,
though.  That's something Coq doesn't tell you.

The main form of this notation is a term like (f x y |# x <- x').  The
interpretation of this term is that it is the erasable value formed by
the function call (f x y) where f isn't itself erasable, and neither
are its arguments x or y, but x' is erasable, and is used to bind x (y
remains free).  The shorthand (f x' y |#<x') means the same thing, but
only works when x' is a variable name, while the general form works
for any erasable term x'.  Note that Coq won't use this shorthand when
printing, because it renames bound variables. *)
Notation "f |# v <- x" := (let (v) := x in #f)
                            (at level 199, left associativity) : Erasable_scope.
Notation "f |# < v" := (f |# v <- v) (*shorthand*)
                         (at level 199, left associativity) : Erasable_scope.

(******************************************************************************)

(* Some (mostly) general purpose tactics to help with this example -
and not to be considered part of theexample itself (in other words, a
mindless-coding practitioner shouldn't need to write tactics like
these - but a developer of mindless-coding techniques has to) *)

(* First, some very general-purpose tactics for simple dealings with
evars:*)

Ltac name_evars id := 
  repeat match goal with |- context[?V] => is_evar V; let H := fresh id in set (H:=V) in * end.

Ltac assign name term :=
  match goal with H := ?V : _ |- _ => match H with name => unify V term end end.

Ltac subst_evars :=
  repeat match goal with H := ?V : _ |- _ => has_evar V; subst H end.

(*Some comprehensions don't simplify on their own - they need a little
prodding:*)
Create HintDb liftRs.

Ltac simplify_comprehension :=
  autounfold with liftRs; hnf;
  try
    let T:=fresh in
    let Q:=fresh in
    let R:=fresh in
    evar (T:Type); evar(Q:T); subst T;
    match goal with 
        |- context[?G] =>
        match G with (let '(erasable _) := _ in _) =>
                     assert (G = Q) as R by (subst Q; unerase; reflexivity)
        end
    end;
    subst Q; rewrite R; clear R.

(* Ring_simplify doesn't know about exponents - fortunately, all we
need to help it with is 2^0 *)
Lemma Twoto0 : 2^0 = 1.
Proof. compute. reflexivity. Qed.

Ltac ring_simplify' := rewrite ?Twoto0; ring_simplify.

(* Tactics to skolemize erasable evars over erasable hypotheses.  We
need to skolemize in these cases because the unerase tactic, which
permits the solution of erasable goals, would normally render evars
un-unifiable with the necessary terms found by such a solution.*)

Ltac funify_evar :=
  match goal with
      H := ?V : ?T, H' : ?T' |- _ =>
           match type of H with
               (##_) =>
               match V with
                   context[?eV] =>
                   is_evar eV;
                     match V with
                       | context[H'] => fail 1
                       | _ => idtac
                     end;
                     match type of H' with
                         (##?W') =>
                         match type of eV with
                             ?VT =>
                             let f:=fresh in
                             evar (f:W'->VT); unify eV (let (x):=H' in f x)
                         end
                     end
               end
           end
    end.

Definition liftR1{T1 T2}
           (f:T1->T2)(x:T1) := #(f x).
Definition liftR2{T1 T2 T3}
           (f:T1->T2->T3)(x1:T1)(x2:T2) := #(f x1 x2).
Definition liftR3{T1 T2 T3 T4}
           (f:T1->T2->T3->T4)(x1:T1)(x2:T2)(x3:T3) := #(f x1 x2 x3).
Definition liftR4{T1 T2 T3 T4 T5}
           (f:T1->T2->T3->T4->T5)(x1:T1)(x2:T2)(x3:T3)(x4:T4)
  := #(f x1 x2 x3 x4).

Hint Unfold liftR1 liftR2 liftR3 liftR4 : liftRs.

Ltac unirefl := (* a more powerful reflexivity tactic *)
  match goal with
    |- ?X = ?Y => unify X Y; reflexivity
  end.

Ltac liftrify_funies :=
  match goal with
      H : ?V : _, H' := ?eV : _ |- _ =>
      match type of H with 
          (##_) => 
          match V with 
              context[eV] => 
              is_evar eV;
              let T:=fresh in
              let Q:=fresh in
              let R:=fresh in
              evar(T:Type); evar(Q:T);
              first [assert (H'=(liftR4 Q)) as R by (subst H' Q;unirefl)
                    |assert (H'=(liftR3 Q)) as R by (subst H' Q;unirefl)
                    |assert (H'=(liftR2 Q)) as R by (subst H' Q;unirefl)
                    |assert (H'=(liftR1 Q)) as R by (subst H' Q;unirefl)];
              subst Q T H'; clear R
          end
      end
  end.

Ltac skolemize_evars_for_unerase :=
  let Evar0 := fresh in
  name_evars Evar0; repeat funify_evar; repeat liftrify_funies; subst_evars.

(* Solving function equalities, including parts resulting from the
above skolemization tactics: *)

Ltac fpatternl :=
  lazymatch goal with
  |- ?lhs = ?rhs ?v =>
  let lhs' := (eval pattern v in lhs) in
  change (lhs' = rhs v)
end.

Lemma fchop{T1 T2}(f g:T1->T2)(x : T1) : f = g -> f x = g x.
Proof. intros. subst. reflexivity. Qed.

Ltac solve_skolem_function := repeat (try unirefl; fpatternl; apply fchop).

Ltac solve_funeq := 
  subst_evars;
  repeat (progress f_equal); try solve_skolem_function; try unirefl.

(*... and on to the "main act":*)

(******************************************************************************)
(* A simple demo of mindless-coding using the example of a redundant
binary counting system.  This redundant binary number system is
mentioned in:

"A programming and problem-solving seminar" by MJ Clancy and DE Knuth:

http://i.stanford.edu/pub/cstr/reports/cs/tr/77/606/CS-TR-77-606.pdf

as well as near the end of the paper:

"Purely Functional Representations of Catenable Sorted Lists" 
by H Kaplan and RE Tarjan.

and also in Chris Okasaki's PhD. thesis and the resulting book on
"Purely Functional Data Structures".

Briefly (for more context, check out one of the above), the redundant
binary counting system presented here makes the increment operation
have O(1) worst-case time complexity, instead of the normal O(logN)
worst-case (although O(1) amortized) time complexity it would have in
a standard binary system (N is the number being represented in the
system, so logN is the number of bits).  It does this by adding
redundant information into the data structure that is used to keep
track of partial operations - in this case, a partially transmitted
carry bit.  One way to think of the data structure is that each "bit",
instead of just encoding the values zero or one, can encode zero, one
or two

The inductive types zot and zot' (ZOT : Zero One Two - the latter
primed type is an internal component of the former) are specified
using dependent types in a fully constrained way, such that the
expected value (as a Z, not a nat, just to simplify the treatment of
subtraction) and additional structural constraints (whether the
current "bit" is a 2 or not) are components of the types.

As with other mindless-coding cases, the point of the
fully-constrained type specification is not just verification - but
also the additional benefit of having the proof assistant (Coq, in
this case) guide the development of function implementations in such a
way as to simplify the mental effort required of the programmer
(although often at the cost of some low-mental-effort drudgery - in
this case, helping Coq solve middle-school-level algebraic equations).

This example also showcases some new developments I am experimenting
with.  One is a new "comprehension" notation for erasable terms - this
hopefully make things easier to read (mostly steps during the proofs,
but also the type specifications themselves), and otherwise has no
semantic impact.  The second is a "skolemization" technique that is an
attempt to get around a peculairity with Coq: its issue with
instantiation of existential variables (evars - the ?number terms that
appear occassionally in proofs).  The skolemization used in this
example is not a general solution - it is only for handling the
specific case of evars of erasable types skolemized over hypotheses of
erasable types.

This example uses a trunk (development) version of Coq as of July 30,
2014.  I encourage those interested in mindless coding to single step
through the proofs of de2 and inczot below.

*)

(* First, some algebraic convenience functions: *)

(* Multiply x by a power of 2 and fill the opening with 1's *)
Definition mp2a1s(x : Z)(n : nat) := x * 2^n + (2^n-1).

Hint Unfold mp2a1s.

(* A zot' will represent the following value: *)
Definition zotval(n1s : nat)(is2 : bool)(next_value : Z) : Z :=
  2 * mp2a1s next_value n1s + if is2 then 2 else 0.

Hint Unfold zotval.

(* zot' will represent the non-lowest bits of a zot.  A zot' is
chained in least-significant-bit-at-head form. 

A minor note on the choice of type parameter-based constraints (which
adds the equalities iseq and veq to Zot') vs. type index-based
constraints.  The parameter-based constraints allow the proof to use
the better-behavied (with regard to naming new hypotheses) Coq tactic
"case" instead of Coq's inversion tactics.  Otherwise, there's not
much of a difference - I've used type indexes and inversion in other
examples (the AVL, red-black and gap trees).  

Also, recall that erasable types are prefixed by the "##" operator,
and erasable values by the "#" oerator.  (in other examples, I used
Coq Notations to abbreviate some of these cases, but have not done so
here).
*)
Inductive zot'(eis2 : ##bool)(value : ##Z) : Set :=
| Zot'(is2 : bool)
      (iseq : eis2=#is2)
      {next_is2 : ##bool}
      (ok : is2=true -> next_is2=#false)
      {next_value : ##Z}
      (n1s : nat)
      (veq : value = (zotval n1s is2 next_value |#<next_value))
      (next : zot' next_is2 next_value)
  : zot' eis2 value.
  
(*De-2 a zot' - meaning, make its head (least-significant bit) not a
2, but otherwise keep its value the same.  We'll implement this
"mindlessly" - meaning that we won't direct the proof to a specific
solution we determined in advance, and instead allow the interactive
elaboration of the proof, under the constraints of the fully-specified
dependent types, get us there with minimal mental exertion on our
part. *)
Definition de2{eis2 value}(z : zot' eis2 value) : zot' #false value.
Proof.
  (*Crack open z*)
  case z.
  intros is2 iseq next_is2 ok next_value n1s veq next. subst.
  (*Obviously, what we do is going to depend on whether is2 is already
  false*)
  destruct is2.
  - specialize (ok eq_refl). subst.
    (*The main case - We could start by examining n1s or next.  Let's
    start with n1s to see if we can solve some subgoals without moving
    onto that next zot'. *)
    destruct n1s.
    + (* As we proceed, we will figure out later that we need to break
      open next - because otherwise there's just not enough info to
      solve the subgoal.  But breaking open next will introduce new
      hypotheses, and we need to make sure they are introduced before
      any evars crop up.  Skolemization would help, but the tactics
      above only skolemize over erasable hypotheses, and next isn't
      erasable.  We could use a more general skolemization, but it's
      still being developed, and it would probably make the proof much
      messier.  The limited over-erasables-only skolemization used
      here is sufficient to illustrate the usefullness of
      skolemization as a workaround for Coq's evar instantiation
      issues.  *)
      case next.
      intros is2' iseq' next_is2' ok' next_value' n1s' veq' next'. subst.
      (* Now, start building a solution:*)
      econstructor.
      (* This is "iseq : eis2=#is2" - which should always be trivially
      true:*)
      reflexivity.
      (* This is the "ok" field, which we should only solve when we
      can do so without having to fill in any evars, as we can do here
      because of the obviously contradictory false=true hypothesis.
      Why not just always solve this immediately?  Because stuffing
      values into evars in unconstrained subgoals (meaning, where
      multiple different values would work) could prevent the solution
      of constrained subgoals later:*)
      discriminate.
      (* This is the "veq" field, where we will focus most of our
      attention - since it's the primary constraint governing the
      value of the zots involved.  However, we need to "unerase" the
      goal in order to solve it, because the consequent as well as
      some hypotheses we need are erased.  Fortunately, because this
      is a Prop context, the unerase tactic is available.*)
      (* Before we use unerase, we need to skolemize any erasable
      evars in the goal so that they remain instantiatable
      afterwards. *)
      skolemize_evars_for_unerase.
      unerase. subst. 
      (*Name the evars, so that they don't appear as ?num's in the
      consequent, because that upsets ring_simplify.  Naming them also
      gives us easy access should we need to provide them with values
      later. *)
      name_evars e.
      (* Note skolem function evar e0, and how it was skolemized over
      nest_is2' and next_value' in the consequent, which were the only
      two erasable hypotheses prior to using unerase. *)
      (* We're ready to start working on this value-equation - first
      unfold the functions, and give our slightly-improved
      ring_simplify tactic a chance to make it look nicer:*)
      autounfold.
      ring_simplify'.
      (* Do some algebraic manipulations to get the equation into a
      solvable form - which requires that "like" parts in the lhs and
      rhs line up.  It would be nice if ring_simplify did this for us,
      but it has a slightly different agenda.  However, it should be
      possible to develop a tactic like ring_simplify that would get
      things into the right form, or at least closer to it, on its
      own.  But, none of the manipulations here should be surprising
      to anyone who has a vague memory of basic middle-school-level
      algebra.  Why sometimes rewrite vs. setoid_rewrite?  That's a
      Coq weirdness/annoyance - it treats the occurrence "at num"
      clauses differently in rewrite vs. setoid_rewrite. *)
      rewrite Z.sub_cancel_r.
      rewrite <-Z.mul_assoc.
      setoid_rewrite Z.mul_comm at 2.
      rewrite Z.mul_assoc.
      change 4 with (2*2).
      setoid_rewrite <-Z.mul_assoc at 2.
      setoid_rewrite <-Z.mul_assoc at 2.
      rewrite <-Zpower.Zpower_nat_succ_r.
      setoid_rewrite <-Z.mul_assoc at 2.
      setoid_rewrite Z.mul_comm at 7.
      setoid_rewrite Z.mul_assoc at 3.
      (* Everything is sufficiently lined up now.  Coq can do the rest
      automatically: *)
      solve_funeq.
      simplify_comprehension.
      (* That looks familiar!  That evar in the consequent is the one
      we didn't solve from the ok field - which leaves us with the
      flexibility to just do this now:*)
      eassumption.
    + (* Second verse, same as the first...*)
      econstructor.
      reflexivity.
      discriminate.
      skolemize_evars_for_unerase.
      unerase. name_evars e.
      autounfold.
      ring_simplify'.
      (* OK - not quite the same. *)
      (* Notice that the rhs has a constant term (- 2), while the lhs
      does not - which means we need to cancel out that constant term
      with what we can, such as by:*)
      assign e 0%nat. subst e. ring_simplify'.
      (* Algebraic maniuplations again to get things to line up. *)
      rewrite <-?Z.mul_assoc.
      rewrite <-Z.mul_add_distr_l.
      (* Everything is sufficiently lined up now. *)
      solve_funeq.
      simplify_comprehension.
      (* But, unlike the first verse, we're left with a zot' that
      isn't immediately available - so we need to contruct it...*)
      econstructor.
      reflexivity.
      (*Don't know how to solve this ok field yet, so swap it*)
      all:swap 1 2.
      skolemize_evars_for_unerase.
      unerase. name_evars e.
      autounfold.
      ring_simplify'.
      (* Again, a constant term on the rhs but none on the lhs - this
      time we can cancel it out using that very convenient if term:*)
      assign e0 true. subst e0. ring_simplify'.
      (* Everything is sufficiently lined up. *)
      solve_funeq.
      (*We can't solve this eis2 by discriminate - so we have no
      choice but to fill in the evar with #false: *)
      reflexivity.
      simplify_comprehension.
      (*Good news, the required zot' is at hand.*)
      eassumption.
  - (*This is just the is2=false case, so we don't need to do anything
    to make it false*)
    assumption.
Qed.

(* And we get this - note how erasability makes this look nice - all
that nasty algebra and constraint fields are gone.  But, most
importantly, we didn't need to know how to implement de2 prior to
interactively developing it.  Instead, with the help of the
fully-constrained zot' type, and under the guidance of an interactive
proof assistant/type checker (Coq), we uncovered an implementation by
solving small low-mental-effort steps (middle-school-level algebra
in this case).  The constraints both force the resulting
implementation to be just what we want, and correct as well. *)
Extraction de2.

(*zot wraps zot', since the head (least significant bit) is slightly
different from the rest - it's never 2.  We could re-use zot', but
we'd have to alter its semantics just for this head case - so why not
just make a new type for that.  *)
Inductive zot(value : ##Z) : Set :=
| Zot(n1s : nat)
     {next_value : ##Z}
     (veq : value = (mp2a1s next_value n1s |#<next_value))
     (next : zot' #false next_value)
  : zot value.

(*Increment a zot, using the same mindless-coding techniques.
However, keep in mind that we can use de2 when we need it. *)
Definition inczot{value}(z : zot value) : zot (value+1 |#<value).
Proof.
  case z.
  intros n1s next_value veq next. subst.
  destruct n1s.
  - case next.
    intros is2' iseq' next_is2' ok' next_value0' n1s' veq' next'. subst.
    econstructor.
    skolemize_evars_for_unerase.
    unerase. subst. name_evars e.
    autounfold.
    ring_simplify'.
    rewrite Z.sub_cancel_r.
    rewrite <-Z.mul_assoc.
    setoid_rewrite Z.mul_comm at 2.
    rewrite Z.mul_assoc.
    rewrite <-Zpower.Zpower_nat_succ_r.
    rewrite Z.mul_comm.
    solve_funeq.
    simplify_comprehension.
    (* We don't have this exactly (next'), but de2 can help:*)
    eapply de2.
    eassumption.
  - econstructor.
    skolemize_evars_for_unerase.
    unerase. name_evars e.
    autounfold.
    ring_simplify'.
    (* Another case with a constant term on only one side that we have
    to cancel out: *)
    assign e0 0%nat. subst e0. ring_simplify'.
    solve_funeq.
    simplify_comprehension.
    (* We only solved stuff above if the eis2 arg to zot' was an evar
    (meaning, unconstrained) - so it's a good guess that will remain
    the case.  Use de2 to make it an evar.  We could always try to
    solve things without using de2 here - and see if we can (we
    can't). *)
    eapply de2.
    econstructor.
    reflexivity.
    all:swap 1 2.
    skolemize_evars_for_unerase.
    unerase. name_evars e.
    autounfold.
    ring_simplify'.
    assign e0 true. subst e0. ring_simplify'.
    solve_funeq.
    reflexivity.
    simplify_comprehension.
    eassumption.
Qed.

(*I'm encouraging you to step through the above yourself, and so am
not extracting to a .ml file!*)
Recursive Extraction inczot.
(* Note how similar inczot is to de2 in the output.  Even though
inczot is incrementing the value while de2 is keeping it the same,
they amount to doing very similar things, because propagating a carry
bit - which is what de2 is doing - amounts to incrementing a later
zot' in the chain.  So, maybe we could have saved a tiny amount of
code if we knew that in advance.  No big deal. *)
