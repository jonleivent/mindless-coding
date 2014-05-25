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

Require Export sorted.
Require Export solvesorted.
Export ListNotations.
Require Export erasable.
Export ErasableNotation.

Global Opaque app.
Global Opaque NotIn.

Section defs.
  Context {A : Type}.
  Context {ordA : Ordered A}.
  
  Definition Esorted := (liftP1 sorted).
  
  Definition Eapp := (lift2 (@app A)).

  Definition ENotIn(x : A) := liftP1 (NotIn x).
End defs.

Hint Extern 2 (ENotIn _ _) => unerase.

(* Some nice syntax for erasable lists.  Note the use of ^x instead
  of [x] - because for some reason [x] wouldn't work in all cases. *)
Infix "++" := Eapp (right associativity, at level 60) : EL_scope.
Notation " [ ] " := (# nil) : EL_scope.
Notation "^ x" := (# (cons x nil)) (at level 59) : EL_scope.
Delimit Scope EL_scope with eln.
Bind Scope EL_scope with Erasable.
Bind Scope list_scope with list.
Open Scope EL_scope.

(* Hint Extern 30 => unerase; simplify_hyps. *)

Section EL_lemmas.
  Context {A : Type}.

  Notation EL := (## (list A)).

  Lemma Eapp_assoc: forall {p q r : EL}, (p++q)++r=p++(q++r).
  Proof.
    intros.
    unerase.
    rewrite <- app_assoc.
    reflexivity.
  Qed.

  Lemma group3Eapp: forall (p q r s : EL), p++q++r++s=(p++q++r)++s.
  Proof.
    intros.
    rewrite ?Eapp_assoc.
    reflexivity.
  Qed.

  Lemma Eapp_nil_l : forall (l : EL), []++l=l.
  Proof.
    unerase.
    reflexivity.
  Qed.
  
  Lemma Eapp_nil_r : forall (l : EL), l++[]=l.
  Proof.
    unerase.
    intros.
    rewrite app_nil_r.
    reflexivity.
  Qed.

End EL_lemmas.

Require Import memo.

Create HintDb Reassoc discriminated.

(* The following tactic steps through all top-level associations:

Ltac reassociate_step :=
  match goal with
      |- _ (?A++?B++?C) =>
      rewrite <- Eapp_assoc; pattern (A++B);
      match goal with
          |- ?F (A++B) =>
          let H:=fresh in
          set (H:=F); rewrite ?Eapp_assoc; subst H; cbv beta
      end
  end.

But, as a hint, it's considerably slower than the following 4 hints
that only examine the re-associations needed by the tree proofs.  *)

Hint Extern 996 => match goal with |- _ (_++_) =>
                                   domemoed rewrite !Eapp_assoc end : Reassoc.
Hint Extern 997 => match goal with |- _ (_++_) =>
                                   domemoed rewrite !Eapp_assoc; rewrite group3Eapp end : Reassoc.
Hint Extern 998 => match goal with |- _ (_++_) =>
                                   domemoed rewrite group3Eapp end : Reassoc.
Hint Extern 999 => match goal with |- _ (_++_) =>
                                   domemoed rewrite <- Eapp_assoc end : Reassoc.

Ltac zauto := typeclasses eauto with core Reassoc.

(**********************************************************************)

Notation EN := (## nat).

Definition ES := (lift1 S).

Ltac denil1 := 
  match goal with
    | H : context[[]++_] |- _ => rewrite Eapp_nil_l in H
    | H : context[_++[]] |- _ => rewrite Eapp_nil_r in H
    | |- context[[]++_] => rewrite Eapp_nil_l
    | |- context[_++[]] => rewrite Eapp_nil_r
  end.
  
Hint Extern 900 => denil1.

Ltac denil := repeat denil1.
