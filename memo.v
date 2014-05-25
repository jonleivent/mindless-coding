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

The standard way to prevent a hint from causing auto/eauto to loop is
to pose a hypothesis after the hint is used, and prevent the hint from
being used if that hypothesis exists.  However, some hints should be
allowed to be used more than once, provided something else makes
progress on the goal in between each usage.  This memo mechanism
provides for such behavior by adding a hypothesis that remembers the
goal's consequent following the hint, and prevents the hint from being
used again until something else modifies the consequent so that it no
longer matches the memoed hypothesis.

*)

Inductive Memo(T : Type) : Type :=
  memo : Memo T.

Ltac memoGoal :=
  match goal with |- ?G => 
                  let H := fresh "goalmemo" in
                  assert (H:Memo G) by constructor
  end.

 (*Fail if there has been no progress on the consequent since it was
 memoized.*)
Ltac memoedGoalFail :=
  match goal with
    |  H : Memo ?G |- ?G => fail 1
    | |- _ => idtac
  end.

Ltac unMemo :=
  match goal with
      H : Memo _ |- _ => clear H 
  end.

Ltac doMemoed tac :=
  intros; memoedGoalFail; try unMemo; tac; memoGoal.

Tactic Notation "domemoed" tactic(tac) := doMemoed ltac:tac.
