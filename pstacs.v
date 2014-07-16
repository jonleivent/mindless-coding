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

(* Proof-search tactics. *)

Ltac redundant T := 
  match goal with H:T, H':T |- _ => idtac end.

Ltac fail_if_redundant_hyp H := 
  match type of H with
      ?T => first [redundant T;fail 2|idtac]
  end.

Ltac posall := repeat match goal with
                         H : (forall (_ : ?A), _), I : ?A |- _ =>
                         let HI:=fresh H I in 
                         generalize (H I); intro HI; fail_if_redundant_hyp HI
                     end.

Ltac noforalls := repeat match goal with
                           | H : context[(forall (V : ?A), _)] |- _ => 
                             is_var V; clear H
                         end.

Ltac posit H :=
  repeat match type of H with 
             (forall (_ : ?A), _) =>
             match goal with 
                 I : ?A |- _ =>
                 let HI:=fresh H I in 
                 generalize (H I); intro HI; fail_if_redundant_hyp HI
             end
         end.

Ltac posall1 := repeat match goal with H:_|-_ => progress (posit H) end. (*same as posall*)
Ltac posall2 := repeat match goal with H:_|-_ => progress (posit H); clear H end.

Ltac unevar tac :=
  match goal with
    |H : _ |- context[?X] => 
     is_evar X; unify X H; solve [tac | unevar tac]
    |H : context[?T] |- context[?X] => 
     is_evar X; unify X T; solve [tac | unevar tac]
  end.
