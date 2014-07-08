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

  A rough draft of a typeclass for generic trees.  Note that "find" is
  omitted - because it can be defined using just break on generic
  trees just as well.  Maybe it should then get a default
  implementation in the typeclass itself?

*)

Require Export common.

Section results.
  Context {A : Type}.
  Notation EL := (##(list A)).

  Variable tree : EL -> Type.

  (*Keep result inductive types index-less so that they analyze easily:*)

  Inductive breakResult(f : EL) : Type :=
  | BreakLeaf : f=[] -> breakResult f
  | BreakNode{fl}(tl : tree fl)(d : A){fr}(tr : tree fr) : f=fl++^d++fr -> breakResult f.

  Inductive insertResult(x : A)(f : EL) : Type :=
  | InsertFound{fl fr} : f=fl++^x++fr -> insertResult x f
  | Inserted{fl fr}(t : tree (fl++^x++fr)) : f=fl++fr -> insertResult x f.

  Inductive delminResult(f : EL) : Type :=
  | DelminLeaf : f=[] -> delminResult f
  | DelminNode(m : A){f'}(t : tree f') : f=^m++f' -> delminResult f.

  Inductive delmaxResult(f : EL) : Type :=
  | DelmaxLeaf : f=[] -> delmaxResult f
  | DelmaxNode(m : A){f'}(t : tree f') : f=f'++^m -> delmaxResult f.

  Inductive deleteResult(x : A)(f : EL) : Type :=
  | DelNotFound{ni : ENotIn x f} : deleteResult x f
  | Deleted{fl fr}(t : tree (fl++fr)) : f=fl++^x++fr -> deleteResult x f.
  
End results.

Class Tree (A : Type){ordA : Ordered A} : Type :=
  { tree     : ##(list A) -> Type;
    leaf     : tree [];
    isSorted : forall {f}(t : tree f), Esorted f;
    break    : forall {f}(t : tree f), breakResult tree f;
    insert   : forall (x : A){f}(t : tree f), insertResult tree x f;
    join     : forall {fl}(tl : tree fl)(d : A){fr}(tr : tree fr)
               {s : Esorted(fl++^d++fr)}, tree (fl++^d++fr);
    delmin   : forall {f}(t : tree f), delminResult tree f;
    delmax   : forall {f}(t : tree f), delmaxResult tree f;
    delete   : forall (x : A){f}(t : tree f), deleteResult tree x f
  }.

