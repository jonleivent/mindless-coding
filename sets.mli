

type __ = Obj.t

type comparison =
| Eq
| Lt
| Gt

type compareSpecT =
| CompEqT
| CompLtT
| CompGtT

type 'a eqDec = 'a -> 'a -> bool

type 'a ordered = { eq_dec : 'a eqDec; compare : ('a -> 'a -> comparison);
                    compare_spec : ('a -> 'a -> compareSpecT) }

val compare_spec : 'a1 ordered -> 'a1 -> 'a1 -> compareSpecT

type ('a, 'tree) breakResult =
| BreakLeaf
| BreakNode of 'tree * 'a * 'tree

type ('a, 'tree) insertResult =
| InsertFound
| Inserted of 'tree

type ('a, 'tree) delminResult =
| DelminLeaf
| DelminNode of 'a * 'tree

type ('a, 'tree) delmaxResult =
| DelmaxLeaf
| DelmaxNode of 'a * 'tree

type ('a, 'tree) deleteResult =
| DelNotFound
| Deleted of 'tree

type 'a tree = { leaf : __; break : (__ -> __ -> ('a, __) breakResult);
                 insert : ('a -> __ -> __ -> ('a, __) insertResult);
                 join : (__ -> __ -> 'a -> __ -> __ -> __ -> __);
                 delmin : (__ -> __ -> ('a, __) delminResult);
                 delmax : (__ -> __ -> ('a, __) delmaxResult);
                 delete : ('a -> __ -> __ -> ('a, __) deleteResult) }

type 'a tree0 = __

val leaf : 'a1 ordered -> 'a1 tree -> 'a1 tree0

val break :
  'a1 ordered -> 'a1 tree -> 'a1 tree0 -> ('a1, 'a1 tree0) breakResult

val join :
  'a1 ordered -> 'a1 tree -> 'a1 tree0 -> 'a1 -> 'a1 tree0 -> 'a1 tree0

val delmin :
  'a1 ordered -> 'a1 tree -> 'a1 tree0 -> ('a1, 'a1 tree0) delminResult

val enat_xrect : (__ -> (__ -> __ -> 'a1) -> 'a1) -> 'a1

type a (* AXIOM TO BE REALIZED *)

val ordA : a ordered

val treeA : a tree

type findResult =
| Found
| NotFound

val find : a -> a tree0 -> findResult

type splitResult =
| Split of bool * a tree0 * a tree0

val split : a -> a tree0 -> splitResult

type unionResult =
  a tree0
  (* singleton inductive, whose constructor was UnionResult *)

val union : a tree0 -> a tree0 -> unionResult

val delete_free_delmin : a tree0 -> (a, a tree0) delminResult

val merge : a tree0 -> a tree0 -> a tree0

type intersectResult =
  a tree0
  (* singleton inductive, whose constructor was IntersectResult *)

val intersection : a tree0 -> a tree0 -> intersectResult

type setdiffResult =
  a tree0
  (* singleton inductive, whose constructor was SetDiffResult *)

val setdifference : a tree0 -> a tree0 -> setdiffResult

type filterResult =
  a tree0
  (* singleton inductive, whose constructor was Filtered *)

val filter : (a -> bool) -> a tree0 -> filterResult

type partitionResult =
| Partitioned of a tree0 * a tree0

val partition : (a -> bool) -> a tree0 -> partitionResult

