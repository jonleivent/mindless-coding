

type __ = Obj.t

type nat =
| O
| S of nat

type comparison =
| Eq
| Lt
| Gt

type compareSpecT =
| CompEqT
| CompLtT
| CompGtT

type 'a sig0 =
  'a
  (* singleton inductive, whose constructor was exist *)

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
                 join : (__ -> __ -> 'a -> __ -> __ -> __ -> __); delmin : (__ -> __ -> ('a, __) delminResult);
                 delmax : (__ -> __ -> ('a, __) delmaxResult); delete : ('a -> __ -> __ -> ('a, __) deleteResult) }

type a (* AXIOM TO BE REALIZED *)

val ordA : a ordered

type gap =
| G1
| G0

type gaptree =
| Leaf
| Node of gap * gaptree * a * gap * gaptree

type findResult =
| Found
| NotFound

val find : a -> gaptree -> findResult

val isLeaf : gaptree -> bool

type gapnode =
  gaptree
  (* singleton inductive, whose constructor was Gapnode *)

type ires =
| ISameH
| Higher

type insertResult0 =
| FoundByInsert
| Inserted0 of gaptree * ires

val iRotateRight : gaptree -> a -> gaptree -> gapnode

val iFitLeft : gap -> gap -> gaptree -> a -> gaptree -> insertResult0

val iRotateLeft : gaptree -> a -> gaptree -> gapnode

val iFitRight : gap -> gap -> gaptree -> a -> gaptree -> insertResult0

val insert0 : a -> gaptree -> insertResult0

type dres =
| DSameH
| Lower

type tryLowerResult =
| Lowered of gaptree
| LowerFailed

val tryLowering : gaptree -> tryLowerResult

val gflip : gap -> gap

val dRotateLeft : gaptree -> a -> gaptree -> gapnode

type delminResult0 =
| NoMin
| MinDeleted of a * ( * )

val dFitLeft : gap -> gap -> gaptree -> a -> gaptree -> ( * )

val delmin0 : gaptree -> delminResult0

val dRotateRight : gaptree -> a -> gaptree -> gapnode

val dFitRight : gap -> gap -> gaptree -> a -> gaptree -> ( * )

type delmaxResult0 =
| NoMax
| MaxDeleted of a * ( * )

val delmax0 : gaptree -> delmaxResult0

val delMinOrMax : gap -> gap -> gaptree -> a -> gaptree -> ( * )

type deleteResult0 =
| DelNotFound0
| Deleted0 of ( * )

val delete0 : a -> gaptree -> deleteResult0

val g2h : nat -> gap -> nat

type jres =
| JSameH
| JHigher

type joinResult =
| JoinResult of nat * gaptree * jres

val joinle : nat -> gaptree -> a -> nat -> gaptree -> joinResult

val joinge : nat -> gaptree -> a -> nat -> gaptree -> joinResult

val join0 : nat -> gaptree -> a -> nat -> gaptree -> joinResult

type gaphtree =
| Gaphtree of nat * gaptree

val gaphtree_tree : a tree

