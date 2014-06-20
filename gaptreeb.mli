

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

type a (* AXIOM TO BE REALIZED *)

val ordA : a ordered

type gap =
| G1
| G0

type gaptree =
| Leaf
| Node of gap * gaptree * a * gap * gaptree

val isLeaf : gaptree -> bool

type gapnode =
  gaptree
  (* singleton inductive, whose constructor was Gapnode *)

type ires =
| ISameH
| Higher

type insertResult =
| FoundByInsert
| Inserted of gaptree * ires

val iRotateRight : gaptree -> a -> gaptree -> gapnode

val iFitLeft : gap -> gap -> gaptree -> a -> gaptree -> insertResult

val iRotateLeft : gaptree -> a -> gaptree -> gapnode

val iFitRight : gap -> gap -> gaptree -> a -> gaptree -> insertResult

val insert : a -> gaptree -> insertResult

type dres =
| DSameH
| Lower

type tryLowerResult =
| Lowered of gaptree
| LowerFailed

val tryLowering : gaptree -> tryLowerResult

val gflip : gap -> gap

val dRotateLeft : gaptree -> a -> gaptree -> gapnode

type delminResult =
| NoMin
| MinDeleted of a * ( * )

val dFitLeft : gap -> gap -> gaptree -> a -> gaptree -> ( * )

val delmin : gaptree -> delminResult

val dRotateRight : gaptree -> a -> gaptree -> gapnode

val dFitRight : gap -> gap -> gaptree -> a -> gaptree -> ( * )

type delmaxResult =
| NoMax
| MaxDeleted of a * ( * )

val delmax : gaptree -> delmaxResult

val delMinOrMax : gap -> gap -> gaptree -> a -> gaptree -> ( * )

type deleteResult =
| DelNotFound
| Deleted of ( * )

val delete : a -> gaptree -> deleteResult

