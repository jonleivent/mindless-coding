

type 'a option =
| Some of 'a
| None

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

type a (* AXIOM TO BE REALIZED *)

val ordA : a ordered

type gap =
| G1
| G0

type gaptree =
| Leaf
| Node of gap * gaptree * a * gaptree

type findResult =
| Found
| NotFound

val find : a -> gaptree -> findResult

val gof : gaptree -> gap option

val setGap : gap -> gaptree -> gaptree

type regapR =
  gaptree
  (* singleton inductive, whose constructor was regapR *)

val regapAs : gaptree -> gaptree -> regapR

val gofis : gaptree -> gap -> bool

type gapnode =
  gaptree
  (* singleton inductive, whose constructor was Gapnode *)

type ires =
| ISameH
| Higher

type insertResult =
| FoundByInsert
| Inserted of gaptree * ires

val rotateRight : gaptree -> a -> gaptree -> gap -> gapnode

val rotateLeft : gaptree -> a -> gaptree -> gap -> gapnode

val iFitLeft : gap -> gaptree -> gaptree -> a -> gaptree -> insertResult

val iFitRight : gap -> gaptree -> a -> gaptree -> gaptree -> insertResult

val insert : a -> gaptree -> insertResult

type dres =
| DSameH
| Lower

type tryLowerResult =
| Lowered of gaptree
| LowerFailed

val tryLowering : gaptree -> tryLowerResult

val dRotateLeft : gaptree -> a -> gaptree -> gap -> gapnode

type delminResult =
| NoMin
| MinDeleted of a * ( * )

val dFitLeft : gap -> gaptree -> gaptree -> a -> gaptree -> ( * )

val delmin : gaptree -> delminResult

val dRotateRight : gaptree -> a -> gaptree -> gap -> gapnode

val dFitRight : gap -> gaptree -> a -> gaptree -> gaptree -> ( * )

type delmaxResult =
| NoMax
| MaxDeleted of a * ( * )

val delmax : gaptree -> delmaxResult

type deleteResult =
| DelNotFound
| Deleted of ( * )

type twoGaps =
| NoneNone
| G0G0
| G1G1
| NoneG0
| G1G0
| G0None
| G0G1

val gof2 : gaptree -> gaptree -> twoGaps

val delMinOrMax : gap -> gaptree -> a -> gaptree -> ( * )

val delete : a -> gaptree -> deleteResult

