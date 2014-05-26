

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

type sumbool =
| Left
| Right

type 'a eqDec = 'a -> 'a -> sumbool

type 'a ordered = { eq_dec : 'a eqDec; compare : ('a -> 'a -> comparison); compare_spec : ('a -> 'a -> compareSpecT) }

val compare_spec : 'a1 ordered -> 'a1 -> 'a1 -> compareSpecT

type a (* AXIOM TO BE REALIZED *)

val ordA : a ordered

type color =
| Red
| Black

type rbtree =
| Leaf
| Node of color * rbtree * a * rbtree

type findResult =
| Found
| NotFound

val find : a -> rbtree -> findResult

val cof : rbtree -> color

val midRedCombine : rbtree -> a -> rbtree -> a -> rbtree -> rbtree

val red2black : rbtree -> rbtree

type iChanged =
| ISameIndx
| IReddened
| IBlackInc

val rebalRight : rbtree -> a -> rbtree -> ( * )

val rebalLeft : rbtree -> a -> rbtree -> ( * )

val color2change : color -> iChanged

type insertResult =
| FoundByInsert
| Inserted of iChanged * rbtree

val insert : a -> rbtree -> insertResult

type dChanged =
| StillFits
| Rebalance

val dRotateLeft : rbtree -> a -> rbtree -> rbtree

val dRotateRight : rbtree -> a -> rbtree -> rbtree

val color2dchange : color -> dChanged

val colorAs : color -> rbtree -> rbtree

val dRebalRight : color -> rbtree -> a -> rbtree -> ( * )

val dRebalLeft : color -> rbtree -> a -> rbtree -> ( * )

val dFitLeft : color -> ( * ) -> a -> rbtree -> ( * )

val dFitRight : color -> rbtree -> a -> ( * ) -> ( * )

val colorFit : color -> rbtree -> ( * )

type delminResult =
| NoMin
| MinDeleted of a * ( * )

val delmin : rbtree -> delminResult

type deleteResult =
| DelNotFound
| Deleted of ( * )

val delete : a -> rbtree -> deleteResult

