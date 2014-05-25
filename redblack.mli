

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

type fnd =
| Found
| NotFound

val find : a -> rbtree -> fnd

val bal0 : rbtree -> a -> rbtree -> a -> rbtree -> rbtree

val r2b : rbtree -> rbtree

val cof : rbtree -> color

type iChangedTo =
| ISameIndx
| IReddened
| IBlackInc

val bal1 : rbtree -> a -> rbtree -> ( * )

val bal2 : rbtree -> a -> rbtree -> ( * )

val c2i : color -> iChangedTo

type ins =
| IFound
| IInsed of iChangedTo * rbtree

val insert : a -> rbtree -> ins

type dChangedTo =
| StillFits
| Rebalance

val bal3 : rbtree -> a -> rbtree -> rbtree

val bal4 : rbtree -> a -> rbtree -> rbtree

val c2d : color -> dChangedTo

val r2c : color -> rbtree -> rbtree

val dfitl : color -> ( * ) -> a -> rbtree -> ( * )

val dfitr : color -> rbtree -> a -> ( * ) -> ( * )

val t2d : color -> rbtree -> ( * )

type dmin =
| Dmleaf
| Dmnode of a * ( * )

val delmin : rbtree -> dmin

type del =
| Delfnd of ( * )
| Delnot

val delete : a -> rbtree -> del

