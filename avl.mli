

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

type balanceFactor =
| HiLeft
| Flat
| HiRight
| NoSubs

type avltree =
| Leaf
| Node of balanceFactor * avltree * a * avltree

type findResult =
| Found
| NotFound

val find : a -> avltree -> findResult

val bof : avltree -> balanceFactor

val rotateRight : avltree -> a -> avltree -> avltree

val rotateLeft : avltree -> a -> avltree -> avltree

val raised : avltree -> avltree -> bool

type insertResult =
| FoundByInsert
| Inserted of avltree

val ifitl : balanceFactor -> avltree -> a -> avltree -> insertResult

val ifitr : balanceFactor -> avltree -> a -> avltree -> insertResult

val insert : a -> avltree -> insertResult

type delout =
  avltree
  (* singleton inductive, whose constructor was Delout *)

val lowered : avltree -> avltree -> bool

val dRotateRight : avltree -> a -> avltree -> delout

val dRotateLeft : avltree -> a -> avltree -> delout

val dFitLeft : balanceFactor -> delout -> avltree -> a -> avltree -> delout

val dFitRight : balanceFactor -> delout -> avltree -> a -> avltree -> delout

type delminResult =
| NoMin
| MinDeleted of a * delout

val delmin : avltree -> delminResult

type deleteResult =
| DelNotFound
| Deleted of delout

val delete : a -> avltree -> deleteResult

