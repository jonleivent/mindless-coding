type bool =
| True
| False

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

val compareSpec2Type : comparison -> compareSpecT

type 'a sig0 =
  'a
  (* singleton inductive, whose constructor was exist *)

val nat_compare : nat -> nat -> comparison

type color =
| Red
| Black

type oKNode =
| OKRed
| OKBlack

type rbtree =
| Leaf
| Node of oKNode * rbtree * nat * rbtree

val r2b : rbtree -> rbtree

type blkn =
| Mkblkn of bool * rbtree

val blacken : rbtree -> blkn

val cof : rbtree -> color

type cComp =
| CCompEQ
| CCompRB
| CCompBR

val ccomp : rbtree -> rbtree -> cComp

val bal0 : nat -> nat -> rbtree -> rbtree -> rbtree -> rbtree

type cT =
  rbtree
  (* singleton inductive, whose constructor was mkCT *)

val bal1 : rbtree -> nat -> rbtree -> cT

val bal2 : rbtree -> nat -> rbtree -> cT

val bal3 : rbtree -> nat -> rbtree -> rbtree

val bal4 : rbtree -> nat -> rbtree -> rbtree

val comp : nat -> nat -> compareSpecT

type fnd =
| Found
| NotFound

val find : nat -> rbtree -> fnd

type ins =
| Mkins of bool * rbtree

val insert : nat -> rbtree -> ins

type dmin =
| Nodmin
| Mkdmin of nat * bool * rbtree

val delmin : rbtree -> dmin

type del =
| Delfnd of bool * rbtree
| Delnot

val delete : nat -> rbtree -> del

