Section InductionPrinciple.
  Variable P : nat -> Type.

  Require Import Omega.

  Local Definition nat_xrect_aux:
    (forall n, (forall m, m<n -> P m) -> P n) ->
    forall n, (forall m, m<n -> P m).
  Proof.
    induction n as [|n IHn].
    - intros m H.
      omega.
    - intros m H.
      apply X.
      intros m0 H0.
      apply IHn.
      omega.
  Qed.

  Local Definition weaken:
    (forall n, (forall m, m<n -> P m)) -> (forall n, P n).
  Proof.
    intros X n.
    apply (X (S n) n).
    omega.
  Qed.

  Theorem nat_xrect:
    (forall n, (forall m, m<n -> P m) -> P n) -> forall n, P n.
  Proof.
    intros X n.
    apply weaken.
    apply nat_xrect_aux.
    assumption.
  Qed.

End InductionPrinciple.

Section EInductionPrinciple.
  Require Import erasable.
  Import ErasableNotation.
  Notation EN := (##nat).
  Definition Elt := liftP2 lt.

  Theorem Elt_wf : well_founded Elt.
  Proof.
    intros y.
    unerase.
    induction y as [y H] using nat_xrect.
    constructor.
    intros ? (x & ? & ? & ? & ?).
    simplify_hyps.
    apply H.
    assumption.
  Qed.

  Variable P : EN -> Type.

  Definition enat_xrect := well_founded_induction_type Elt_wf.

End EInductionPrinciple.

Extraction Inline weaken.
Extraction Inline nat_xrect_aux.
Extraction Inline nat_xrect.
Extraction Inline enat_xrect.
