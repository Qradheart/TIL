Theorem Modus_ponens:
  forall (P Q: Prop), (P->Q)->P->Q.
Proof.
intro.
intro.
intro.
exact H.
Qed.

Theorem Modus_ponens_another_proof:
  forall (P Q: Prop), (P->Q)->P->Q.
Proof.
intros.
apply H.
exact H0.
Qed.

Theorem Modus_ponens_is_good:
  forall (P Q: Prop), (P->Q)->P->Q.
Proof.
exact Modus_ponens.
Qed.
