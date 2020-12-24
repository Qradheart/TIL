Theorem S_combinator:
  forall (P Q R: Prop), (P->Q->R) -> (Q->P) -> Q -> R.
Proof.
intros.
apply H.
apply H0.
assumption.
assumption.
Qed.

Lemma De_Morgan:
  forall A B: Prop, ~(A \/ B) -> (~A /\ ~B).
Proof.
unfold not.
intros.
apply conj.
intros.
apply H.
apply or_introl.
assumption.
intros.
apply H.
apply or_intror.
assumption.
Qed.
