Section Prop_Logic.
  Lemma Coq_01 : forall A B C:Prop, (A->B->C) -> (A->B) -> A -> C.
Proof.
intros.
apply H.
assumption.
apply H0.
assumption.
Qed.

  Lemma Coq_02 : forall A B C:Prop, A /\ (B /\ C) -> (A /\ B) /\ C.
Proof.
intros.
apply conj.
apply conj.
apply H.
destruct H.
apply H0.
apply H.
Qed.

  Lemma Coq_03 : forall A B C D:Prop, (A -> C) /\ (B -> D) /\ A /\ B -> C /\ D.
Proof.
intros.
destruct H.
destruct H0.
destruct H1.
apply conj.
apply H.
exact H1.
apply H0.
exact H2.
Qed.

  Lemma Coq_04 : forall A : Prop, ~(A /\ ~A).
Proof.
intros.
unfold not.
intros.
destruct H.
apply H0.
exact H.
Qed.

  Lemma Coq_05 : forall A B C:Prop, A \/ (B \/ C) -> (A \/ B) \/ C.
Proof.
intros.
destruct H.
apply or_introl.
apply or_introl.
exact H.
destruct H.
apply or_introl.
apply or_intror.
exact H.
apply or_intror.
exact H.
Qed.

  Lemma Coq_06 : forall A, ~~~A -> ~A.
Proof.
unfold not.
intros.
apply H.
intro.
contradiction.
Qed.

  Lemma Coq_07 : forall A B:Prop, (A->B)->~B->~A.
Proof.
unfold not.
intros.
assert B.
apply H.
apply H1.
contradiction.
Qed.

  Lemma Coq_08: forall A B:Prop, ((((A->B)->A)->A)->B)->B.
Proof.
intros.
apply H.
intros.
apply H0.
intros.
apply H.
intros.
apply H1.
Qed.

  Lemma Coq_09 : forall A:Prop, ~~(A\/~A).
Proof.
unfold not.
intros.
apply H.
assert (A->False).
intros.
assert (A\/(A->False)).
apply or_introl.
apply H0.
apply H.
exact H1.
apply or_intror.
exact H0.
Qed.

End Prop_Logic.
