Section inequality.
(* *)

Fixpoint nat_equal (n m: nat) :=
  match n with
  | 0 => match m with
        | 0 => True
        | S q => False
        end
  | S p => match m with
        | 0 => False
        | S q => nat_equal p q
        end
  end.

Fixpoint nat_leq (n m: nat) :=
  match n with
  | 0 => match m with
        | 0 => True
        | S q => True
        end
  | S p => match m with
        | 0 => False
        | S q => nat_leq p q
        end
  end.

Fixpoint nat_lt (n m: nat) :=
  match n with
  | 0 => match m with
        | 0 => False
        | S q => True
        end
  | S p => match m with
        | 0 => False
        | S q => nat_lt p q
        end
  end.

Proposition one_neq_zero:
  (1 = 0) -> False.
Proof.
intro.

(* nat_equal 関数の値の評価 *)
assert (nat_equal 1 0). rewrite H. simpl. trivial.

assert (nat_equal 1 0 = False). simpl. trivial.
rewrite <- H1. exact H0.
Qed.

Proposition nat_equal_is_equality:
  forall n m: nat, n = m <-> nat_equal n m.
Proof.
intro.
induction n.
split.

(* 0 = m -> nat_equal 0 m *)
intro. rewrite H. clear H.
induction m.
  simpl. trivial.
  simpl. exact IHm.

(* nat_equal 0 m -> 0 = m *)

intro.
induction m.
  trivial.
  assert (nat_equal 0 (S m) -> False).
    simpl. trivial.
  contradiction.

split.
intro. rewrite H. clear H.
induction m.
  simpl. trivial.
  simpl. exact IHm.
induction m.
intro.
  assert (nat_equal 0 (S n) -> False).
    simpl. trivial.
  contradiction.
intro.
  assert (nat_equal (S n) (S m) -> nat_equal n m).
  simpl. trivial.
assert (n = m).
  apply IHn. apply H0. exact H.
rewrite H1. trivial.
Qed.

Lemma zero_leq_nat:
  forall n: nat, 0 <= n.
Proof.
induction n.
trivial. apply le_S. exact IHn.
Qed.

Lemma n_neq_Sn:
  forall n: nat, n < S n.
Proof.
intro. unfold lt. trivial.
Qed.

Lemma leq_S:
  forall n m: nat, n <= m -> S n <= S m.
Proof.
intros.
induction H. trivial. apply le_S. trivial.
Qed.

Lemma nat_leq_succ:
  forall n m: nat, nat_leq n m -> nat_leq n (S m).
Proof.
induction n.
induction m. simpl. trivial.
  simpl. trivial.
induction m. simpl. intro. contradiction.
  simpl. apply IHn.
Qed.

Lemma nat_leq_trans:
  forall n m p: nat, (n <= m) -> (nat_leq m p) -> (nat_leq n p).
Proof.
intros.
induction m. inversion H. trivial.
inversion H. trivial.
  assert (nat_leq (S m) p -> nat_leq m p).
    induction p. simpl. intro. contradiction.
    simpl. apply (nat_leq_succ m p).

apply IHm. apply H2. apply H3. apply H0.
Qed.

Lemma leq_trans:
  forall n m p: nat, (n <= m) -> (m <= p) -> (n <= p).
Proof.
  intros n m p Hnm Hmp.
  induction Hmp.
  - (* le_n *) apply Hnm.
  - (* le_S *) apply le_S. apply IHHmp. Qed.

Lemma nat_leq_is_leq:
  forall n m: nat, (n <= m) <-> (nat_leq n m).
Proof.
intros. split. 
  intro. induction m.
  inversion H. simpl. trivial.
  inversion H. simpl. clear H H0 IHm. induction m. simpl. trivial. simpl. trivial.
    clear H0 H. assert (nat_leq n m). apply (IHm H1).
    apply (nat_leq_succ n m). exact H.

assert ((forall t p q: nat, q <= t -> nat_leq p q -> p <= q) -> nat_leq n m -> n <= m).
intro. specialize (H m n m). apply H. clear H. apply le_n. apply H. clear H.
intro. clear n m.

induction t.
  induction q.
    induction p. trivial. intros. assert (nat_leq (S p) 0 -> False). simpl. intro. trivial.
    contradiction.
  intro.
  inversion H.
    assert (forall q: nat, q <= S t -> q <= t \/ q = S t). clear IHt. 
    intros. inversion H. right. trivial. left. trivial.
  intros. specialize (H q).
  apply H in H0. clear H.
  destruct H0.
    specialize (IHt p q).
    apply IHt in H. exact H. exact H1.
    rewrite H. rewrite H in H1.
    clear H.
    induction p. apply (zero_leq_nat (S t)).
    assert (nat_leq (S p) (S t) -> nat_leq p t). simpl. trivial.
    assert (p <= t).
      specialize (IHt p t). apply IHt. apply le_n. 
      apply (H H1).
    clear IHt H1 IHp H q.
    apply leq_S. trivial.
Qed.

(* 以下演算を伴う不等号に関する命題群 *)

Lemma add_zero_right:
  forall n: nat, n + 0 = n.
Proof.
intro. induction n. trivial. simpl. rewrite IHn. trivial.
Qed.

Lemma additive_commute:
  forall n m: nat, n + m = m + n.
Proof.
intros. induction n. simpl. symmetry. apply (add_zero_right m). simpl. rewrite IHn.
clear IHn. induction m. simpl. trivial. simpl. rewrite IHm. trivial.
Qed.

Lemma S_neq_0:
  forall n: nat, (S n = 0) -> False.
Proof.
pose proof nat_equal_is_equality as X. intro. specialize (X (S n) 0). 
destruct X. intro. 
assert (nat_equal (S n) 0 -> False). simpl. trivial.
apply H2. apply H. exact H1.
Qed.

Lemma no_nat_smaller_than_0:
  forall n: nat, n <= 0 -> n = 0.
Proof.
intro. induction n. trivial.
intro. inversion H.
Qed.


Lemma additive_leq:
  forall n m: nat, n <= n + m.
Proof.
intros. pose proof additive_commute as X.
specialize (X n m). rewrite X. clear X.
induction m.
  simpl. trivial.
  simpl. apply le_S. trivial.
Qed.

Lemma posint_multiple_bigger:
  forall n m: nat, m <= (S n) * m.
Proof.
intros.
induction n. 
simpl. pose proof add_zero_right as X.
specialize (X m). rewrite X. trivial.

simpl. specialize (additive_leq m (m + n * m)). trivial.
Qed.

End inequality.



















