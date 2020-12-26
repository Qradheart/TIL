Require Import Classical.
Load "D:\デスクトップ\Coq\art\library\arithmetic\basic_property.v".

Section preparation.

Fixpoint equal_num (n m: nat) :=
  match n with
  | 0 => match m with
        | 0 => 1
        | S q => 0
        end
  | S p => match m with
        | 0 => 0
        | S q => equal_num p q
        end
  end.

Definition multiple_check (n l m: nat) := equal_num n (l * m).

Definition boollike (n: nat) :=
  match n with
  | 0 => 0
  | S m => 1
  end.

Lemma boollike_value:
  forall n: nat, (boollike n = 0) \/ (boollike n = 1).
Proof.
induction n.
simpl. left. trivial.
simpl. right. trivial.
Qed.

Fixpoint paramater_and (f:nat -> nat) (n: nat) :=
  match n with
  | 0 => 1
  | S p => boollike ((paramater_and f p) * (f p))
  end.

Fixpoint paramater_or (f:nat -> nat) (n: nat) :=
  match n with
  | 0 => 0
  | S p => boollike ((paramater_or f p) + (f p))
  end.

Definition divisible (n m: nat) := paramater_or (multiple_check m n) (S m).

Lemma paramater_and_boollike:
  forall f: nat -> nat, forall n:nat,
    (paramater_and f n = 0) \/ (paramater_and f n = 1).
Proof.
intros.

induction n.
(* n = 0 case *)
  simpl. right. trivial.
(* S n case *)
  simpl.
  specialize (boollike_value (paramater_and f n * f n)). trivial.
Qed.

Lemma paramater_or_boollike:
  forall f: nat -> nat, forall n:nat,
    (paramater_or f n = 0) \/ (paramater_or f n = 1).
Proof.
intros.

induction n.
(* n = 0 case *)
  simpl. left. trivial.
(* S n case *)
  simpl.
  specialize (boollike_value (paramater_or f n + f n)). trivial.
Qed.

Lemma divisible_value_boollike:
  forall n m: nat, (divisible n m = 0) \/ (divisible n m = 1).
Proof.
intros.
unfold divisible.
specialize (paramater_or_boollike (multiple_check m n) (S m)). trivial.
Qed.

Lemma multiple_0:
  forall n: nat, n * 0 = 0.
Proof.
induction n. simpl. trivial. simpl. trivial.
Qed.

Lemma division_modify:
  forall n m: nat,
    (exists quot: nat, m = n * quot) -> 
      (exists goodquot: nat, (goodquot <= m) /\ (m = n * goodquot)).
Proof.
intros. destruct H. induction m.
exists 0. split. trivial. symmetry. apply (multiple_0 n).
clear IHm.

exists x. split.
  induction n. 
    assert (S m = 0). rewrite H. simpl. trivial. clear H. inversion H0.
    clear IHn. pose proof additive_leq as AL.
    assert (x <= S n * x).
      simpl. apply AL.
    rewrite H. exact H0.
  trivial.
Qed.

Lemma divisibility_a:
  forall n m: nat, (exists quot: nat, m = n * quot) 
    -> (divisible n m = 1).
Proof.
intros.
pose proof division_modify as Div.
specialize ((Div n m) H). clear H.
destruct Div. destruct H.
unfold divisible.

assert (paramater_or (multiple_check m n) (S x) = 1).
  simpl. unfold multiple_check. 
  rewrite <- H0.
    assert (forall t: nat, equal_num t t = 1).
    intros. induction t.
    simpl. trivial.
    simpl. trivial.
  specialize (H1 m).
  rewrite H1.
  assert (forall t: nat, boollike(t + 1) = 1).
    induction t.
    simpl. trivial.
    simpl. trivial.
  apply H2.

assert (S x <= S m). apply leq_S. trivial.

assert (forall t: nat, S x <= t ->
  paramater_or (multiple_check m n) t = 1).
intros. induction H3.
    trivial.
    simpl. rewrite IHle. simpl. trivial.

specialize (H3 (S m)). specialize (H3 H2).
exact H3.
Qed.


End preparation.

Section prime.




End prime.