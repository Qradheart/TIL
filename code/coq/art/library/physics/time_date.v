(*
曜日型とそれに関連する基本的な関数・命題の実装です. 
*)
(*
曜日型は day : Type です.
next_day は day -> day であって「次の曜日を返す」ことを意図しています. 
week_day_periodicity は「next_day を seven 回するは恒等的」を意図しています. 
later_day は day -> nat -> day であって
  「day1 の nat1 日後の曜日を返す」ことを意図しています. 
seven_days は「day1 の 7 日後の曜日は day1」を意図しています. 
commute_next_later は
  「day1 の次の曜日の nat1 日後の曜日は day1 の nat1 日後の曜日の次の曜日」
  を意図しています.  
later_day_addition は
  「day1 の nat1 日後の曜日の nat2 日後の曜日は day1 の (nat1 + nat2) 日後の曜日」
  を意図しています. 
later_day_peroidicity は
  「day1 の 7 * nat1 日後の曜日は day1」を意図しています.
*)
(*
next_weekday は「次の平日の曜日を返す」ことを意図しています. 
*)

Inductive day : Type :=
  | monday : day
  | tuesday : day
  | wednesday : day
  | thursday : day
  | friday : day
  | saturday : day
  | sunday : day.

Definition next_day (d:day) : day :=
  match d with
  | monday => tuesday
  | tuesday => wednesday
  | wednesday => thursday
  | thursday => friday
  | friday => saturday
  | saturday => sunday
  | sunday => monday
  end.

Lemma week_day_periodicity:
  forall D: day, next_day(next_day(next_day(next_day(next_day(next_day(next_day(D)))))))=D.
Proof.
induction D.
simpl. trivial.
simpl. trivial.
simpl. trivial.
simpl. trivial.
simpl. trivial.
simpl. trivial.
simpl. trivial.
Qed.

Fixpoint later_day (d:day)(n:nat) : day :=
  match n with
  | 0 => d
  | S m => next_day(later_day d m)
  end.

Lemma seven_days:
  forall D: day, later_day D 7 = D.
Proof.
simpl.
apply week_day_periodicity.
Qed.

Lemma commute_next_later:
  forall D: day, forall n: nat, next_day (later_day D n) = later_day (next_day D) n.
Proof.
induction n.
simpl. trivial.
simpl. rewrite IHn. trivial.
Qed.

Lemma later_day_addition:
  forall D: day, forall n m: nat, later_day (later_day D n) m = later_day D (n + m).
Proof.
induction n.
(* Case n = 0 *)
simpl. trivial.
(* Case S n *)
simpl. intro.
specialize (IHn m).
rewrite <- IHn.
rewrite (commute_next_later (later_day D n) m). trivial.
Qed.

Lemma later_day_periodicity:
  forall D: day, forall n: nat, (exists m: nat, n = m * 7) -> later_day D n = D.
Proof.
intros. destruct H. rewrite H. clear H.
induction x.
simpl. trivial.
assert (S x * 7 = 7 + x * 7).
simpl. trivial.
rewrite H.
destruct (later_day_addition D 7 (x * 7)).
pose proof seven_days as X.
specialize (X D).
rewrite X. exact IHx.
Qed.

Definition next_weekday (d:day) : day :=
  match d with
  | monday => tuesday
  | tuesday => wednesday
  | wednesday => thursday
  | thursday => friday
  | friday => monday
  | saturday => monday
  | sunday => monday
  end.













