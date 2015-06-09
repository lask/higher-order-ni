Inductive label : Type :=
| High
| Low.

Definition join l1 l2 :=
  match l1, l2 with
    | High, High => High
    | High, Low => High
    | Low, High => High
    | Low, Low => Low
  end.

Lemma join_idempotent :
  forall l,
    l = join l l.
Proof.
  destruct l; reflexivity.
Qed.

Definition flows_to l1 l2 :=
  l2 = join l1 l2.

Lemma flows_to_refl :
  forall l,
    flows_to l l.
Proof.
  unfold flows_to.
  apply join_idempotent.
Qed.

Lemma flows_to_trans :
  forall l l' l'',
    flows_to l l' ->
    flows_to l' l'' ->
    flows_to l l''.
Proof.
  intros l l' l'';
  destruct l;
  destruct l';
  destruct l'';
  auto.
  intros.
  apply flows_to_refl.
Qed.

Lemma flows_to_antisym :
  forall l l',
    flows_to l l' ->
    flows_to l' l ->
    l = l'.
Proof.
  destruct l;
  destruct l';
  intros;
  auto.
Qed.

Lemma high_is_top :
  forall l,
    flows_to l High.
Proof.
  destruct l; reflexivity.
Qed.

Lemma low_is_bot :
  forall l,
    flows_to Low l.
Proof.
  destruct l; reflexivity.
Qed.


Lemma join_high_r :
  forall l,
    join l High = High.
Proof.
  destruct l; reflexivity.
Qed.

Lemma join_high_l :
  forall l,
    join High l = High.
Proof.
  destruct l; reflexivity.
Qed.

Lemma join_low_r :
  forall l,
    join l Low = l.
Proof.
  destruct l; reflexivity.
Qed.

Lemma join_low_l :
  forall l,
    join Low l = l.
Proof.
  destruct l; reflexivity.
Qed.

Lemma join_is_upper_bound :
  forall l l',
    flows_to l (join l l') /\ flows_to l' (join l l').
Proof.
  destruct l; destruct l'; split; (auto ) || (unfold flows_to; reflexivity).
Qed.

Lemma join_is_least_upper_bound :
  forall l l' u,
    flows_to l u ->
    flows_to l' u ->
    flows_to (join l l') u.
Proof.
  destruct l; destruct l'; destruct u; intros; auto.
Qed.

Lemma flows_to_questionable :
  forall l l' l'',
    flows_to l l' ->
    flows_to l l'' ->
    flows_to l (join l'' l').
Proof.
  destruct l; destruct l'; destruct l''; intros; try reflexivity.
  inversion H0.
Qed.

Lemma join_comm :
  forall l l',
    join l l' = join l' l.
Proof.
  intros.
  destruct (join_is_upper_bound l l').
  destruct (join_is_upper_bound l' l).
  assert (flows_to (join l l') (join l' l)).
  apply join_is_least_upper_bound; assumption.
  assert (flows_to (join l' l) (join l l')).
  apply join_is_least_upper_bound; assumption.
  apply flows_to_antisym; auto.
Qed.

Lemma join_assoc :
  forall l l' l'',
    join (join l l') l'' = join l (join l' l'').
Proof.
  destruct l; destruct l'; destruct l''; reflexivity.
Qed.
