Inductive label : Type :=
| High
| Low.

Definition meet l1 l2 :=
  match l1, l2 with
    | High, High => High
    | High, Low => High
    | Low, High => High
    | Low, Low => Low
  end.

Lemma meet_idempotent :
  forall l,
    l = meet l l.
Proof.
  destruct l; reflexivity.
Qed.

Definition flows_to l1 l2 :=
  l2 = meet l1 l2.

Lemma flows_to_refl :
  forall l,
    flows_to l l.
Proof.
  unfold flows_to.
  apply meet_idempotent.
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


Lemma meet_high_r :
  forall l,
    meet l High = High.
Proof.
  destruct l; reflexivity.
Qed.

Lemma meet_high_l :
  forall l,
    meet High l = High.
Proof.
  destruct l; reflexivity.
Qed.

Lemma meet_low_r :
  forall l,
    meet l Low = l.
Proof.
  destruct l; reflexivity.
Qed.

Lemma meet_low_l :
  forall l,
    meet Low l = l.
Proof.
  destruct l; reflexivity.
Qed.

Lemma meet_is_upper_bound :
  forall l l',
    flows_to l (meet l l') /\ flows_to l' (meet l l').
Proof.
  destruct l; destruct l'; split; (auto ) || (unfold flows_to; reflexivity).
Qed.

Lemma meet_is_least_upper_bound :
  forall l l' u,
    flows_to l u ->
    flows_to l' u ->
    flows_to (meet l l') u.
Proof.
  destruct l; destruct l'; destruct u; intros; auto.
Qed.

Lemma flows_to_questionable :
  forall l l' l'',
    flows_to l l' ->
    flows_to l l'' ->
    flows_to l (meet l'' l').
Proof.
  destruct l; destruct l'; destruct l''; intros; try reflexivity.
  inversion H0.
Qed.

Lemma meet_l_l :
  forall l,
    meet l l = l.
Proof.
  intros.
  assert (flows_to (meet l l) l).
  apply meet_is_least_upper_bound.
  apply flows_to_refl.
  apply flows_to_refl.
  destruct (meet_is_upper_bound l l).
  apply flows_to_antisym; assumption.
Qed.
