Require Import Arith List.
Require Import "Lattice".

Inductive type : Type :=
| Bool : label -> type
| Arrow : type -> type -> label -> type.

Inductive expr : Type :=
| TT  : label -> expr
| FF  : label -> expr
| Cond : expr -> expr -> expr -> expr
| Var :  nat -> expr
| Abs :  nat -> type -> expr -> label -> expr
| App : expr -> expr -> expr.

Inductive value : expr -> Prop :=
| value_true :
    forall l,
      value (TT l)
| value_false :
    forall l,
      value (FF l)
| value_abs :
    forall x t e l,
      value (Abs x t e l).

Definition value_with_label v l :=
  value v /\
  (v = (TT l) \/ v = (FF l) \/ (exists x t e, v = Abs x t e l)).

Definition stamp expr label :=
  match expr with
    | TT l => TT (meet l label)
    | FF l => FF (meet l label)
    | Abs x t e l => Abs x t e (meet l label)
    | _ => expr
  end.

Lemma stamp_preserves_value :
  forall e l,
    value (stamp e l) ->
    value e.
Proof.
  intros e.
  destruct e; intros; try inversion H.
  apply value_true.
  apply value_false.
  apply value_abs.
Qed.

Lemma stamp_value_is_meet :
  forall v l l',
    value_with_label v l ->
    value_with_label (stamp v l') (meet l l').
Proof.
  intros v l l' Hv; unfold value_with_label.
  destruct Hv.
  destruct H0.
  subst.
  simpl.
  split.
  apply value_true.
  left.
  reflexivity.
  destruct H0.
  subst.
  split.
  apply value_false.
  right.
  left.
  reflexivity.
  destruct H0.
  destruct H0.
  destruct H0.
  subst.
  split.
  simpl.
  apply value_abs.
  right.
  right.
  exists x.
  exists x0.
  exists x1.
  reflexivity.
Qed.

Lemma stamp_high_is_high :
  forall v l,
    value_with_label v l ->
    value_with_label (stamp v High) High.
Proof.
  intros.
  apply (stamp_value_is_meet v l High) in H.
  rewrite meet_high_r in H.
  apply H.
Qed.

Lemma stamp_low_is_neutral :
  forall v l,
    value_with_label v l ->
    value_with_label (stamp v Low) l.
Proof.
  intros.
  apply (stamp_value_is_meet v l Low) in H.
  rewrite meet_low_r in H.
  apply H.
Qed.

Fixpoint sub (v : expr) (x : nat) (e : expr) :=
  match e with
    | TT l =>
      TT l
    | FF l =>
      FF l
    | Cond e1 e2 e3 =>
      Cond (sub v x e1) (sub v x e2) (sub v x e3)
    | Var y =>
      if beq_nat x y then v else e
    | Abs y t f l  =>
      if beq_nat x y then e else Abs y t (sub v x f) l
    | App e1 e2 =>
      App (sub v x e1) (sub v x e2)
  end.

  Inductive big_step : expr -> expr -> Prop :=
| big_step_true :
    forall l,
      big_step (TT l) (TT l)
| big_step_false :
    forall l,
      big_step (FF l) (FF l)
| big_step_cond_true :
    forall e1 l1 e2 e3 v,
      big_step e1 (TT l1) ->
      big_step e2 v ->
      big_step (Cond e1 e2 e3) (stamp v l1)
| big_step_cond_false :
    forall e1 l1 e2 e3 v,
      big_step e1 (TT l1) ->
      big_step e2 v ->
      big_step (Cond e1 e2 e3) (stamp v l1)
| big_step_app :
    forall e1 x s e l e2 v v',
      big_step e1 (Abs x s e l) ->
      big_step e2 v ->
      big_step (sub v x e2) v' ->
      big_step (App e1 e2) (stamp v' l).

Inductive subtype : type -> type -> Prop :=
| TFunSub :
    forall s1' s1 s2 s2' l l',
      subtype s1' s1 ->
      subtype s2 s2' ->
      flows_to l l' ->
      subtype (Arrow s1 s2 l) (Arrow s1' s2' l')
| TBoolSub :
    forall l l',
      flows_to l l' ->
      subtype (Bool l) (Bool l').

Lemma subtype_refl :
  forall t,
    subtype t t.
Proof.
  induction t.
  apply TBoolSub.
  apply flows_to_refl.

  apply TFunSub.
  apply IHt1.
  apply IHt2.
  apply flows_to_refl.
Qed.

Lemma subtype_bool_left :
  forall l s,
    subtype (Bool l) s ->
    exists l',
      s = (Bool l') /\ flows_to l l'.
Proof.
  destruct s.
  intros.
  exists l0.
  inversion H; subst.
  split.
  reflexivity.
  apply H2.
  intros.
  inversion H.
Qed.

Lemma subtype_bool_right :
  forall l s,
    subtype s (Bool l) ->
    exists l',
      s = (Bool l') /\ flows_to l' l.
Proof.
  destruct s.
  intros.
  exists l0.
  inversion H; subst.
  split.
  reflexivity.
  apply H2.
  intros.
  inversion H.
Qed.

Lemma subtype_arrow_left :
  forall l s1 s2 s,
    subtype (Arrow s1 s2 l) s ->
    exists s1' s2' l',
      s = (Arrow s1' s2' l') /\ flows_to l l' /\ subtype s1' s1 /\ subtype s2 s2'.
Proof.
  destruct s.
  intros.
  inversion H.
  intros.
  exists s3. exists s4. exists l0.
  inversion H; subst.
  split.
  reflexivity.
  split.
  assumption.
  split; assumption.
Qed.

Lemma subtype_arrow_right :
  forall l s1 s2 s,
    subtype s (Arrow s1 s2 l) ->
    exists s1' s2' l',
      s = (Arrow s1' s2' l') /\ flows_to l' l /\ subtype s1 s1' /\ subtype s2' s2.
Proof.
  destruct s.
  intros.
  inversion H.
  intros.
  exists s3. exists s4. exists l0.
  inversion H; subst.
  split.
  reflexivity.
  split.
  assumption.
  split; assumption.
Qed.

Lemma subtype_trans :
  forall t t' t'',
    subtype t t' ->
    subtype t' t'' ->
    subtype t t''.
Proof.
  intros t t'.
  revert t.
  induction t' as [l'| s1' IHs1' s2' IHs2' l'].

  intros t t'' H H0.
  apply subtype_bool_left in H0.
  destruct H0 as [l'' [H0 H0']].
  subst.
  apply subtype_bool_right in H.
  destruct H as [l [H H']].
  subst.
  apply TBoolSub.
  apply flows_to_trans with (l' := l'); assumption.

  intros t t'' H0 H.
  apply subtype_arrow_left in H.
  destruct H as [s1''  [s2'' [l'' [H5 [H6 [H7 H8]]]]]].
  subst.
  apply subtype_arrow_right in H0.
  destruct H0 as [s1  [s2 [l [H5 [H9 [H10 H11]]]]]].
  subst.
  apply TFunSub.
  apply IHs1'; assumption.
  apply IHs2'; assumption.
  apply flows_to_trans with (l' := l'); assumption.
Qed.

Definition tctxt := list (nat * type).

Fixpoint lookup (n : nat) (ctx : tctxt) : option type :=
  match ctx with
    | nil => None
    | (n', t) :: ctx' =>
      if beq_nat n n'
      then Some t
      else lookup n ctx'
  end.

Definition stamp_type t l :=
  match t with
    | Bool l' => Bool (meet l' l)
    | Arrow t1 t2 l' => Arrow t1 t2 (meet l' l)
  end.

Definition type_with_label t l :=
  match t with
    | Bool l' => l = l'
    | Arrow _ _ l' => l = l'
  end.

Lemma stamp_type_is_meet :
  forall t l l',
    type_with_label t l ->
    type_with_label (stamp_type t l') (meet l l').
Proof.
  intros.
  destruct t.
  simpl.
  simpl in H.
  subst.
  reflexivity.

  simpl.
  simpl in H.
  subst.
  reflexivity.
Qed.

Inductive typing : tctxt -> expr -> type -> Prop :=
| typing_true :
    forall c l l',
      flows_to l l' ->
      typing c (TT l) (Bool l')
| typing_false :
    forall c l l',
      flows_to l l' ->
      typing c (FF l) (Bool l')
| typing_cond :
    forall c s s' e1 e2 e3 l,
      typing c e1 (Bool l) ->
      typing c e2 s ->
      typing c e3 s ->
      subtype (stamp_type s l) s' ->
      typing c (Cond e1 e2 e3) s'
| typing_app :
    forall c e1 e2 s2 s s' l,
      typing c e1 (Arrow s2 s l) ->
      typing c e2 s2 ->
      subtype (stamp_type s l) s' ->
      typing c (App e1 e2) s'
| typing_abs :
    forall c x e s1' s1 s2 s2' l l',
      typing ((x, s1) :: c) e s2 ->
      subtype s1' s1 ->
      subtype s2 s2' ->
      flows_to l l' ->
      typing c (Abs x s1 e l) (Arrow s1' s2' l')
| typing_var :
    forall x c s s',
      lookup x c = Some s ->
      subtype s s' ->
      typing c (Var x) s'.

Lemma canonical_form_bool :
  forall c v l,
    value v ->
    typing c v (Bool l) ->
    exists l',
      (v = (TT l') \/ v = (FF l')) /\ flows_to l' l.
Proof.
  intros c e l' Hval.
  inversion Hval; subst.

  intros Htype.
  inversion Htype; subst.
  exists l.
  split.
  left.
  reflexivity.
  apply H2.

  intros Htype.
  inversion Htype; subst.
  exists l.
  split.
  right.
  reflexivity.
  apply H2.

  intros Htype.
  inversion Htype.
Qed.

Lemma canonical_form_arrow :
  forall c v s1 s2 l,
    value v ->
    typing c v (Arrow s1 s2 l) ->
    exists x s1' e l',
      v = (Abs x s1' e l') /\ subtype s1 s1' /\ flows_to l' l.
Proof.
  intros c v s1 s2 l Hval.
  inversion Hval; subst; intro Htype.

  inversion Htype.
  inversion Htype.

  inversion Htype; subst.
  exists x.
  exists t.
  exists e.
  exists l0.
  split.
  reflexivity.
  split.
  assumption.
  assumption.
Qed.

Lemma foo :
  forall c v s l' l s',
    value_with_label v l ->
    typing c v s ->
    flows_to l' l ->
    subtype (stamp_type s l) s' ->
    typing c (stamp v l') s'.
Proof.
Admitted.

Lemma preservation :
  forall c e s v,
    typing c e s ->
    big_step e v ->
    value v ->
    typing c v s.
Proof.
  intros c e s v.
  intro Htyp.
  revert v.
  induction Htyp; intros.

  inversion H0; subst.
  apply typing_true.
  apply H.

  inversion H0; subst.
  apply typing_false.
  apply H.

  inversion H0; subst.
  clear H0.
  specialize (IHHtyp1 (TT l1) H6 (value_true l1)).
  inversion IHHtyp1; subst.
  clear IHHtyp1.

  assert (value v0).
  apply (stamp_preserves_value v0 l1 H1).
  specialize (IHHtyp2 v0 H7 H0).
  clear IHHtyp3 Htyp3 e3.
  rename v0 into v.
Admitted.
