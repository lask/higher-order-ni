Require Import "Main".
Require Import "Lattice".

Inductive z_s : Type :=
| ZType : z_t -> label -> z_s
with z_t : Type :=
| ZBool : z_t
| ZArrow : z_s -> z_s -> z_t.

Theorem z_s_ind' :
  forall P : z_s -> Prop,
    (forall (z : z_t) (l : label), P (ZType z l)) ->
    forall z, P z.
Proof.
  apply z_s_ind.
Qed.




Fixpoint type_of_z_s z :=
  match z with
    | ZType t l => type_of_z_t t l
  end
with type_of_z_t t l :=
       match t with
         | ZBool => Bool l
         | ZArrow t1 t2 => Arrow (type_of_z_s t1) (type_of_z_s t2) l
       end.

Fixpoint z_s_of_type t :=
  match t with
    | Bool l => ZType ZBool l
    | Arrow t1 t2 l => ZType (ZArrow (z_s_of_type t1) (z_s_of_type t2)) l
  end.

Lemma type_and_z_s_are_isomorphic :
  exists (f : z_s -> type) (g : type -> z_s) ,
    (forall t, f (g t) = t) /\ (forall z, g (f z) = z).
