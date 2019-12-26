From iris Require Export base.
Set Default Proof Using "Type".

Class Cancelative {A} (R : relation A) (f : A → A → A) : Prop :=
  cancel x y z : R (f x y) (f x z) → R y z.

Class PartialInv {A} (R: relation A) (f : A → A → A) (g : A → A → A) : Prop :=
  pinv x y : R (g (f x y) y) x.

Class CCM {M} :=
  {
    ccm_unit : M;
    ccm_op: M → M → M;
    ccm_opinv: M → M → M;
    ccm_assoc : Assoc (=) ccm_op;
    ccm_comm : Comm (=) ccm_op;
    ccm_left_id : LeftId (=) ccm_unit ccm_op;
    ccm_cancel : Cancelative (=) ccm_op;
    ccm_pinv : PartialInv (=) ccm_op ccm_opinv;
  }.

Lemma ccm_right_id `{CCM M} : RightId (=) ccm_unit ccm_op.
Proof. intros x. etrans; [apply ccm_comm|apply ccm_left_id]. Qed.

Lemma ccm_pinv_unit `{CCM M} x : ccm_opinv x ccm_unit = x.
Proof.
  rewrite <- (ccm_right_id x) at 1.
  apply ccm_pinv.
Qed.

