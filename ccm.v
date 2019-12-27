From iris Require Export base.
Set Default Proof Using "Type".

Class Cancelative {A} (R : relation A) (f : A → A → A) : Prop :=
  cancel x y z : R (f x y) (f x z) → R y z.

Class PartialInv {A} (R: relation A) (f : A → A → A) (g : A → A → A) : Prop :=
  pinv x y : R (g (f x y) y) x.

Class CCM :=
  {
    ccm_car :> Type;
    ccm_unit : ccm_car;
    ccm_op: ccm_car → ccm_car → ccm_car;
    ccm_opinv: ccm_car → ccm_car → ccm_car;
    ccm_assoc : Assoc (=) ccm_op;
    ccm_comm : Comm (=) ccm_op;
    ccm_left_id : LeftId (=) ccm_unit ccm_op;
    ccm_cancel : Cancelative (=) ccm_op;
    ccm_pinv : PartialInv (=) ccm_op ccm_opinv;
  }.

Lemma ccm_right_id {M: CCM} : RightId (=) ccm_unit ccm_op.
Proof. intros x. etrans; [apply ccm_comm|apply ccm_left_id]. Qed.

Lemma ccm_pinv_unit {M: CCM} x : ccm_opinv x ccm_unit = x.
Proof.
  rewrite <- (ccm_right_id x) at 1.
  apply ccm_pinv.
Qed.

