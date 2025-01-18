Require Import Modulus.
Require Export Complex. 

(******************************)
(* Defining polar coordinates *)
(******************************)

Definition get_arg (p : C) : R :=
  match Rcase_abs (snd p) with
  | left _ => 2 * PI - acos (fst p / Cmod p)
  | right _ => acos (fst p / Cmod p)
  end.

Definition rect_to_polar (z : C) : R * R :=
  (Cmod z, get_arg z).

Definition polar_to_rect (p : R * R) : C := 
  fst p * (Cexp (snd p)).


Definition WF_polar (p : R * R) : Prop :=
  0 < fst p /\ 0 <= snd p < 2 * PI.

Definition polar_mult (p1 p2 : R * R) : R * R :=
  match Rcase_abs (snd p1 + snd p2 - 2 * PI) with
  | left _ => (fst p1 * fst p2, snd p1 + snd p2)%R
  | right _ => (fst p1 * fst p2, snd p1 + snd p2 - 2 * PI)%R
  end.

Fixpoint polar_pow (p : R * R) (n : nat) : R * R :=
  match n with 
  | O => (1, 0)%R
  | S n' => polar_mult p (polar_pow p n')
  end.


 

(* prelim sin and cos lemmas *)


Lemma cos_2PI_minus_x : forall (x : R), cos (2 * PI - x) = cos x.
Proof. intros. 
       rewrite cos_minus, cos_2PI, sin_2PI; lra.
Qed.

Lemma sin_2PI_minus_x : forall (x : R), sin (2 * PI - x) = (- sin x)%R.
Proof. intros. 
       rewrite sin_minus, cos_2PI, sin_2PI; lra.
Qed.

Lemma fst_div_Cmod : forall (x y : R),
  (x, y) <> C0 ->
  -1 <= x / Cmod (x, y) <= 1.
Proof. intros. 
       assert (H0 := Rmax_Cmod (x, y)).
       apply (Rle_trans (Rabs (fst (x, y)))) in H0; try apply Rmax_l; simpl in *.
       apply (Rmult_le_compat_r (/ Cmod (x, y))) in H0.
       rewrite Rinv_r, <- (Rabs_pos_eq (Cmod _)), <- Rabs_inv, <- Rabs_mult in H0.
       all : try (left; apply Rinv_0_lt_compat); try apply Cmod_ge_0; try apply Cmod_gt_0.
       all : try (unfold not; intros; apply H; apply Cmod_eq_0; easy).
       destruct H0.
       - apply Rabs_def2 in H0; lra.
       - unfold Rabs in H0; destruct (Rcase_abs (x * / Cmod (x, y))).
         assert (H' : (x * / Cmod (x, y))%R = (-1)%R). lra.
         unfold Rdiv; rewrite H'; lra.
         unfold Rdiv; rewrite H0; lra.
Qed.

Lemma fst_div_Cmod_lt : forall (x y : R),
  (y <> 0)%R ->
  -1 < x / Cmod (x, y) < 1.
Proof. intros. 
       assert (H' : (x, y) <> C0).
       { unfold not; intros; apply H.
         apply (f_equal_gen snd snd) in H0; simpl in *; easy. }
       assert (H0 := Rmax_Cmod (x, y)).
       apply (Rle_trans (Rabs (fst (x, y)))) in H0; try apply Rmax_l; simpl in *.
       destruct H0.
       - apply (Rmult_lt_compat_r (/ Cmod (x, y))) in H0.
         rewrite Rinv_r, <- (Rabs_pos_eq (Cmod _)), <- Rabs_inv, <- Rabs_mult in H0.
         all : try (apply Rinv_0_lt_compat; apply Cmod_gt_0).
         all : try apply Cmod_ge_0.
         all : try (unfold not; intros; apply H'; apply Cmod_eq_0; easy).
         apply Rabs_def2 in H0; unfold Rdiv; easy.
       - unfold Cmod in H0; simpl fst in H0; simpl snd in H0.
         assert (H1 : ((Rabs x) * (Rabs x))%R = ((√ (x ^ 2 + y ^ 2)) * (√ (x ^ 2 + y ^ 2)))%R).
         { rewrite H0; easy. }
         rewrite sqrt_def, <- Rabs_mult, Rabs_right in H1.
         apply (f_equal_gen (Rminus (x ^ 2)) (Rminus (x ^ 2))) in H1; auto.
         replace (x ^ 2 - x * x)%R with 0%R in H1 by lra.
         replace (x ^ 2 - (x ^ 2 + y ^ 2))%R with (y ^ 2)%R in H1 by lra. 
         apply (Cpow_nonzero_real _ 2) in H. 
         assert (H'' : False). apply H; rewrite H1; lca.
         easy. 
         replace (x * x)%R with (x ^ 2)%R by lra. 
         assert (H'' := pow2_ge_0 x). lra.
         apply Rplus_le_le_0_compat; apply pow2_ge_0.
Qed.

(* some lemmas about these defs *)

Lemma get_arg_ver : forall (r θ : R),
  0 < r -> 0 <= θ < 2 * PI ->
  get_arg (r * Cexp θ) = θ.
Proof. intros. 
       unfold get_arg; simpl.
       do 2 rewrite Rmult_0_l; unfold Rminus. 
       rewrite Ropp_0, Rplus_0_r, Rplus_0_r, Cmod_mult, 
         Cmod_Cexp, Rmult_1_r, Cmod_R, Rabs_right; try lra. 
       replace (r * cos θ / r)%R with (cos θ)%R.
       2 : unfold Rdiv; rewrite Rmult_comm, <- Rmult_assoc, Rinv_l; try lra.
       destruct (Rle_lt_dec θ PI).
       - assert (H' : 0 <= r * sin θ).
         { apply Rmult_le_pos; try lra.
           apply sin_ge_0; lra. }
         destruct (Rcase_abs (r * sin θ)); try lra.
         apply acos_cos; easy.
       - assert (H' : r * sin θ < 0).
         { rewrite <- (Rmult_0_r r).
           apply Rmult_lt_compat_l; try lra.
           apply sin_lt_0; easy. }
         destruct (Rcase_abs (r * sin θ)); try lra.
         rewrite <- cos_2PI_minus_x.
         rewrite acos_cos; lra.
Qed.

Lemma get_arg_bound : forall (z : C),
  0 <= get_arg z < 2 * PI. 
Proof. intros.
       unfold get_arg.
       case (Rcase_abs (snd z)); intros.
       - destruct z as [x y]; simpl in *.
         assert (H' : y <> 0). lra. 
         apply (fst_div_Cmod_lt x y) in H'.
         apply acos_bound_lt in H'.
         lra.
       - assert (H' := acos_bound (fst z / Cmod z)).
         assert (H0 : PI < 2 * PI).
         { replace PI with (1 * PI)%R by lra. 
           rewrite <- Rmult_assoc, Rmult_1_r.
           apply Rmult_lt_compat_r; try lra.
           apply PI_RGT_0. }
         lra. 
Qed.         

Lemma get_arg_R_pos (r : R) (Hr : 0 < r) : get_arg r = 0.
Proof.
  unfold get_arg.
  simpl.
  destruct (Rcase_abs 0) as [Hfalse | Hge0]; [lra|].
  unfold Rdiv.
  rewrite Cmod_R, Rabs_pos_eq, Rinv_r, acos_1 by lra.
  reflexivity.
Qed.

Lemma get_arg_R_neg (r : R) (Hr : r < 0) : get_arg r = PI.
Proof.
  unfold get_arg.
  simpl.
  destruct (Rcase_abs 0) as [Hfalse | Hge0]; [lra|].
  rewrite Cmod_R, Rabs_left, Rdiv_opp_r by auto.
  unfold Rdiv. 
  rewrite Rinv_r, acos_opp, acos_1 by lra.
  lra.
Qed.

Lemma get_arg_Rmult (r : R) c (Hr : 0 < r) : 
  get_arg (r * c) = get_arg c.
Proof.
  unfold get_arg.
  cbn.
  rewrite 2!Rmult_0_l, Rplus_0_r, Rminus_0_r.
  rewrite 2!if_sumbool.
  apply f_equal_if.
  - destruct (Rcase_abs (snd c)) as [Hlt0 | Hgt0], 
      (Rcase_abs (r * snd c)) as [Hlt0' | Hgt0'];
    [reflexivity | | | reflexivity].
    + exfalso.
      revert Hgt0'.
      apply Rgt_not_ge.
      apply Rlt_gt.
      rewrite Rmult_comm.
      rewrite <-(Rmult_0_r (snd c)); apply Rmult_lt_gt_compat_neg_l; auto.
    + exfalso.
      revert Hlt0'.
      apply Rle_not_lt.
      apply Rmult_le_pos; lra.
  - f_equal.
    f_equal.
    rewrite Cmod_mult, Cmod_R, Rabs_pos_eq by lra.
    unfold Rdiv.
    rewrite Rinv_mult.
    rewrite <- Rmult_assoc.
    f_equal.
    field.
    lra.
  - f_equal.
    rewrite Cmod_mult, Cmod_R, Rabs_pos_eq by lra.
    unfold Rdiv.
    rewrite Rinv_mult.
    rewrite <- Rmult_assoc.
    f_equal.
    field.
    lra.
Qed.


Lemma polar_to_rect_to_polar : forall (p : R * R),
  WF_polar p ->
  rect_to_polar (polar_to_rect p) = p.
Proof. intros.       
       unfold polar_to_rect, rect_to_polar; destruct p; simpl.
       destruct H; simpl in *.
       rewrite Cmod_mult, Cmod_Cexp, Cmod_R, Rabs_right, get_arg_ver, Rmult_1_r; 
         try lra; easy.  
Qed.

Lemma div_subtract_helper : forall (x y : R),
  (x, y) <> C0 ->
  (1 - (x / Cmod (x, y))²)%R = (y² * / (Cmod (x, y))²)%R.
Proof. intros.  
       unfold Rdiv.
       rewrite Rsqr_mult.
       rewrite Rsqr_inv'.
       rewrite <- (Rinv_r ((Cmod (x, y))²)).
       replace (((Cmod (x, y))² * / (Cmod (x, y))² + - (x² * / (Cmod (x, y))²))%R) with
         ( ((Cmod (x, y))² - x²) * / ((Cmod (x, y))²))%R by lra.
       replace ((Cmod (x, y))²) with (x² + y²)%R; try lra. 
       unfold Cmod; simpl fst; simpl snd. 
       rewrite Rsqr_sqrt; try lra. 
       unfold Rsqr; lra.
       apply Rplus_le_le_0_compat; apply pow2_ge_0.
       all : unfold not; intros; apply H.
       unfold Rsqr in H0.
       apply Rmult_integral in H0; apply Cmod_eq_0. 
       destruct H0; easy.
Qed.

Lemma rect_to_polar_to_rect : forall (z : C),
  z <> C0 ->
  polar_to_rect (rect_to_polar z) = z.
Proof. intros.       
       unfold polar_to_rect, rect_to_polar; destruct z as [x y]; simpl.
       unfold get_arg, Cexp. 
       case (Rcase_abs (snd (x, y))); intros; simpl in *.
       - rewrite cos_2PI_minus_x, sin_2PI_minus_x, cos_acos, sin_acos; 
           try apply fst_div_Cmod; auto.
         unfold Cmult; simpl.
         do 2 rewrite Rmult_0_l.
         rewrite div_subtract_helper; auto.
         unfold Rminus.
         rewrite Ropp_0, Rplus_0_r, Rplus_0_r.
         rewrite sqrt_mult, sqrt_inv, sqrt_Rsqr_abs, sqrt_Rsqr_abs, 
           (Rabs_left y), Rabs_right; auto.
         replace (- (- y * / Cmod (x, y)))%R with (y * / Cmod (x, y))%R by lra.
         unfold Rdiv.
         apply injective_projections; simpl.
         all : try (left; apply Rinv_0_lt_compat).
         all : try apply Rsqr_pos_lt.
         all : try (rewrite Rmult_comm, Rmult_assoc, Rinv_l; try lra).
         all : try (unfold not; intros; apply H; apply Cmod_eq_0; easy). 
         assert (H' := Cmod_ge_0 (x, y)); lra.
         apply Rle_0_sqr.
       - rewrite cos_acos, sin_acos; 
           try apply fst_div_Cmod; auto.
         rewrite div_subtract_helper; auto.
         rewrite sqrt_mult, sqrt_inv, sqrt_Rsqr_abs, sqrt_Rsqr_abs, 
           (Rabs_right y), Rabs_right; auto.
         unfold Rdiv, Cmult; simpl. 
         do 2 rewrite Rmult_0_l.
         unfold Rminus; rewrite Ropp_0, Rplus_0_r, Rplus_0_r.
         apply injective_projections; simpl.
         all : try (left; apply Rinv_0_lt_compat).
         all : try apply Rsqr_pos_lt.
         all : try (rewrite Rmult_comm, Rmult_assoc, Rinv_l; try lra).
         all : try (unfold not; intros; apply H; apply Cmod_eq_0; easy). 
         assert (H' := Cmod_ge_0 (x, y)); lra.
         apply Rle_0_sqr.
Qed.

Lemma WF_rect_to_polar : forall (z : C),
  z <> C0 -> WF_polar (rect_to_polar z).
Proof. intros. 
       unfold WF_polar, rect_to_polar; split; simpl.
       apply Cmod_gt_0; easy.
       apply get_arg_bound.
Qed.

Lemma WF_polar_mult : forall (p1 p2 : R * R),
  WF_polar p1 -> WF_polar p2 ->
  WF_polar (polar_mult p1 p2).
Proof. intros. 
       destruct H; destruct H0.
       unfold polar_mult; split.
       - destruct (Rcase_abs (snd p1 + snd p2 - 2 * PI)); simpl.
         all : apply Rmult_lt_0_compat; easy.
       - destruct (Rcase_abs (snd p1 + snd p2 - 2 * PI)); simpl.
         all : lra. 
Qed.         

Lemma WF_polar_pow : forall (p : R * R) (n : nat),
  WF_polar p ->
  WF_polar (polar_pow p n).
Proof. induction n as [| n']; intros. 
       - unfold WF_polar, polar_pow; simpl; split; try lra.
         split; try lra. 
         apply Rmult_lt_0_compat; try lra.
         apply PI_RGT_0.
       - simpl. 
         apply WF_polar_mult; try apply IHn'; easy.
Qed.

Lemma polar_to_rect_mult_compat : forall (p1 p2 : R * R),
  WF_polar p1 -> WF_polar p2 ->   
  polar_to_rect (polar_mult p1 p2) = (polar_to_rect p1) * (polar_to_rect p2).
Proof. intros. 
       unfold polar_to_rect, polar_mult, Cmult.
       destruct p1 as [x1 y1]; destruct p2 as [x2 y2]; simpl. 
       destruct (Rcase_abs (y1 + y2 - 2 * PI)); simpl. 
       - rewrite cos_plus, sin_plus.
         apply injective_projections; simpl; lra.
       - rewrite cos_minus, sin_minus, cos_2PI, sin_2PI, cos_plus, sin_plus. 
         apply injective_projections; simpl; lra.
Qed.

Lemma rect_to_polar_mult_compat : forall (z1 z2 : C),
  z1 <> C0 -> z2 <> C0 -> 
  rect_to_polar (z1 * z2) = polar_mult (rect_to_polar z1) (rect_to_polar z2).
Proof. intros. 
       rewrite <- polar_to_rect_to_polar, polar_to_rect_mult_compat.
       rewrite rect_to_polar_to_rect, rect_to_polar_to_rect; auto.
       3 : apply WF_polar_mult.
       all : apply WF_rect_to_polar; auto.
Qed.

Lemma polar_to_rect_pow_compat : forall (p : R * R) (n : nat),
  WF_polar p ->   
  polar_to_rect (polar_pow p n) = (polar_to_rect p) ^ n.
Proof. induction n as [| n']; intros. 
       - unfold polar_to_rect; simpl. 
         rewrite Cexp_0; lca.
       - simpl. 
         rewrite polar_to_rect_mult_compat, IHn'; auto.
         apply WF_polar_pow; easy. 
Qed.

Lemma rect_to_polar_pow_compat : forall (z : C) (n : nat),
  z <> C0 ->
  rect_to_polar (z ^ n) = polar_pow (rect_to_polar z) n.
Proof. intros.
       rewrite <- polar_to_rect_to_polar, polar_to_rect_pow_compat.
       rewrite rect_to_polar_to_rect; easy.
       2 : apply WF_polar_pow.
       all : apply WF_rect_to_polar; auto.
Qed.       

(******************)
(* nth roots in C *)
(******************)

(* first we need to establish nth roots in R *)

Definition pow_n (n : nat) : R -> R :=
  fun r => (r ^ n)%R.

Lemma pow_n_reduce : forall (n : nat),
  mult_fct (pow_n 1) (pow_n n) = pow_n (S n).
Proof. unfold pow_n; intros. 
       apply functional_extensionality; intros. 
       unfold mult_fct; simpl; lra. 
Qed.

Lemma continuous_const : continuity (pow_n 0).
Proof. unfold continuity, continuity_pt, continue_in, limit1_in, limit_in; intros. 
       exists eps; split; auto; intros. 
       unfold pow_n; simpl in *.
       rewrite R_dist_eq; lra. 
Qed.

Lemma continuous_linear : continuity (pow_n 1).
Proof. unfold continuity, continuity_pt, continue_in, limit1_in, limit_in; intros. 
       exists eps; split; auto; intros. 
       unfold pow_n; simpl in *.
       do 2 rewrite Rmult_1_r; easy. 
Qed.

Lemma continuous_pow_n : forall (n : nat), continuity (pow_n n).
Proof. induction n as [| n'].
       - apply continuous_const. 
       - rewrite <- pow_n_reduce.
         apply continuity_mult.
         apply continuous_linear.
         apply IHn'.
Qed.

Lemma nth_root_nonnegR : forall (r : R) (n : nat),
  0 <= r -> (n > 0)%nat ->
  exists r', 0 <= r' /\ (r' ^ n = r)%R.
Proof. intros. 
       destruct (Req_dec r 0); subst.
       exists 0; split; try lra. 
       rewrite pow_i; easy.
       destruct (Ranalysis5.f_interv_is_interv (pow_n n) 0 (r + 1) r); try lra.
       unfold pow_n; split; simpl.
       rewrite pow_i; easy.
       eapply Rle_trans; try apply (Rle_pow (r + 1) 1 n); try lra; lia.
       intros. 
       apply continuous_pow_n.
       exists x; split; try lra.
       unfold pow_n in a.
       easy.
Qed.

(* now we show the existance of nth roots in C *)

Lemma polar_pow_n : forall (r θ : R) (n : nat),
  0 < r -> 0 <= θ -> (INR n * θ < 2 * PI)%R ->
  polar_pow (r, θ) n = (r ^ n, INR n * θ)%R.
Proof. induction n as [| n']; intros.
       - simpl; rewrite Rmult_0_l; easy.
       - simpl polar_pow. 
         rewrite IHn'; auto.
         unfold polar_mult; simpl fst; simpl snd.
         destruct (Rcase_abs (θ + INR n' * θ - 2 * PI)); try lra. 
         apply injective_projections; simpl; try lra.
         destruct n'; simpl; try lra.
         rewrite S_INR in H1; lra.
         rewrite S_INR in H1; lra.
Qed.

Lemma nth_root_polar : forall (r θ : R) (n : nat), 
  (n > 0)%nat -> 
  WF_polar (r, θ) -> 
  exists p, WF_polar p /\ polar_pow p n = (r, θ).
Proof. intros. 
       destruct H0; simpl in *.
       destruct (nth_root_nonnegR r n) as [r' [H2 H3] ]; try lra; auto.
       assert (0 < r').
       destruct H2; auto; subst.
       destruct n; try easy; simpl in H0.
       rewrite Rmult_0_l in H0; lra.
       exists (r', / (INR n) * θ)%R; split.
       - split; simpl; auto.
         split. 
         apply Rmult_le_pos; try easy. 
         left; apply Rinv_0_lt_compat.
         apply lt_0_INR; auto.
         assert (/ INR n * θ <= θ). 
         rewrite <- Rmult_1_l.
         apply Rmult_le_compat_r; try lra.
         apply (Rmult_le_reg_r (INR n)).
         apply lt_0_INR; lia.
         rewrite Rinv_l, Rmult_1_l.
         replace 1 with (INR 1) by easy.
         apply le_INR; lia.
         apply not_0_INR; destruct n; easy.
         lra. 
       - rewrite polar_pow_n; auto.
         all : try rewrite <- Rmult_assoc, Rinv_r, Rmult_1_l. 
         rewrite H3; easy.
         all : try (apply not_0_INR; destruct n; easy).
         apply Rmult_le_pos; try easy. 
         left; apply Rinv_0_lt_compat.
         apply lt_0_INR; auto.
         easy.
Qed.

Theorem nth_root_C : forall (z : C) (n : nat),
  (n > 0)%nat -> 
  exists z', (Cpow z' n = z)%C.
Proof. intros. 
       destruct (Ceq_dec z C0); subst.
       exists C0; destruct n; simpl; try easy; lca.
       destruct (rect_to_polar z) as [r θ] eqn:E.
       destruct (nth_root_polar r θ n) as [p [H0 H1] ]; auto.
       rewrite <- E.
       apply WF_rect_to_polar; auto.
       exists (polar_to_rect p).
       rewrite <- polar_to_rect_pow_compat; auto.
       rewrite H1, <- E, rect_to_polar_to_rect; easy.
Qed.

Lemma nonzero_nth_root : forall (c c' : C) (n : nat),
  (n > 0)%nat -> c' ^ n = c ->
  c <> C0 -> 
  c' <> C0.
Proof. intros. 
       destruct n; try easy.
       simpl in H0.
       unfold not; intros; apply H1; subst.
       lca.
Qed.


(****)
(*****)
(***)


Definition Clog (c : C) :=
  (ln (Cmod c), get_arg c).

Lemma CexpC_Clog (c : C) (Hc : c <> 0) : 
  CexpC (Clog c) = c.
Proof.
  unfold Clog, CexpC.
  cbn.
  rewrite exp_ln.
  - exact (rect_to_polar_to_rect c Hc).
  - apply Cmod_gt_0, Hc.
Qed.

Lemma Cexp_get_arg_unit (z : C) : Cmod z = 1 ->
  Cexp (get_arg z) = z.
Proof.
  intros Hmod.
  rewrite <- (CexpC_Clog z) at 2 by 
    (intros H; rewrite H, Cmod_0 in Hmod; lra).
  rewrite Cexp_CexpC.
  f_equal.
  unfold Clog.
  rewrite Hmod, ln_1.
  reflexivity.
Qed.
