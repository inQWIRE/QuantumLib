Require Export Complex. 
Require Import List. 

(* TODO: can certainly find these definitions elsewhere, eg in Coq.Reals.Rlimit *)

(* we start by defining limits *) 

Definition limit_at_point (f : C -> C) (a L : C) : Prop :=
  forall ϵ : R, ϵ > 0 -> exists δ, (δ > 0 /\ forall x, x <> a -> Cmod (x - a) < δ -> Cmod (f(x) - L) < ϵ).

Definition continuous_at (f : C -> C) (a : C) : Prop :=
  limit_at_point f a (f a).

Lemma limit_unique : forall (f : C -> C) (a L1 L2 : C),
  limit_at_point f a L1 -> limit_at_point f a L2 ->
  L1 = L2.
Proof. intros. 
       destruct (Ceq_dec (L1 - L2) C0).
       - rewrite <- Cplus_0_r, <- e.
         lca. 
       - unfold limit_at_point in *.
         destruct (H ((Cmod (L1 - L2)) / 2)%R) as [δ1 [H1 H2] ];
         destruct (H0 ((Cmod (L1 - L2)) / 2)%R) as [δ2 [H3 H4] ];
         try (unfold Rdiv; apply Rmult_gt_0_compat; try lra; apply Cmod_gt_0; easy).
         assert (H5 : exists b, b <> a /\ Cmod (b - a) < (Rmin δ1 δ2)).
         { exists (a + ((Rmin δ1 δ2) / 2, 0)%R)%C.
           split. 
           + unfold not; intros. 
             apply (f_equal (Cplus (-a))) in H5.
             rewrite Cplus_assoc, Cplus_opp_l, Cplus_0_l in H5.
             apply (f_equal fst) in H5; simpl in H5.
             apply (f_equal (Rmult 2)) in H5.
             rewrite Rmult_0_r in H5.
             replace (2 * (Rmin δ1 δ2 / 2))%R with (Rmin δ1 δ2) in H5 by lra. 
             apply (Rmin_pos δ1 δ2) in H1; auto.
             lra. 
           + unfold Cplus, Cminus, Copp, Cmod; simpl.
             replace (snd a + 0 + - snd a)%R with 0 by lra. 
             replace (fst a + Rmin δ1 δ2 / 2 + - fst a)%R with (Rmin δ1 δ2 / 2)%R by lra. 
             rewrite Rmult_0_l, Rplus_0_r, Rmult_1_r, sqrt_square. 
             apply Rlt_eps2_eps.
             apply (Rmin_pos δ1 δ2); auto.
             unfold Rdiv.
             apply Rmult_le_pos; try lra. 
             left; apply (Rmin_pos δ1 δ2); auto. }
         destruct H5 as [b [H5 H6] ].
         assert (H7 : Cmod (f b - L1) + Cmod (f b - L2) < Cmod (L1 - L2)).
         rewrite (double_var (Cmod (L1 - L2))).
         apply Rplus_lt_compat.
         apply H2; auto. 
         assert (H' := (Rmin_l δ1 δ2)). lra. 
         apply H4; auto. 
         assert (H' := (Rmin_r δ1 δ2)). lra. 
         assert (H8 :  Cmod (L1 - (f b) + (f b - L2)) <= Cmod (L1 - f b) + Cmod (f b - L2)).
         { apply Cmod_triangle. }
         replace (L1 - f b + (f b - L2)) with (L1 - L2) in H8 by lca. 
         replace (L1 - f b) with (- (f b - L1)) in H8 by lca. 
         rewrite Cmod_opp in H8. lra. 
Qed.

Lemma limit_const : forall (a x : C),
  limit_at_point (fun c => a) x a.
Proof. unfold limit_at_point; intros. 
       exists 1. split; try lra. 
       intros. 
       replace (a - a) with C0 by lca. 
       rewrite Cmod_0.
       easy. 
Qed.


Lemma limit_scale : forall (f : C -> C) (a c L : C),
  limit_at_point f a L ->
  limit_at_point (fun x => c * f x) a (c * L).
Proof. intros. 
       unfold limit_at_point in *.
       intros. 
       destruct (Ceq_dec c 0); subst.
       - exists 1. 
         split; try lra. 
         intros. 
         replace (C0 * f x - C0 * L) with C0 by lca. 
         rewrite Cmod_0; easy.
       - destruct (H (ϵ / Cmod c)%R).
         unfold Rdiv.
         apply Rmult_lt_0_compat; auto. 
         apply Rinv_0_lt_compat.
         apply Cmod_gt_0; auto. 
         exists (x)%R.
         destruct H1.
         split. auto. 
         intros. 
         unfold Cminus.
         rewrite Copp_mult_distr_r, <- Cmult_plus_distr_l, Cmod_mult.
         apply H2 in H3; auto. 
         apply (Rmult_lt_compat_l (Cmod c)) in H3.
         unfold Rdiv in H3.
         rewrite (Rmult_comm ϵ), <- Rmult_assoc, Rinv_r, Rmult_1_l in H3; auto.
         unfold not; intros; apply n.
         apply Cmod_eq_0; auto. 
         apply Cmod_gt_0; auto.
Qed.

Lemma limit_plus : forall (f1 f2 : C -> C) (a L1 L2 : C),
  limit_at_point f1 a L1 -> limit_at_point f2 a L2 ->
  limit_at_point (fun c => f1 c + f2 c) a (L1 + L2).
Proof. unfold limit_at_point. 
       intros. 
       assert (H2 : ϵ / 2 > 0).
       { lra. }
       assert (H3 := H2).
       apply H in H2.
       apply H0 in H3.
       destruct H2 as [δ1 [H2 H4] ]; destruct H3 as [δ2 [H3 H5] ]. 
       exists (Rmin δ1 δ2); split. 
       apply Rmin_Rgt; auto.
       intros. 
       assert (H8 : Cmod (f1 x - L1) < ϵ / 2).
       { apply H4; auto.
         assert (H' := (Rmin_l δ1 δ2)); lra. }
       assert (H9 : Cmod (f2 x - L2) < ϵ / 2).
       { apply H5; auto.
         assert (H' := (Rmin_r δ1 δ2)); lra. }
       apply (Rplus_lt_compat (Cmod (f1 x - L1)) (ϵ / 2) (Cmod (f2 x - L2)) (ϵ / 2)) in H8; auto.
       replace (ϵ / 2 + ϵ / 2)%R with ϵ in H8 by lra.   
       replace (f1 x + f2 x - (L1 + L2))%C with ((f1 x - L1) + (f2 x - L2))%C by lca. 
       assert (H10 :  Cmod (f1 x - L1 + (f2 x - L2)) <= Cmod (f1 x - L1) + Cmod (f2 x - L2)).
       { apply Cmod_triangle. }
       lra. 
Qed.

Lemma limit_mult_0 : forall (f1 f2 : C -> C) (a : C),
  limit_at_point f1 a C0 -> limit_at_point f2 a C0 ->
  limit_at_point (fun c => f1 c * f2 c) a C0.
Proof. intros. 
       unfold limit_at_point in *.
       intros. 
       destruct (H (√ ϵ)); try apply sqrt_lt_R0; auto. 
       destruct (H0 (√ ϵ)); try apply sqrt_lt_R0; auto. 
       destruct H2; destruct H3.
       exists (Rmin x x0).       
       split. 
       apply Rmin_pos; auto.
       intros. 
       unfold Cminus in *.
       rewrite Copp_0, Cplus_0_r in *.
       rewrite Cmod_mult, <- (sqrt_def ϵ); try lra.
       apply Rmult_le_0_lt_compat; try apply Cmod_ge_0.
       all : rewrite <- (Cplus_0_r (_ x1)).
       apply H4; auto.  
       assert (H8 := Rmin_l x x0). lra. 
       apply H5; auto.  
       assert (H8 := Rmin_r x x0). lra. 
Qed.

Lemma limit_mult : forall (f1 f2 : C -> C) (a L1 L2 : C),
  limit_at_point f1 a L1 -> limit_at_point f2 a L2 ->
  limit_at_point (fun c => f1 c * f2 c) a (L1 * L2).
Proof. intros. 
       assert (H' : (fun c => f1 c * f2 c) = 
                    (fun c => ((f1 c - L1) * (f2 c - L2)) + (L1 * f2 c) + (L2 * f1 c) - (L1 * L2))).
       { apply functional_extensionality. 
         intros. lca. }
       replace (L1 * L2) with (C0 + L1 * L2 + L2 * L1 - L1 * L2) by lca. 
       rewrite H'. 
       repeat apply limit_plus.
       unfold Cminus.
       apply limit_mult_0. 
       replace C0 with (L1 + - L1) by lca. 
       apply limit_plus; auto. 
       apply limit_const.
       replace C0 with (L2 + - L2) by lca. 
       apply limit_plus; auto. 
       apply limit_const.
       all : try apply limit_scale; auto.
       apply limit_const.
Qed.

Lemma continuous_plus : forall (f1 f2 : C -> C) (a : C),
  continuous_at f1 a -> continuous_at f2 a -> 
  continuous_at (fun c => f1 c + f2 c)  a.
Proof. intros. 
       unfold continuous_at in *.
       apply (limit_plus f1 f2 a (f1 a) (f2 a)); easy.
Qed.

Lemma continuous_mult : forall (f1 f2 : C -> C) (a : C),
  continuous_at f1 a -> continuous_at f2 a -> 
  continuous_at (fun c => f1 c * f2 c)  a.
Proof. intros. 
       unfold continuous_at in *.
       apply (limit_mult f1 f2 a (f1 a) (f2 a)); easy.
Qed.

Lemma constant_ae_continuous : forall (f : C -> C) (a c : C),
  continuous_at f c -> (forall x, x <> c -> f x = a) -> 
  f c = a. 
Proof. intros.
       unfold continuous_at in H.
       assert (H1 : limit_at_point f c a).
       { unfold limit_at_point.
         intros.  
         exists 1.
         split; try lra. 
         intros. 
         rewrite H0; auto.
         unfold Cminus. 
         rewrite Cplus_opp_r, Cmod_0.
         lra. }
       apply (limit_unique f c); easy.
Qed.
