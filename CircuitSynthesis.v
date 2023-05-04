  
Require Export RingExamples. 

(* Require Export Matrix.
Require Export Quantum. *) 
Require Export RowColOps.



(*
Open Scope genmatrix_scope.
*)

(* TODO: find way to access databases within the section in GenMatrix.v *)


(* TODO: make sure this fix is actually good *)
Notation D8Matrix := (GenMatrix D8). 

Notation CMatrix := (GenMatrix Complex.C). 
(*
Definition D8Mplus {m n : nat} (A B : D8Matrix m n) : D8Matrix m n := 
  @GMplus _ _ _ _ A B.

Definition D8Mopp {m n : nat} (A : D8Matrix m n) : D8Matrix m n := 
  GMopp D8 _ _ _ D8_is_ring A.

Definition D8Mscale {m n : nat} (d : D8) (A : D8Matrix m n) : D8Matrix m n := 
  @scale D8 _ _ _ D8_is_ring m n d A.

Definition D8Mmult {m n o : nat} (A : D8Matrix m n) (B : D8Matrix n o) : D8Matrix m o := 
  @GMmult D8 _ _ _ D8_is_ring m n o A B.

Definition D8Mpow {n : nat} (A : D8Matrix n n) (p : nat) : D8Matrix n n := 
  @GMmult_n D8 _ _ _ D8_is_ring n A p.
*)




Definition D8MtoCM {m n : nat} (A : D8Matrix m n) : CMatrix m n := 
  fun i j => D8toC (A i j).


Lemma D8MtoCM_inj : forall {m n} (A B : D8Matrix m n), 
  D8MtoCM A = D8MtoCM B -> A = B.
Proof. intros. 
       prep_genmatrix_equality.
       apply D8toC_inj. 
       unfold D8MtoCM in H.
       apply (f_equal_gen _ _ x x) in H; 
         try apply (f_equal_gen _ _ y y) in H; auto.
Qed.


Lemma D8MtoCM_plus : forall {m n} (A B : D8Matrix m n), 
  D8MtoCM (A .+ B) = (D8MtoCM A) .+ (D8MtoCM B).
Proof. intros.
       unfold D8MtoCM, GMplus; simpl. 
       prep_genmatrix_equality.
       rewrite D8toC_plus; easy.
Qed.


Lemma D8MtoCM_opp : forall {m n} (A : D8Matrix m n), 
  D8MtoCM (GMopp A) = GMopp (D8MtoCM A). 
Proof. intros. 
       unfold D8MtoCM, GMopp, GenMatrix.scale; simpl. 
       prep_genmatrix_equality.
       autorewrite with D8toC_db.
       lca.
Qed.

Lemma D8MtoCM_mult : forall {m n o} (A : D8Matrix m n) (B : D8Matrix n o), 
  D8MtoCM (GMmult A B) = (D8MtoCM A) × (D8MtoCM B).
Proof. intros. 
       unfold D8MtoCM, GMmult; simpl. 
       prep_genmatrix_equality.
       rewrite (big_sum_func_distr _ D8toC n).
       apply big_sum_eq_bounded; intros.        
       rewrite D8toC_mult; easy.
       intros; simpl.
       rewrite D8toC_plus; easy.
Qed.

Lemma D8MtoCM_pow : forall {m} (A : D8Matrix m m) (p : nat), 
  D8MtoCM (p ⨉ A) = p ⨉ (D8MtoCM A).
Proof. intros. 
       induction p; simpl.
       - prep_genmatrix_equality.
         unfold D8MtoCM, I.
         bdestruct_all; simpl; lca. 
       - rewrite <- IHp, D8MtoCM_mult.
         easy.
Qed.



(* Some basic lemmas. *)

(*
(*  TODO: I shouldn't need to add these since they already exist in GenMatrix.v *)
Lemma D8Mmult_assoc : forall {m n o p} (A : D8Matrix m n) (B : D8Matrix n o) 
                        (C : D8Matrix o p),
  D8Mmult A (D8Mmult B C) = D8Mmult (D8Mmult A B) C.
Proof. intros. 
       unfold D8Mmult.
       rewrite GMmult_assoc.
       easy. 
Qed.

 
Lemma D8Mpow_add : forall {n} (A : D8Matrix n n) (a b : nat),
  WF_GenMatrix D8 _ A -> 
  (D8Mpow A (a + b)) = D8Mmult (D8Mpow A a) (D8Mpow A b).
Proof. intros.
       unfold D8Mpow.
       rewrite GMmult_n_add. auto.
       apply D8_is_comm_ring.
       easy. 
Qed.

Lemma D8Mpow_mult_r : forall {n} (A : D8Matrix n n) (a b : nat),
  @WF_GenMatrix D8 _ n n A -> 
  (D8Mpow A (a * b)) = D8Mpow (D8Mpow A a) b.
Proof. intros.
       unfold D8Mpow.
       rewrite GMmult_n_mult_r. auto.
       apply D8_is_comm_ring.
       easy. 
Qed.
 *)



Open Scope nat_scope.


Definition denom_exp_mat {m n} (A : D8Matrix m n) (k : nat) : Prop :=
  forall i j, i < m -> j < n -> (denom_exp (A i j) k).


Definition least_denom_exp_mat {m n} (A : D8Matrix m n) (k : nat) : Prop :=
  denom_exp_mat A k /\ forall k', denom_exp_mat A k' -> (k <= k')%nat.




(*
 * some helpers to show that there always exists a denom_exp_mat and least_denom_exp_mat: 
 *) 


Lemma get_weaker_denom_exp_mat : forall {m n} (A : D8Matrix m n) (k k' : nat),
  (k <= k')%nat -> 
  denom_exp_mat A k -> denom_exp_mat A k'.
Proof. intros. 
       unfold denom_exp_mat in *; intros. 
       apply (get_weaker_denom_exp (A i j) k k'); auto.
Qed.
    


Lemma DEM_reduce_row : forall {m n} (A : D8Matrix (S m) n) (k : nat),
  denom_exp_mat A k -> denom_exp_mat (reduce_row A m) k.
Proof. intros. 
       unfold denom_exp_mat, reduce_row in *; intros.
       bdestruct (i <? m); try lia. 
       apply H; lia.
Qed.       


Lemma DEM_reduce_col : forall {m n} (A : D8Matrix m (S n)) (k : nat),
  denom_exp_mat A k -> denom_exp_mat (reduce_col A n) k.
Proof. intros. 
       unfold denom_exp_mat, reduce_col in *; intros. 
       bdestruct (j <? n); try lia.
       apply H; lia.
Qed.       


Lemma exists_denom_exp_vec : forall {m} (v : D8Matrix m 1),
  exists k, denom_exp_mat v k.
Proof. induction m.
       - intros. 
         exists 0; easy.
       - intros.
         destruct (IHm (reduce_row v m)). 
         destruct (exists_denom_exp (v m O)).
         exists (x + x0).
         unfold denom_exp_mat in *; intros. 
         bdestruct (i <? m).
         + apply (H i j) in H2; auto.
           apply (get_weaker_denom_exp (v i j) x (x + x0)); try lia. 
           unfold reduce_row in H2.
           bdestruct (i <? m); try lia.
           easy. 
         + bdestruct (i =? m); bdestruct (j =? 0); try lia; subst.
           apply (get_weaker_denom_exp (v m 0) x0 (x + x0)); try lia. 
           easy.
Qed.


Lemma exists_denom_exp_mat : forall {m n} (A : D8Matrix m n),
  exists k, denom_exp_mat A k.
Proof. induction n.
       - intros.
         exists 0; easy.
       - intros.
         destruct (IHn (reduce_col A n)). 
         destruct (exists_denom_exp_vec (get_col A n)).
         exists (x + x0).
         unfold denom_exp_mat in *; intros. 
         bdestruct (j <? n).
         + apply (H i j) in H1; auto.
           apply (get_weaker_denom_exp _ x (x + x0)); try lia. 
           unfold reduce_col in H1.
           bdestruct (j <? n); try lia.
           easy. 
         + apply (H0 i 0) in H1; try lia.
           apply (get_weaker_denom_exp _ x0 (x + x0)); try lia. 
           unfold get_col in H1.
           bdestruct (j =? n); bdestruct (0 =? 0); try lia; subst.
           easy.
Qed.



Lemma denom_exp_vec_dec : forall {m} (v : D8Matrix m 1) (k : nat),
  { denom_exp_mat v k } + { ~ denom_exp_mat v k }.
Proof. induction m.
       - intros; left.
         unfold denom_exp_mat; intros; easy.
       - intros.
         destruct (IHm (reduce_row v m) k). 
         + destruct (denom_exp_dec (v m O) k).
           * left. 
             unfold denom_exp_mat, reduce_row in *; intros. 
             bdestruct (i <? m); bdestruct (i =? m); try lia.
             apply (d i j) in H0; auto.
             bdestruct (i <? m); try lia; auto.
             bdestruct (j =? 0); try lia; subst; auto.
           * right.
             unfold not; intros; apply n.
             apply H; try lia.
         + right.
           unfold not; intros; apply n.
           apply DEM_reduce_row.
           easy.
Qed.



Lemma denom_exp_mat_dec : forall {m n} (A : D8Matrix m n) (k : nat),
  { denom_exp_mat A k } + { ~ denom_exp_mat A k }.
Proof. induction n.
       - intros; left.
         unfold denom_exp_mat; intros; easy.
       - intros.
         destruct (IHn (reduce_col A n) k). 
         + destruct (denom_exp_vec_dec (get_col A n) k).
           * left.
             unfold denom_exp_mat, reduce_col in *; intros. 
             bdestruct (j <? n); bdestruct (j =? n); try lia.
             apply (d i j) in H1; auto.
             bdestruct (j <? n); try lia; auto.
             apply (d0 i 0) in H; auto.
             unfold get_col in H.
             simpl in *; subst; auto. 
           * right.
             unfold not; intros; apply n0.
             unfold denom_exp_mat, get_col in *; intros. 
             bdestruct (j =? 0); try lia. 
             apply H; lia.
         + right.
           unfold not; intros; apply n0.
           apply DEM_reduce_col.
           easy.
Qed.             


Corollary exists_least_denom_exp_mat : forall {m n} (A : D8Matrix m n),
  exists k, least_denom_exp_mat A k.
Proof. intros.
       assert (H' := exists_denom_exp_mat A).
       apply (dec_inh_nat_subset_has_unique_least_element (denom_exp_mat A)) in H'.
       destruct H'; do 2 destruct H. 
       exists x; split; auto.
       intros.  
       destruct (denom_exp_mat_dec A n0).
       left; easy.
       right; easy.
Qed.   


Corollary least_denom_exp_mat_dec : forall {m n} (A : D8Matrix m n) k,
  { least_denom_exp_mat A k } + { ~ least_denom_exp_mat A k }.
Proof. intros. 
       destruct (denom_exp_mat_dec A k).
       - destruct k.
         left; split; intros; auto; lia.
         destruct (denom_exp_mat_dec A k).
         + right.
           unfold not; intros. 
           destruct H.
           apply H0 in d0; lia.
         + left.
           split; auto; intros. 
           bdestruct (k' <=? k)%nat; try lia.
           apply (get_weaker_denom_exp_mat A k' k) in H0; auto.
           easy. 
       - right.  
         unfold not; intros; apply n0.
         apply H.
Qed.



Lemma denom_exp_mat_mult : forall {m n o} (A : D8Matrix m n) (B : D8Matrix n o) (a b : nat),
  denom_exp_mat A a -> denom_exp_mat B b -> 
  denom_exp_mat (GMmult A B) (a + b).
Proof. intros.
       unfold denom_exp_mat, GMmult in *; intros. 
       apply (big_sum_prop_distr _ (fun d =>  denom_exp d (a + b)) n); intros. 
       apply denom_exp_plus; auto.
       unfold denom_exp.
       apply D8isZ8_mult.
       apply D8isZ8_pow. 
       all : try easy.
       apply denom_exp_mult.
       apply H; auto.
       apply H0; auto.
Qed.


Lemma denom_exp_mat_pow : forall {m} (A : D8Matrix m m) (a n : nat),
  denom_exp_mat A a ->
  denom_exp_mat (GMmult_n A n) (n * a).
Proof. intros. 
       induction n; simpl. 
       - unfold denom_exp_mat, denom_exp, I; intros. 
         bdestruct_all; try easy.
       - apply denom_exp_mat_mult; auto.
Qed.


Lemma denom_exp_mat_reduce : forall {m n} (A : D8Matrix m n) (k : nat),
  denom_exp_mat (scale (Z8toD8 root2) A) k <->
  denom_exp_mat A (S k).
Proof. intros; split; intros; unfold denom_exp_mat in *; intros. 
       - apply -> denom_exp_reduce.
         apply H; easy.
       - apply <- denom_exp_reduce.
         apply H; easy.
Qed.       


Lemma rho_to_scale_reduce : forall {m n} (A : D8Matrix m n) (k i j : nat),
  rho (S k) (A i j) = rho k ((scale (Z8toD8 root2) A) i j).
Proof. intros. 
       unfold rho, scale; simpl.
       rewrite D8mult_assoc, (D8mult_comm _ root2); easy.
Qed.



(*
(* more def's for matrices, note the differences since I don't want to define Z8 matrices *)

Definition reducible_mat {m n} (A : D8Matrix m n) : Prop :=
  forall i j, i < m -> j < n -> (D8isZ8 (A i j) /\ reducible (D8toZ8 (A i j))).

Definition irreducible {m n} (A : D8Matrix m n) : Prop :=
  forall i j, i < m -> j < n -> (D8isZ8 (A i j) /\ irreducible (D8toZ8 (A i j))).

Definition twice_reducible_mat {m n} (A : D8Matrix m n) : Prop :=
  forall i j, i < m -> j < n -> (D8isZ8 (A i j) /\ twice_reducible (D8toZ8 (A i j))).
*)








(* Defining some matrices! *)


Definition dI : D8Matrix 2 2 := @I D8 _ _ _ _ 2.

Definition dX : D8Matrix 2 2 :=
  fun x y => 
  match (x, y) with
  | (0, 0) => D80
  | (0, 1) => D81
  | (1, 0) => D81
  | (1, 1) => D80
  | _ => D80
  end.

Definition dZ : D8Matrix 2 2 :=
  fun x y => 
  match (x, y) with
  | (0, 0) => D81
  | (0, 1) => D80
  | (1, 0) => D80
  | (1, 1) => D8opp D81
  | _ => D80
  end.

Definition dH : D8Matrix 2 2 :=
  fun x y => 
  match (x, y) with
  | (0, 0) => root2_recip
  | (0, 1) => root2_recip
  | (1, 0) => root2_recip
  | (1, 1) => D8opp root2_recip
  | _ => D80
  end.

Definition dH_scaled : D8Matrix 2 2 :=
  fun x y => 
  match (x, y) with
  | (0, 0) => D81
  | (0, 1) => D81
  | (1, 0) => D81
  | (1, 1) => D8opp D81
  | _ => D80
  end.


Definition dS : D8Matrix 2 2 :=
  fun x y => 
  match (x, y) with
  | (0, 0) => D81
  | (0, 1) => D80
  | (1, 0) => D80
  | (1, 1) => Z8i
  | _ => D80
  end.

Definition dT : D8Matrix 2 2 :=
  fun x y => 
  match (x, y) with
  | (0, 0) => D81
  | (0, 1) => D80
  | (1, 0) => D80
  | (1, 1) => Z8w
  | _ => D80
  end.


Definition dT_to_nth (n : nat) : D8Matrix 2 2 :=
  fun x y => 
  match (x, y) with
  | (0, 0) => D81
  | (0, 1) => D80
  | (1, 0) => D80
  | (1, 1) => Z8pow Z8w n
  | _ => D80
  end.


(* translation lemmas *)

Lemma D8MtoCM_I : D8MtoCM dI = I 2.
Proof. prep_genmatrix_equality.
       unfold D8MtoCM, dI, I.
       bdestruct_all; simpl; lca.
Qed.

Lemma D8MtoCM_negI : D8MtoCM (GMopp dI) = GMopp (I 2).
Proof. prep_genmatrix_equality.
       unfold D8MtoCM, dI, I, GMopp.
       bdestruct_all; simpl; lca.
Qed.

(* TODO: come up with tactic that does this *)
Lemma D8MtoCM_X : D8MtoCM dX = σx.
Proof. prep_genmatrix_equality.
       destruct x; try destruct x;
       destruct y; try destruct y; simpl; try lca.
Qed.

Lemma D8MtoCM_Z : D8MtoCM dZ = σz.
Proof. prep_genmatrix_equality.
       destruct x; try destruct x;
       destruct y; try destruct y; simpl; try lca.
Qed.

Lemma D8MtoCM_H : D8MtoCM dH = hadamard.
Proof. prep_genmatrix_equality.
       unfold dH, D8MtoCM.
       destruct x; try destruct x;
       destruct y; try destruct y; simpl; try lca; simpl.
       all : autorewrite with D8toC_db; rewrite root2_recip_ver; lca.
Qed.

Lemma D8MtoCM_S : D8MtoCM dS = Sgate.
Proof. prep_genmatrix_equality.
       unfold dS, D8MtoCM.
       destruct x; try destruct x;
       destruct y; try destruct y; simpl; try lca; simpl.
       rewrite Cexp_PI2.
       rewrite Z8toC_i; easy.
Qed.

Lemma D8MtoCM_T : D8MtoCM dT = Tgate.
Proof. prep_genmatrix_equality.
       unfold dT, D8MtoCM.
       destruct x; try destruct x;
       destruct y; try destruct y; simpl; try lca; simpl.
       rewrite Z8toC_w; easy.
Qed.

Lemma D8MtoCM_T_to_nth : forall n, D8MtoCM (dT_to_nth n) = phase_shift ((PI / 4) * (INR n)).
Proof. intros. 
       prep_genmatrix_equality.
       unfold dT_to_nth, D8MtoCM.
       destruct x; try destruct x;
       destruct y; try destruct y; simpl; try lca; simpl.
       rewrite <- Cexp_pow.
       rewrite <- Z8toC_pow.
       apply f_equal_gen; auto; apply f_equal.
       rewrite Z8toC_w; easy.
Qed.


(* Some basic identities *)

Lemma dH_to_dH_scaled : dH = scale root2_recip dH_scaled.
Proof. unfold dH, dH_scaled, scale.
       solve_matrix.
Qed.

Lemma dH_scaled_to_dH : dH_scaled = scale (Z8toD8 root2) dH.
Proof. unfold dH, dH_scaled, scale.
       solve_matrix.
Qed.


Lemma dT_pow_to_dT_to_nth : forall n, GMmult_n dT n = dT_to_nth n.
Proof. intros. 
       apply D8MtoCM_inj.
       rewrite D8MtoCM_pow, D8MtoCM_T_to_nth. 
       rewrite Rmult_comm, <- phase_pow, D8MtoCM_T.
       easy.
Qed.


(* Some pow identities *)

Lemma dA_pow0 : forall A, GMmult_n A 0 = dI.
Proof. intros; simpl.  
       easy. 
Qed.

Lemma dA_pow1 : forall (A : D8Matrix 2 2), 
    @WF_GenMatrix D8 D8_is_monoid 2 2 A -> GMmult_n A 1 = A.
Proof. intros; simpl. 
       rewrite GMmult_1_r; try apply D8_is_comm_ring; 
       easy.
Qed.

(* TODO: automate! *)
Lemma dX_pow2 : GMmult_n dX 2 = dI.
Proof. apply D8MtoCM_inj.
       rewrite D8MtoCM_pow, D8MtoCM_X, D8MtoCM_I; simpl.
       rewrite Mmult_1_r; auto with wf_db. 
       autorewrite with Q_db; easy.
Qed.

Lemma dZ_pow2 : GMmult_n dZ 2 = dI.
Proof. apply D8MtoCM_inj.
       rewrite D8MtoCM_pow, D8MtoCM_Z, D8MtoCM_I; simpl.
       rewrite Mmult_1_r; auto with wf_db.
       autorewrite with Q_db; easy.
Qed.

Lemma dH_pow2 : GMmult_n dH 2 = dI.
Proof. apply D8MtoCM_inj.
       rewrite D8MtoCM_pow, D8MtoCM_H, D8MtoCM_I; simpl.
       rewrite Mmult_1_r; auto with wf_db.
       autorewrite with Q_db; easy.
Qed.

Lemma neg_dI_pow2 : GMmult_n (GMopp dI) 2 = dI.
Proof. apply D8MtoCM_inj.
       rewrite D8MtoCM_pow, D8MtoCM_negI, D8MtoCM_I; simpl.
       rewrite Mmult_1_r; auto with wf_db.
       solve_matrix.
       unfold Mopp.
       auto with wf_db.
Qed.

Lemma dS_pow2 : GMmult_n dS 2 = dZ.
Proof. apply D8MtoCM_inj.
       rewrite D8MtoCM_pow, D8MtoCM_S, D8MtoCM_Z; simpl.
       rewrite Mmult_1_r; auto with wf_db.
       autorewrite with Q_db; easy.
Qed.

Lemma dT_pow2 : GMmult_n dT 2 = dS.
Proof. apply D8MtoCM_inj.
       rewrite D8MtoCM_pow, D8MtoCM_T, D8MtoCM_S; simpl.
       rewrite Mmult_1_r; auto with wf_db.
       autorewrite with Q_db; easy.
Qed.


Lemma dS_pow4 : GMmult_n dS 4 = dI.
Proof. replace 4 with (2*2) by lia.
       rewrite <- GMmult_n_mult_r.
       rewrite dS_pow2, dZ_pow2; easy.
       apply D8_is_comm_ring.
       show_wf; auto.
Qed.

Lemma dT_pow4 : GMmult_n dT 4 = dZ.
Proof. replace 4 with (2*2) by lia.
       rewrite <- GMmult_n_mult_r.
       rewrite dT_pow2, dS_pow2; easy.
       apply D8_is_comm_ring.
       show_wf; auto.
Qed.

Lemma dT_pow8 : GMmult_n dT 8 = dI.
Proof. replace 8 with (2*4) by lia.
       rewrite <- GMmult_n_mult_r.
       rewrite dT_pow2, dS_pow4; easy.
       apply D8_is_comm_ring.
       show_wf; auto.
Qed.





Lemma DEM_dI : denom_exp_mat dI 0.
Proof. unfold denom_exp_mat, denom_exp; intros;
       destruct i; destruct j; try destruct i; try destruct j; try lia; easy.
Qed.

Lemma DEM_dX : denom_exp_mat dX 0.
Proof. unfold denom_exp_mat, denom_exp; intros;
       destruct i; destruct j; try destruct i; try destruct j; easy.
Qed.

Lemma DEM_dZ : denom_exp_mat dZ 0.
Proof. unfold denom_exp_mat, denom_exp; intros;
       destruct i; destruct j; try destruct i; try destruct j; easy.
Qed.

Lemma DEM_dH : denom_exp_mat dH 1.
Proof. unfold denom_exp_mat, denom_exp; intros;
       destruct i; destruct j; try destruct i; try destruct j; easy.
Qed.

Lemma DEM_dH_scale : denom_exp_mat dH_scaled 0.
Proof. unfold denom_exp_mat, denom_exp; intros;
       destruct i; destruct j; try destruct i; try destruct j; easy.
Qed.

Lemma DEM_dS : denom_exp_mat dS 0.
Proof. unfold denom_exp_mat, denom_exp; intros;
       destruct i; destruct j; try destruct i; try destruct j; easy.
Qed.

Lemma DEM_dT : denom_exp_mat dT 0.
Proof. unfold denom_exp_mat, denom_exp; intros;
       destruct i; destruct j; try destruct i; try destruct j; easy.
Qed.


Lemma DEM_mult_by_Z8M : forall {m n o} (A : D8Matrix m n) (B : D8Matrix n o) (k : nat),
  denom_exp_mat A 0 ->
  denom_exp_mat B k ->
  denom_exp_mat (GMmult A B) k.
Proof. intros. 
       rewrite <- (Nat.add_0_l k). 
       apply denom_exp_mat_mult; auto.
Qed.


(* TODO: this does not get every case because sometimes we want dH instead of dH_scaled,
   so there is still a lot of repeated code *)
Lemma DEM_mult_by_HT : forall (u : D8Matrix 2 1) (b k : nat),
  denom_exp_mat u k ->
  denom_exp_mat (GMmult dH_scaled (GMmult (GMmult_n dT b) u)) k.
Proof. intros. 
       apply DEM_mult_by_Z8M.
       apply DEM_dH_scale.
       apply DEM_mult_by_Z8M.
       rewrite <- (Nat.mul_0_r b).
       apply denom_exp_mat_pow.  
       rewrite Nat.mul_0_r.
       apply DEM_dT.
       easy.  
Qed.
  
   
(* this is basically just a bit stronger than Lemma4_case1 *)
Lemma twice_reducible_mat_reduce : forall (u : D8Matrix 2 1) (k : nat),
  @WF_GenMatrix D8 D8_is_monoid 2 1 u -> 
  denom_exp_mat u (S (S k)) -> 
  twice_reducible (rho (S (S k)) (u O O)) -> 
  twice_reducible (rho (S (S k)) (u 1 O)) -> 
  denom_exp_mat u k.
Proof. intros.  
       unfold denom_exp_mat; intros. 
       destruct j; destruct i; try destruct i; try lia;
       apply (twice_reducible_reduce _ k); auto. 
Qed.


Lemma reducible_mat_reduce : forall (u : D8Matrix 2 1) (k : nat),
  @WF_GenMatrix D8 D8_is_monoid 2 1 u -> 
  denom_exp_mat u (S k) -> 
  reducible (rho (S k) (u O O)) -> 
  reducible (rho (S k) (u 1 O)) -> 
  denom_exp_mat u k.
Proof. intros. 
       unfold denom_exp_mat; intros. 
       destruct j; destruct i; try destruct i; try lia;
       apply (reducible_reduce _ k); auto. 
Qed.      







(*
 *    LEMMA 4: 
 *   
 *)


(* There is a lot of repeated code in this section but Lemma 4 has many subcases which are all
   a bit different, so it probably is not worth it to make this more efficient *)



Lemma Lemma4_case1 : forall (u : D8Matrix 2 1) (x1 x2 : Z8) (k : nat),
  @WF_GenMatrix D8 D8_is_monoid 2 1 u -> 
  denom_exp_mat u (S k) -> 
  rho (S k) (u O O) = x1 -> 
  rho (S k) (u 1 O) = x2 -> 
  Z8toF28 (Z8mult root2 x1) = (F0, F0, F0, F0) -> 
  Z8toF28 (Z8mult root2 x2) = (F0, F0, F0, F0) -> 
  denom_exp_mat u k.
Proof. intros. 
       apply (twice_reducible_mat_reduce u); auto; subst.
       apply (get_weaker_denom_exp_mat u (S k) (S (S k))); auto.
       all : apply twice_reducible_iff_0_res; rewrite rho_mult_root2; auto. 
Qed.  



Lemma Lemma4_case2_enum_cases : forall (x : Z8),
  Z8toF28 (Z8mult (Z8conj x) x) = (F0, F1, F0, F1) ->
  Z8toF28 x = (F1, F1, F0, F0) \/ Z8toF28 x = (F0, F1, F1, F0) \/
  Z8toF28 x = (F0, F0, F1, F1) \/ Z8toF28 x = (F1, F0, F0, F1).
Proof. intros.   
       rewrite <- square_norm_ver in H.
       destruct (Z8toF28 x); repeat destruct p. 
       destruct f; destruct f0; destruct f1; destruct f2; try easy; auto.
Qed.


(* takes a bit long. Could take less long if all 16 cases are listed instead of using try *)
Lemma connect_by_w_case2 : forall (x1 x2 : Z8),
  Z8toF28 (Z8mult (Z8conj x1) x1) = (F0, F1, F0, F1) ->
  Z8toF28 (Z8mult (Z8conj x2) x2) = (F0, F1, F0, F1) ->
  (exists b, Z8toF28 (Z8plus x1 (Z8mult (Z8pow Z8w b) x2)) = (F0, F0, F0, F0)).
Proof. intros. 
       destruct (Lemma4_case2_enum_cases x1) as [H1 | [H1 | [H1 | H1]]];
         destruct (Lemma4_case2_enum_cases x2) as [H2 | [H2 | [H2 | H2]]]; auto;
         try (exists 0; simpl; rewrite Z8mult_1_l, Z8toF28_plus, H1, H2; easy);
         try (exists 1; simpl; rewrite Z8mult_1_r, Z8toF28_plus;
                rewrite Z8mult_w_l_F28cycle;
                rewrite H1, H2; easy); 
         try (exists 2; simpl; rewrite Z8mult_1_r, Z8toF28_plus;
                rewrite <- Z8mult_assoc;
                do 2 rewrite Z8mult_w_l_F28cycle;
                rewrite H1, H2; easy);
         try (exists 3; simpl; rewrite Z8mult_1_r, Z8toF28_plus;
                do 2 rewrite <- Z8mult_assoc;
                do 3 rewrite Z8mult_w_l_F28cycle;
                rewrite H1, H2; easy).
Qed.       


Lemma mult_T_H_effect : forall (u : D8Matrix 2 1) (x1 x2 : Z8) (k b i : nat),
  i <= 1 ->
  @WF_GenMatrix D8 D8_is_monoid 2 1 u -> 
  denom_exp_mat u k -> 
  rho k (u O O) = x1 -> 
  rho k (u 1 O) = x2 -> 
  Z8toF28 (rho k (GMmult dH_scaled (GMmult (GMmult_n dT b) u) i 0)) = 
    Z8toF28 (Z8plus x1 (Z8mult (Z8pow Z8w b) x2)).
Proof. intros.
       rewrite dT_pow_to_dT_to_nth. 
       unfold GMmult, GMmult, dH_scaled, dT_to_nth; simpl.   
       destruct i; try destruct i; try lia.
       - naive_lD8a. 
         rewrite rho_plus, rho_mult_z, H2, H3; auto.
         rewrite <- (Nat.add_0_l k). 
         apply denom_exp_mult. 
         unfold denom_exp; simpl. 
         rewrite D8mult_1_l.
         apply D8isZ8_ver; exists (Z8pow Z8w b); easy.
         apply H1; auto.
       - naive_lD8a.
         rewrite rho_plus, Z8toF28_plus, H2; auto.
         replace (D8opp D81) with (Z8toD8 (Z8opp Z81)) by easy. 
         rewrite <- Z8toD8_mult, rho_mult_z; auto.
         rewrite <- Z8mult_assoc, Z8mult_neg1, Z8toF28_opp, F28opp_id, H3, Z8toF28_plus.
         easy.
         rewrite <- (Nat.add_0_l k). 
         apply denom_exp_mult. 
         replace (D8opp D81) with (Z8toD8 (Z8opp Z81)) by easy.
         rewrite <- Z8toD8_mult.
         apply D8isZ8_ver; exists (Z8mult (Z8opp Z81) (Z8pow Z8w b)); simpl.
         rewrite D8mult_1_l.
         easy. 
         apply H1; auto.
Qed.         
        




(* this helps for both case 2 and case 3, so it is its own lemma *)
Lemma Lemma4_cycle_case : forall (u : D8Matrix 2 1) (x1 x2 : Z8) (k b : nat),
  k <> 0%nat -> 
  @WF_GenMatrix D8 D8_is_monoid 2 1 u -> 
  denom_exp_mat u (S k) -> 
  rho (S k) (u O O) = x1 -> 
  rho (S k) (u 1 O) = x2 -> 
  Z8toF28 (Z8plus x1 (Z8mult (Z8pow Z8w b) x2)) = (F0, F0, F0, F0) -> 
  denom_exp_mat (GMmult (GMmult dH (GMmult_n dT b)) u) k.
Proof. intros.  
       destruct k; try easy. 
       apply -> (denom_exp_mat_reduce (GMmult (GMmult dH (GMmult_n dT b)) u)). 
       replace (scale (Z8toD8 root2) (GMmult (GMmult dH (GMmult_n dT b)) u)) with
         (GMmult (scale (Z8toD8 root2) dH) (GMmult (GMmult_n dT b) u)).
       rewrite <- dH_scaled_to_dH.
       remember (GMmult dH_scaled (GMmult (GMmult_n dT b) u)) as v.
       apply (twice_reducible_mat_reduce v); auto; subst.  
       - repeat apply WF_mult.  
         show_wf; easy.
         apply WF_GMmult_n; show_wf; easy.
         auto.
       - apply DEM_mult_by_HT; auto.
       - apply twice_reducible_iff_0_res.
         rewrite (mult_T_H_effect _ (rho (S (S k)) (u 0 0)) (rho (S (S k)) (u 1 0))); auto.
       - apply twice_reducible_iff_0_res.
         rewrite (mult_T_H_effect _ (rho (S (S k)) (u 0 0)) (rho (S (S k)) (u 1 0))); auto.
       - rewrite Mscale_mult_dist_l.
         apply f_equal_gen; auto.
         rewrite GMmult_assoc; easy.
Qed.


Lemma Lemma4_case2 : forall (u : D8Matrix 2 1) (x1 x2 : Z8) (k : nat),
  k <> 0 -> 
  @WF_GenMatrix D8 D8_is_monoid 2 1 u -> 
  denom_exp_mat u (S k) -> 
  rho (S k) (u O O) = x1 -> 
  rho (S k) (u 1 O) = x2 -> 
  Z8toF28 (Z8mult (Z8conj x1) x1) = (F0, F1, F0, F1) -> 
  Z8toF28 (Z8mult (Z8conj x2) x2) = (F0, F1, F0, F1) -> 
  (exists b, 
      denom_exp_mat (GMmult (GMmult (GMmult_n dH 1) (GMmult_n dT b)) u) k).
Proof. intros.
       destruct (connect_by_w_case2 x1 x2) as [b H6]; auto.
       exists b.
       replace (GMmult_n dH 1) with dH.
       apply (Lemma4_cycle_case u x1 x2); auto.
       rewrite dA_pow1; auto; show_wf; easy. 
Qed.




Lemma Lemma4_case3_enum_cases : forall (x : Z8),
  Z8toF28 (Z8mult (Z8conj x) x) = (F1, F0, F0, F0) ->
  (Z8toF28 x = (F1, F0, F0, F0) \/ Z8toF28 x = (F0, F1, F0, F0) \/
   Z8toF28 x = (F0, F0, F1, F0) \/ Z8toF28 x = (F0, F0, F0, F1)) \/
  (Z8toF28 x = (F1, F1, F1, F0) \/ Z8toF28 x = (F0, F1, F1, F1) \/
   Z8toF28 x = (F1, F0, F1, F1) \/ Z8toF28 x = (F1, F1, F0, F1)).
Proof. intros.   
       rewrite <- square_norm_ver in H.
       destruct (Z8toF28 x); repeat destruct p. 
       destruct f; destruct f0; destruct f1; destruct f2; try easy; auto.
Qed.



(* takes a bit long. Could take less long if all 16 cases are listed instead of using try *)
Lemma connect_by_w_case3_0s : forall (x1 x2 : Z8),
  (Z8toF28 x1 = (F1, F0, F0, F0) \/ Z8toF28 x1 = (F0, F1, F0, F0) \/
   Z8toF28 x1 = (F0, F0, F1, F0) \/ Z8toF28 x1 = (F0, F0, F0, F1)) ->
  (Z8toF28 x2 = (F1, F0, F0, F0) \/ Z8toF28 x2 = (F0, F1, F0, F0) \/
   Z8toF28 x2 = (F0, F0, F1, F0) \/ Z8toF28 x2 = (F0, F0, F0, F1)) ->
  (exists b, Z8toF28 (Z8plus x1 (Z8mult (Z8pow Z8w b) x2)) = (F0, F0, F0, F0)).
Proof. intros. 
       destruct H as [H | [H | [H | H]]];
         destruct H0 as [H0 | [H0 | [H0 | H0]]]; auto;
         try (exists 0; simpl; rewrite Z8mult_1_l, Z8toF28_plus, H, H0; easy);
         try (exists 1; simpl; rewrite Z8mult_1_r, Z8toF28_plus;
                rewrite Z8mult_w_l_F28cycle;
                rewrite H, H0; easy);
         try (exists 2; simpl; rewrite Z8mult_1_r, Z8toF28_plus;
                rewrite <- Z8mult_assoc;
                do 2 rewrite Z8mult_w_l_F28cycle;
                rewrite H, H0; easy);
         try (exists 3; simpl; rewrite Z8mult_1_r, Z8toF28_plus;
                do 2 rewrite <- Z8mult_assoc;
                do 3 rewrite Z8mult_w_l_F28cycle;
                rewrite H, H0; easy).
Qed.



(* takes a bit long. Could take less long if all 16 cases are listed instead of using try *)
Lemma connect_by_w_case3_1s : forall (x1 x2 : Z8),
  (Z8toF28 x1 = (F1, F1, F1, F0) \/ Z8toF28 x1 = (F0, F1, F1, F1) \/
   Z8toF28 x1 = (F1, F0, F1, F1) \/ Z8toF28 x1 = (F1, F1, F0, F1)) ->
  (Z8toF28 x2 = (F1, F1, F1, F0) \/ Z8toF28 x2 = (F0, F1, F1, F1) \/ 
   Z8toF28 x2 = (F1, F0, F1, F1) \/ Z8toF28 x2 = (F1, F1, F0, F1)) ->
  (exists b, Z8toF28 (Z8plus x1 (Z8mult (Z8pow Z8w b) x2)) = (F0, F0, F0, F0)).
Proof. intros. 
       destruct H as [H | [H | [H | H]]];
         destruct H0 as [H0 | [H0 | [H0 | H0]]]; auto;
         try (exists 0; simpl; rewrite Z8mult_1_l, Z8toF28_plus, H, H0; easy);
         try (exists 1; simpl; rewrite Z8mult_1_r, Z8toF28_plus;
                rewrite Z8mult_w_l_F28cycle;
                rewrite H, H0; easy);
         try (exists 2; simpl; rewrite Z8mult_1_r, Z8toF28_plus;
                rewrite <- Z8mult_assoc;
                do 2 rewrite Z8mult_w_l_F28cycle;
                rewrite H, H0; easy);
         try (exists 3; simpl; rewrite Z8mult_1_r, Z8toF28_plus;
                do 2 rewrite <- Z8mult_assoc;
                do 3 rewrite Z8mult_w_l_F28cycle;
                rewrite H, H0; easy).
Qed.


(* soo many cases *)
Lemma connect_by_w_case3_noncycle : forall (x1 x2 : Z8), 
  ((Z8toF28 x1 = (F1, F0, F0, F0) \/ Z8toF28 x1 = (F0, F1, F0, F0) \/
   Z8toF28 x1 = (F0, F0, F1, F0) \/ Z8toF28 x1 = (F0, F0, F0, F1)) /\ 
   (Z8toF28 x2 = (F1, F1, F1, F0) \/ Z8toF28 x2 = (F0, F1, F1, F1) \/
   Z8toF28 x2 = (F1, F0, F1, F1) \/ Z8toF28 x2 = (F1, F1, F0, F1))) \/
  ((Z8toF28 x1 = (F1, F1, F1, F0) \/ Z8toF28 x1 = (F0, F1, F1, F1) \/
   Z8toF28 x1 = (F1, F0, F1, F1) \/ Z8toF28 x1 = (F1, F1, F0, F1)) /\
  (Z8toF28 x2 = (F1, F0, F0, F0) \/ Z8toF28 x2 = (F0, F1, F0, F0) \/
   Z8toF28 x2 = (F0, F0, F1, F0) \/ Z8toF28 x2 = (F0, F0, F0, F1))) -> 
  exists d, Z8toF28 (Z8plus x1 (Z8mult (Z8pow Z8w d) x2)) = (F1, F1, F1, F1).
Proof. intros.  
       destruct H as [[[H | [H | [H | H]]] [H0 | [H0 | [H0 | H0]]]] | 
                       [[H | [H | [H | H]]] [H0 | [H0 | [H0 | H0]]]]];
         try (exists 0; simpl; rewrite Z8mult_1_l, Z8toF28_plus, H, H0; easy).
         all : try (exists 1; simpl; rewrite Z8mult_1_r, Z8toF28_plus, 
                      Z8mult_w_l_F28cycle, H, H0; easy).
         all : try (exists 2; simpl; rewrite Z8mult_1_r, Z8toF28_plus;
                      rewrite <- Z8mult_assoc;
                      do 2 rewrite Z8mult_w_l_F28cycle;
                      rewrite H, H0; easy).
         all : try (exists 3; simpl; rewrite Z8mult_1_r, Z8toF28_plus;
                      do 2 rewrite <- Z8mult_assoc;
                      do 3 rewrite Z8mult_w_l_F28cycle;
                      rewrite H, H0; easy).
Qed.


Lemma Lemma4_case3_noncycle_case : forall (u : D8Matrix 2 1) (x1 x2 : Z8) (k d : nat),
  k <> 0 -> 
  @WF_GenMatrix D8 D8_is_monoid 2 1 u -> 
  denom_exp_mat u (S k) -> 
  rho (S k) (u O O) = x1 -> 
  rho (S k) (u 1 O) = x2 -> 
  Z8toF28 (Z8plus x1 (Z8mult (Z8pow Z8w d) x2)) = (F1, F1, F1, F1) -> 
  denom_exp_mat (GMmult (GMmult dH (GMmult_n dT d)) u) (S k).
Proof. intros. 
       apply reducible_mat_reduce. 
       repeat try apply WF_mult; try apply WF_GMmult_n; auto; try show_wf; auto.  
       replace (S (S k)) with ((1 + 0) + (S k)) by lia.
       apply denom_exp_mat_mult; auto.
       apply denom_exp_mat_mult.
       apply DEM_dH.
       rewrite <- (Nat.mul_0_r d).
       apply denom_exp_mat_pow.  
       rewrite Nat.mul_0_r.
       apply DEM_dT. 
       all : rewrite GMmult_assoc, rho_to_scale_reduce, 
           <- Mscale_mult_dist_l, <- dH_scaled_to_dH. 
       all : apply Lemma2_4; apply Lemma2_3; apply Lemma2_2; right; right; right.
       all : rewrite (mult_T_H_effect _ x1 x2); auto.
Qed.
       

Lemma reduce_1s_vector_enum_cases : forall (x : Z8),
  Z8toF28 (Z8mult root2 x) = (F1, F1, F1, F1) -> 
  (Z8toF28 x = (F1, F1, F0, F0) \/ Z8toF28 x = (F0, F1, F1, F0) \/
   Z8toF28 x = (F0, F0, F1, F1) \/ Z8toF28 x = (F1, F0, F0, F1)).
Proof. intros. 
       rewrite <- mult_by_root2_ver in H.
       destruct (Z8toF28 x); repeat destruct p.
       destruct f; destruct f0; destruct f1; destruct f2; try easy; auto.
Qed.  


(* Lemma4_case2 makes this quite short! *)
Lemma reduce_1s_vector : forall (u' : D8Matrix 2 1) (k : nat),
  k <> 0 -> 
  @WF_GenMatrix D8 D8_is_monoid 2 1 u' -> 
  denom_exp_mat u' (S k) -> 
  Z8toF28 (rho (S (S k)) (u' O O)) = (F1, F1, F1, F1) ->  
  Z8toF28 (rho (S (S k)) (u' 1 O)) = (F1, F1, F1, F1) -> 
  (exists b, denom_exp_mat (GMmult (GMmult (GMmult_n dH 1) (GMmult_n dT b)) u') k).  
Proof. intros. 
       rewrite rho_mult_root2 in H2; auto.
       rewrite rho_mult_root2 in H3; auto.
       apply reduce_1s_vector_enum_cases in H2.
       apply reduce_1s_vector_enum_cases in H3.
       apply (Lemma4_case2 _ (rho (S k) (u' O O)) (rho (S k) (u' 1 O))); auto;
         rewrite Z8toF28_mult, Z8conj_F28conj. 
       destruct H2 as [H2 | [H2 | [H2 | H2]]]; rewrite H2; auto.
       destruct H3 as [H3 | [H3 | [H3 | H3]]]; rewrite H3; auto.
Qed.       
       

Lemma Lemma4_enum_cases : forall (z : Z8), 
  Z8toF28 (Z8mult (Z8conj z) z) = (F0, F0, F0, F0) \/
  Z8toF28 (Z8mult (Z8conj z) z) = (F0, F1, F0, F1) \/
  Z8toF28 (Z8mult (Z8conj z) z) = (F1, F0, F0, F0).
Proof. intros. 
       rewrite <- square_norm_ver.
       destruct (Z8toF28 z); repeat destruct p. 
       destruct f; destruct f0; destruct f1; destruct f2; auto.
Qed.


(* putting it all together... *)
Theorem Lemma4 : forall (u : D8Matrix 2 1) (x1 x2 : Z8) (k : nat),
  k <> 0 -> 
  @WF_GenMatrix D8 D8_is_monoid 2 1 u ->
  denom_exp_mat u (S k) -> 
  rho (S k) (u O O) = x1 -> 
  rho (S k) (u 1 O) = x2 -> 
  Z8toF28 (Z8mult (Z8conj x1) x1) = Z8toF28 (Z8mult (Z8conj x2) x2) -> 
  (exists a b c d, 
      denom_exp_mat (GMmult (GMmult (GMmult (GMmult (GMmult_n dH a) (GMmult_n dT b)) 
                                 (GMmult_n dH c)) (GMmult_n dT d)) u) k).
Proof. intros.  
       destruct (Lemma4_enum_cases x1) as [H5 | [H5 | H5]].
       - exists O, O, O, O; simpl.
         repeat rewrite GMmult_1_l; 
           try apply D8_is_comm_ring; try apply WF_I; auto.
         symmetry in H4; rewrite H5 in H4.
         apply Lemma2_3 in H4; apply Lemma2_3 in H5.
         apply (Lemma4_case1 u x1 x2); auto; subst.
       - destruct (Lemma4_case2 u x1 x2 k) as [b H6]; auto. 
         rewrite <- H4, H5; easy. 
         exists 1, b, O, O; simpl in *.        
         repeat rewrite GMmult_1_r; rewrite GMmult_1_r in H6;
           try apply D8_is_comm_ring; try apply WF_I; 
           try apply WF_mult; try apply WF_GMmult_n; try show_wf; auto. 
       - rewrite H5 in H4; symmetry in H4.
         apply Lemma4_case3_enum_cases in H4.
         apply Lemma4_case3_enum_cases in H5.
         destruct H4; destruct H5.
         + destruct (connect_by_w_case3_0s x1 x2) as [b H6]; auto.
           exists 1, b, 0, 0; simpl.
           repeat rewrite GMmult_1_r; 
           try apply D8_is_comm_ring; try apply WF_I; 
           try apply WF_mult; try apply WF_GMmult_n; try show_wf; auto. 
           apply (Lemma4_cycle_case u x1 x2 k b); auto. 
         + destruct (connect_by_w_case3_noncycle x1 x2) as [d H6]; auto.    
           destruct (reduce_1s_vector (GMmult dH (GMmult (GMmult_n dT d) u)) k) as [b H7]; auto.
           repeat apply WF_mult; try apply WF_GMmult_n; auto; show_wf; auto. 
           rewrite <- GMmult_assoc.
           apply (Lemma4_case3_noncycle_case _ x1 x2); auto.
           all : try (rewrite rho_to_scale_reduce, <- Mscale_mult_dist_l, 
                       <- dH_scaled_to_dH, (mult_T_H_effect _ x1 x2); auto).
           exists 1, b, 1, d.
           repeat rewrite GMmult_assoc in *.
           rewrite dA_pow1 in *; try show_wf; auto.
         + destruct (connect_by_w_case3_noncycle x1 x2) as [d H6]; auto.    
           destruct (reduce_1s_vector (GMmult dH (GMmult (GMmult_n dT d) u)) k) as [b H7]; auto.
           repeat apply WF_mult; try apply WF_GMmult_n; auto; show_wf; auto. 
           rewrite <- GMmult_assoc.
           apply (Lemma4_case3_noncycle_case _ x1 x2); auto.
           all : try (rewrite rho_to_scale_reduce, <- Mscale_mult_dist_l, 
                       <- dH_scaled_to_dH, (mult_T_H_effect _ x1 x2); auto).
           exists 1, b, 1, d.
           repeat rewrite GMmult_assoc in *.
           rewrite dA_pow1 in *; try show_wf; auto.
         + destruct (connect_by_w_case3_1s x1 x2) as [b H6]; auto.
           exists 1, b, 0, 0; simpl.
           repeat rewrite GMmult_1_r; 
           try apply D8_is_comm_ring; try apply WF_I; 
           try apply WF_mult; try apply WF_GMmult_n; try show_wf; auto.  
           apply (Lemma4_cycle_case u x1 x2 k b); auto.
Qed.


(* 
 *  LEMMA 5: 
 *
 *)



Inductive Cliff_T_inter (n : nat) : Type :=
  | CTI_w : nat -> Cliff_T_inter n
  | CTI_X : nat -> nat -> Cliff_T_inter n
  | CTI_H : nat -> nat -> Cliff_T_inter n
  | CTI_T : nat -> nat -> Cliff_T_inter n.





Inductive vType (n : nat) : Type :=
  | G : TType n -> vType n
  | Cap : vType n -> vType n -> vType n
  | Arrow : vType n -> vType n -> vType n
  | Err : vType n.








(* 
 *
 *
 *
 *)

