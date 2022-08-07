
(** This file contains more concepts relevent to quantum computing, as well as some more general linear algebra concepts such as Gram-Schmidt and eigenvectors/eigenvalues. *)

Require Import List.       
Require Export Complex.
Require Export Quantum. 
Require Import FTA.


(****************************)
(** * Proving some indentities *)
(****************************)

(* little Ltac for helping with √ 2 *)
Ltac Hhelper :=
   unfold Mmult;
   unfold big_sum;
   unfold I;
   simpl;
   C_field_simplify;
   try lca;
   C_field.

Lemma Y_eq_iXZ : σy = Ci .* σx × σz. Proof. lma'. Qed.
Lemma H_eq_Hadjoint : hadamard† = hadamard. Proof. lma'. Qed.


Hint Rewrite Y_eq_iXZ H_eq_Hadjoint : Q_db.

Lemma ItimesIid : I 2 × I 2 = I 2. Proof. lma'. Qed.      
Lemma XtimesXid : σx × σx = I 2. Proof. lma'. Qed.      
Lemma YtimesYid : σy × σy = I 2. Proof. lma'. Qed.
Lemma ZtimesZid : σz × σz = I 2. Proof. lma'. Qed.
Lemma HtimesHid : hadamard × hadamard = I 2. Proof. lma'; Hhelper. Qed.

Hint Rewrite ItimesIid XtimesXid YtimesYid ZtimesZid HtimesHid : Q_db.

Lemma ZH_eq_HX : σz × hadamard = hadamard × σx. Proof. lma'. Qed.
Lemma XH_eq_HZ : σx × hadamard = hadamard × σz. Proof. lma'. Qed.
Lemma SX_eq_YS : Sgate × σx = σy × Sgate. Proof. lma'; unfold Mmult;
                                                   simpl; rewrite Cexp_PI2; lca. Qed.
Lemma SZ_eq_ZS : Sgate × σz = σz × Sgate. Proof. lma'; unfold Mmult;
                                                   simpl; rewrite Cexp_PI2; lca. Qed.
Lemma cnotX1 : cnot × (σx ⊗ I 2) = (σx ⊗ σx) × cnot. Proof. lma'. Qed.
Lemma cnotX2 : cnot × (I 2 ⊗ σx) = (I 2 ⊗ σx) × cnot. Proof. lma'. Qed.
Lemma cnotZ1 : cnot × (σz ⊗ I 2) = (σz ⊗ I 2) × cnot. Proof. lma'. Qed.
Lemma cnotZ2 : cnot × (I 2 ⊗ σz) = (σz ⊗ σz) × cnot. Proof. lma'. Qed.

Hint Rewrite ZH_eq_HX XH_eq_HZ SX_eq_YS SZ_eq_ZS cnotX1 cnotX2 cnotZ1 cnotZ2 : Q_db.


(*******************************)
(** * Defining orthonormal matrix *)
(*******************************)


Local Open Scope nat_scope. 

Definition orthogonal {n m} (S : Matrix n m) : Prop := 
  forall i j, i <> j -> inner_product (get_vec i S) (get_vec j S) = C0.

Definition orthonormal {n m} (S : Matrix n m) : Prop :=
  orthogonal S /\ (forall (i : nat), i < m -> norm (get_vec i S) = 1%R).

(* to match WF_Unitary *)
Definition WF_Orthonormal {n m} (S : Matrix n m) : Prop := 
  WF_Matrix S /\ orthonormal S. 

Lemma inner_product_is_mult : forall {n} (i j : nat) (S : Square n),
  inner_product (get_vec i S) (get_vec j S) = (S† × S) i j.
Proof. intros. unfold inner_product, get_vec, Mmult, adjoint.
       apply big_sum_eq.
       apply functional_extensionality; intros. simpl.
       reflexivity.
Qed.

Lemma inner_product_comm_conj : forall {n} (v u : Vector n), 
  inner_product v u = Cconj (inner_product u v).
Proof. intros. 
       unfold inner_product.
       assert (H' : forall A : Matrix 1 1, (A 0 0) ^* = A† 0 0).
       { unfold adjoint, Cconj. 
         easy. }
       rewrite H'. 
       rewrite Mmult_adjoint, adjoint_involutive.
       easy.
Qed.



(***************************************************)
(** * showing that all matrices have some eigenvector *)
(***************************************************)

(* We first must define a new type to connect polynomials to matrices *)

Definition MatrixP (m n : nat) := nat -> nat -> Polynomial.

Notation SquareP n := (MatrixP n n).

Definition eval_matP {n m} (A : MatrixP n m) (c : C) : Matrix n m :=
  fun x y => (A x y)[[c]]. 

Definition reduceP {n} (A : SquareP (S n)) (row col : nat) : SquareP n :=
  fun x y => (if x <? row 
              then (if y <? col 
                    then A x y
                    else A x (1+y))
              else (if y <? col 
                    then A (1+x) y
                    else A (1+x) (1+y))).

Lemma reduceP_eval_mat : forall {n} (A : SquareP (S n)) (c : C) (x y : nat),
  reduce (eval_matP A c) x y = eval_matP (reduceP A x y) c.
Proof. intros. 
       prep_matrix_equality.
       unfold reduce, eval_matP, reduceP.
       bdestruct_all; easy. 
Qed.

Fixpoint DeterminantP (n : nat) (A : SquareP n) : Polynomial :=
  match n with 
  | 0 => [C1]
  | S 0 => A 0 0
  | S n' => (big_sum (fun i => [(parity i)] *, (A i 0) *, (DeterminantP n' (reduceP A i 0)))%C n)
  end.

Arguments DeterminantP {n}. 

Lemma DetP_simplify : forall {n} (A : SquareP (S (S n))),
  DeterminantP A =  
  (big_sum (fun i => [(parity i)] *, (A i 0) *, (DeterminantP (reduceP A i 0)))%C (S (S n))).
Proof. intros. easy. Qed.

Lemma Peval_Det : forall {n} (A : SquareP n) (c : C),
  Determinant (eval_matP A c) = (DeterminantP A)[[c]].
Proof. induction n as [| n']. 
       - intros; lca.  
       - intros. 
         destruct n'. 
         + simpl. easy. 
         + rewrite DetP_simplify, Det_simplify.
           rewrite Psum_eval.
           apply big_sum_eq_bounded; intros.
           rewrite reduceP_eval_mat, IHn'.
           do 2 rewrite Pmult_eval.
           repeat apply f_equal_gen; try easy.  
           unfold Peval; lca. 
Qed.

(* not really useful except for in the proof of connect *)
Definition prep_mat {n} (A : Square n) : SquareP n := 
  (fun x y => if (x =? y) && (x <? n) then [A x y; -C1] else [A x y]).

(* we must first show that degree (DeterminantP (prep_mat A)) = n *)

Definition deg_elem_leq_1 {n} (A : SquareP n) : Prop :=
  forall i j, degree (A i j) <= 1.
  
Lemma del1_reduce : forall {n} (A : SquareP (S n)) (i j : nat),
  deg_elem_leq_1 A -> deg_elem_leq_1 (reduceP A i j).
Proof. unfold deg_elem_leq_1, reduceP in *; intros. 
       bdestruct_all; easy.
Qed.

Lemma bound_deg_matP : forall {n} (A : SquareP n),
  deg_elem_leq_1 A -> degree (DeterminantP A) <= n.
Proof. induction n as [| n'].
       - intros.
         unfold degree, compactify; simpl. 
         destruct (Ceq_dec C1 C0); easy.
       - intros.
         destruct n'.
         + simpl. 
           apply H.
         + rewrite DetP_simplify.
           apply Psum_degree; intros. 
           destruct (Peq_dec (A i 0) []).
           rewrite p, Pmult_0_r.
           unfold degree; simpl; lia. 
           destruct (Peq_dec (DeterminantP (reduceP A i 0)) []).
           rewrite p, Pmult_0_r.
           unfold degree; simpl; lia. 
           destruct (Peq_dec [parity i] []).
           rewrite p. 
           unfold degree; simpl; lia.
           destruct (Peq_dec ([parity i] *, A i 0) []).
           rewrite p. 
           unfold degree; simpl; lia.
           repeat rewrite Pmult_degree; auto. 
           assert (H' : degree [parity i] = 0).
           { unfold degree, compactify; simpl.  
             destruct (Ceq_dec (parity i) C0); easy. }
           rewrite H', <- (Nat.add_1_l (S n')), Nat.add_0_l.  
           apply Nat.add_le_mono; auto.
           apply IHn'.
           apply del1_reduce; easy. 
Qed.

(* we now prove prepmat is del1 *)
Lemma del1_prep_mat : forall {n} (A : Square n),
  deg_elem_leq_1 (prep_mat A).
Proof. unfold deg_elem_leq_1, prep_mat; intros.
       destruct ((i =? j) && (i <? n)).
       all : unfold degree, compactify; simpl. 
       destruct (Ceq_dec (- C1) C0); simpl; try lia. 
       all : destruct (Ceq_dec (A i j) C0); simpl; lia.
Qed.

Lemma reduce_prep_mat : forall {n} (A : Square (S n)),
  reduceP (prep_mat A) 0 0 = prep_mat (reduce A 0 0).
Proof. intros. 
       prep_matrix_equality.
       unfold reduceP, reduce, prep_mat.
       bdestruct_all; simpl; try easy. 
Qed.       

(* this got annoyingly long. Probably want to add some helper lemmas at some point *)
Lemma detP_deg : forall {n} (A : Square n),
  degree (DeterminantP (prep_mat A)) = n.
Proof. induction n as [| n'].
       - intros. 
         unfold degree, compactify; simpl. 
         destruct (Ceq_dec C1 C0); easy.
       - intros. 
         destruct n'.  
         + unfold degree, compactify; simpl. 
           destruct (Ceq_dec (- C1) C0); try easy.
           assert (H' : - (- C1) = C0).
           { rewrite e; lca. }
           replace (- - C1) with C1 in H' by lca. 
           apply C1_neq_C0 in H'; easy. 
         + rewrite DetP_simplify.
           assert (H' : forall n f, big_sum f (S n) = f 0 +, big_sum (fun i => f (S i)) n). 
           { intros. 
             induction n. 
             + simpl. 
               destruct (f 0); try easy; simpl. 
             + simpl in *. 
               rewrite IHn, Pplus_assoc; easy. }
           assert (H0 : degree (prep_mat A 0 0) = 1). 
           { unfold prep_mat.
             bdestruct_all; simpl. 
             unfold degree, compactify; simpl. 
             destruct (Ceq_dec (- C1) C0); try easy. 
             assert (H'' := C1_neq_C0).
             replace C1 with (-C1 * -C1)%C in H'' by lca.  
             rewrite e, Cmult_0_l in H''; easy. }
           assert (H1 : degree ([parity 0] *, prep_mat A 0 0 *, 
                                            DeterminantP (reduceP (prep_mat A) 0 0)) = S (S n')).
           { simpl parity.             
             rewrite Pmult_1_l, Pmult_degree, reduce_prep_mat, H0, IHn'.
             easy.
             destruct (Peq_dec (prep_mat A 0 0) []); auto. 
             rewrite p in H0; easy. 
             destruct (Peq_dec (DeterminantP (reduceP (prep_mat A) 0 0)) []); auto. 
             rewrite reduce_prep_mat in *.
             assert (H1 := (IHn' (reduce A 0 0))).
             rewrite p in H1; easy. }
           rewrite H', Pplus_comm, Pplus_degree2; auto. 
           rewrite H1. 
           apply le_lt_n_Sm.
           apply Psum_degree; intros. 
           assert (H2 : prep_mat A (S i) 0 = [A (S i) 0]).
           { unfold prep_mat. 
             bdestruct_all; easy. }
           rewrite H2. 
           replace ([parity (S i)] *, [A (S i) 0]) with [parity (S i) * A (S i) 0]%C. 
           destruct (Peq_dec [(parity (S i) * A (S i) 0)%C] []).
           rewrite p; simpl. 
           unfold degree, compactify; simpl; try lia. 
           destruct (Peq_dec (DeterminantP (reduceP (prep_mat A) (S i) 0)) []).
           rewrite p, Pmult_0_r. 
           unfold degree, compactify; simpl; try lia. 
           rewrite Pmult_degree; auto. 
           rewrite <- Nat.add_0_l.
           apply Nat.add_le_mono.
           destruct (parity (S i) * A (S i) 0)%C eqn:E.
           unfold degree, compactify; simpl. 
           destruct (Ceq_dec (r, r0) C0); simpl; lia. 
           apply bound_deg_matP.
           apply del1_reduce.
           apply del1_prep_mat.
           simpl; rewrite Cplus_0_r. easy. 
Qed.


Lemma connect : forall (n : nat) (A : Square (S n)),
  exists (p : Polynomial), (Polynomial.degree p) > 0 /\
    (forall c : C, Determinant (A .+ (-c .* I (S n))) = p[[c]]).
Proof. intros. 
       exists (DeterminantP (prep_mat A)).
       split; intros. 
       rewrite detP_deg; lia. 
       rewrite <- Peval_Det.
       apply f_equal_gen; try easy. 
       prep_matrix_equality.
       unfold prep_mat, eval_matP, Peval, I, Mplus, scale.
       bdestruct_all; simpl; lca. 
Qed.

Lemma connect2 : forall (n : nat) (A : Square (S n)),
  exists (c : C), det_eq_c C0 (A .+ (-c .* I (S n))).
Proof. intros. 
       destruct (connect n A) as [p [H H0] ].
       destruct (Fundamental_Theorem_Algebra p); auto.
       exists x. 
       split; auto. 
       rewrite H0; easy.
Qed.
     
Lemma exists_eigenvector : forall (n : nat) (A : Square (S n)),
  WF_Matrix A -> 
  exists (c : C) (v : Vector (S n)), WF_Matrix v /\ v <> Zero /\ A × v = c.* v.
Proof. intros. 
       destruct (connect2 n A) as [c H0].
       apply lin_dep_det_eq_0 in H0; auto with wf_db.
       destruct H0 as [v [H1 [H2 H3] ] ].
       exists c, v.
       split; auto. 
       split; auto. 
       rewrite Mmult_plus_distr_r, Mscale_mult_dist_l, Mmult_1_l in H3; auto.
       assert (H4 : A × v .+ (-c .* v) .+ (c .* v) = (c .* v)).
       { rewrite H3. lma. }
       rewrite Mplus_assoc in H4.
       rewrite <- Mscale_plus_distr_l in H4. 
       replace (-c + c)%C with C0 in H4 by lca.
       rewrite <- H4.
       lma. 
Qed.
    
(************************************)
(** * Lemmas relating to forming bases *)
(************************************)


Definition form_basis {n} (v : Vector n) (non_zero : nat) : Matrix n n :=
  fun x y => if (y =? non_zero) 
             then (v x 0)
             else (@e_i n y x 0).

Lemma WF_form_basis : forall {n} (v : Vector n) (x : nat),
  WF_Matrix v -> x < n -> WF_Matrix (form_basis v x).
Proof. unfold WF_Matrix, form_basis, e_i. 
       intros. 
       bdestruct (y =? x).
       apply H.
       destruct H1; auto; lia.
       bdestruct (x0 =? y); try easy.
       bdestruct (x0 <? n); try lia; try easy.
Qed.       

Lemma get_v_in_basis : forall {n} (v : Vector n) (x : nat),
  WF_Matrix v -> get_vec x (form_basis v x) = v.
Proof. intros. 
       prep_matrix_equality.
       unfold get_vec, form_basis.
       bdestruct (y =? 0).
       rewrite <- beq_nat_refl, H0; easy.
       unfold WF_Matrix in H.
       rewrite H; try easy.
       right. 
       destruct y; try lia; try easy.
Qed.

Lemma get_ei_in_basis : forall {n} (v : Vector n) (x y : nat),
  y < n -> y <> x -> get_vec y (form_basis v x) = e_i y.
Proof. intros. 
       prep_matrix_equality.
       unfold get_vec, form_basis.
       bdestruct (y0 =? 0).
       bdestruct (y =? x); try easy.
       rewrite H1; easy.
       unfold e_i.
       bdestruct (x0 =? y); bdestruct (x0 <? n); bdestruct (y0 =? 0); try easy. 
Qed.

Lemma form_basis_ver : forall {n} (v : Vector n) (x : nat),
  v <> Zero -> WF_Matrix v -> v x 0 <> C0 -> x < n -> 
  linearly_independent (form_basis v x) /\ get_vec x (form_basis v x) = v.
Proof. intros.
       destruct n; try lia. split.
       - apply (mat_prop_col_add_many_conv _ _ x (-C1 .* (make_row_zero x v))); 
           try easy; auto with invr_db.
         unfold scale, make_row_zero. 
         bdestruct (x =? x); try lia; lca. 
         apply (mat_prop_col_scale_conv _ _ x (/ (v x 0))); auto with invr_db.
         apply nonzero_div_nonzero; easy.
         assert (H' : forall A : Square (S n), A = I (S n) -> linearly_independent A).
         { intros. rewrite H3. 
           apply lin_indep_invertible; auto with wf_db.
           unfold invertible. exists (I (S n)).
           unfold Minv. 
           split; rewrite Mmult_1_l; auto with wf_db. }
         apply H'. 
         apply mat_equiv_eq; auto with wf_db. 
         apply WF_col_scale. 
         apply WF_col_add_many; try easy.
         apply WF_form_basis; easy. 
         unfold mat_equiv; intros. 
         unfold col_scale, col_add_many, make_row_zero, 
         form_basis, scale, gen_new_vec, get_vec.
         assert (H0' : forall a b : C, a = C0 -> (b + a = b)%C). 
         { intros. rewrite H5. lca. }
         bdestruct (j =? x); bdestruct (j =? i).
         all : try rewrite Msum_Csum. 
         all : try unfold scale. 
         rewrite H5 in *. rewrite <- H6.
         rewrite H0'. 
         unfold I. 
         bdestruct (x =? x); bdestruct (x <? S n); try lia. 
         rewrite Cinv_l; try easy. 
         rewrite big_sum_0_bounded; try easy.
         unfold e_i.
         intros. 
         bdestruct (x0 =? x); try lia; try lca. 
         bdestruct (x =? x0); try lia; lca.          
         rewrite (big_sum_unique (-C1 * (v i 0))%C).
         unfold I. bdestruct (i =? j); try lia; simpl. 
         lca. exists i. split; try easy. 
         split. simpl. 
         rewrite H5 in *.
         bdestruct (i =? x); try lia. 
         unfold e_i. 
         bdestruct (i =? i); bdestruct (i <? S n); simpl; try lia; lca. 
         intros. 
         bdestruct (x' =? x); try lca. 
         simpl; unfold e_i.
         bdestruct (i =? x'); simpl; try lia; lca. 
         rewrite H6.
         all : unfold e_i, I.
         all : bdestruct (i =? i); bdestruct (i <? S n); simpl; try lia; try easy.  
         bdestruct (i =? j); easy.
       - apply get_v_in_basis; easy.
Qed.

Lemma lin_indep_out_of_v : forall {n} (v : Vector n),
  WF_Matrix v -> v <> Zero ->
  exists S : Square n, WF_Matrix S /\ linearly_independent S /\ get_vec 0 S = v. 
Proof. intros. 
       destruct n. 
       - exists Zero. 
         split. easy. 
         split. 
         unfold linearly_independent.
         intros. unfold WF_Matrix in H1. 
         prep_matrix_equality. 
         apply H1; lia.
         prep_matrix_equality. 
         unfold get_vec, Zero.
         unfold WF_Matrix in H. 
         rewrite H; try lia. 
         bdestruct (y =? 0); easy.
       - assert (H' := H).
         apply nonzero_vec_nonzero_elem in H'; try easy.
         destruct H'. 
         exists (col_swap (form_basis v x) x 0).
         assert (H' : x < S n).
         { bdestruct (x <? S n); try easy. 
           unfold WF_Matrix in H.
           unfold not in H1. 
           assert (H' : v x 0 = C0). 
           { apply H. lia. }
           easy. }
         assert (H'' : linearly_independent (form_basis v x) /\ get_vec x (form_basis v x) = v).
         { apply form_basis_ver; try easy. }
         split.
         apply WF_col_swap; try lia; try easy.
         apply WF_form_basis; easy.
         split. 
         + apply_mat_prop lin_indep_swap_invr.  
           apply H3; try lia.
           easy. 
         + rewrite col_swap_diff_order.
           rewrite <- (col_swap_get_vec _ 0 x).
           apply get_v_in_basis. 
           easy. 
Qed.         


(*****************************************************************************************)
(** * Defining and verifying the gram_schmidt algorythm and proving v can be part of an onb *)
(*****************************************************************************************)


(* proj of v onto u *)
Definition proj {n} (u v : Vector n) : Vector n :=
  ((inner_product u v) / (inner_product u u)) .* u.

Definition proj_coef {n} (u v : Vector n) : C :=
  ((inner_product u v) / (inner_product u u)).

Lemma proj_inner_product : forall {n} (u v : Vector n),
  (norm u) <> 0%R -> inner_product u (proj u v) = inner_product u v.
Proof. intros.
       unfold proj, inner_product. 
       distribute_scale.
       unfold scale. 
       unfold Cdiv.  
       rewrite <- Cmult_assoc. 
       rewrite Cinv_l.
       lca. 
       unfold norm, inner_product in H.
       intro. apply H.
       rewrite H0. simpl. 
       rewrite sqrt_0.
       easy.
Qed.

Definition gram_schmidt_on_v (n m : nat) (v : Vector n) (S : Matrix n m) :=
  v .+ (big_sum (fun i => (-C1) .* (proj (get_vec i S) v)) m).

Definition delta_T {n m} (T : Matrix n (S m)) (i : nat) : C := 
  match i =? m with 
  | true => C1
  | _ => - (proj_coef (get_vec i T) (get_vec m T))
  end. 

(* slightly different version thats easier to work with in general case *)
Definition gram_schmidt_on_T (n m : nat) (T : Matrix n (S m)) : Vector n :=
  big_sum (fun i => (delta_T T) i .* (get_vec i T)) (S m).

Lemma WF_gs_on_T : forall {n m} (T : Matrix n (S m)),
  WF_Matrix T -> WF_Matrix (gram_schmidt_on_T n m T).
Proof. intros.
       unfold gram_schmidt_on_T.
       apply WF_Msum; intros. 
       apply WF_scale. 
       unfold get_vec, WF_Matrix in *; intros. 
       destruct H1.
       - rewrite H; auto.
         bdestruct (y =? 0); easy. 
       - bdestruct (y =? 0); try lia; try easy. 
Qed.

Lemma gram_schmidt_compare : forall {n m} (T : Matrix n (S m)),
  inner_product (get_vec m T) (get_vec m T) <> C0 -> 
  gram_schmidt_on_T n m T = gram_schmidt_on_v n m (get_vec m T) (reduce_col T m).
Proof. intros. 
       unfold gram_schmidt_on_T, gram_schmidt_on_v.
       prep_matrix_equality. 
       unfold Mplus. 
       do 2 rewrite Msum_Csum. 
       rewrite Cplus_comm. 
       rewrite <- big_sum_extend_r.
       apply Cplus_simplify.
       - apply big_sum_eq_bounded.
         intros. 
         unfold delta_T.
         bdestruct (x0 =? m); try lia. 
         unfold proj, proj_coef. 
         distribute_scale.
         assert (H' : get_vec x0 (reduce_col T m) = get_vec x0 T).
         { prep_matrix_equality; 
           unfold get_vec, reduce_col.
           bdestruct (x0 <? m); try lia; easy. }
         rewrite H'. unfold scale. lca. 
       - unfold delta_T. 
         bdestruct (m =? m); try lia. 
         unfold scale. lca. 
Qed.

(* here, we show that gs_on_v preserves normalness *)
Lemma gram_schmidt_orthogonal : forall {n m} (v : Vector n) (S : Matrix n m) (i : nat),
  orthonormal S -> i < m -> inner_product (get_vec i S) (gram_schmidt_on_v n m v S) = C0.
Proof. intros.  
       destruct H as [H H1]. 
       unfold orthogonal in H.
       unfold gram_schmidt_on_v. 
       rewrite inner_product_plus_r, inner_product_big_sum_r.
       rewrite (big_sum_unique (-C1 * ⟨ get_vec i S, v ⟩)%C _ m); try lca. 
       exists i. split; try easy.
       split.
       - rewrite inner_product_scale_r.
         rewrite proj_inner_product. 
         lca.
         rewrite H1; auto; lra.
       - intros.
         unfold proj.
         do 2 rewrite inner_product_scale_r.
         apply H in H3. 
         rewrite H3. 
         lca. 
Qed. 

Definition f_to_vec (n : nat) (f : nat -> C) : Vector n :=
  fun i j => if (j =? 0) && (i <? n) then f i else C0. 

Lemma WF_f_to_vec : forall (n : nat) (f : nat -> C), WF_Matrix (f_to_vec n f).
Proof. intros. 
       unfold WF_Matrix, f_to_vec. 
       intros x y [H | H]. 
       - bdestruct (y =? 0); bdestruct (x <? n); try lia; easy. 
       - bdestruct (y =? 0); bdestruct (x <? n); try lia; easy. 
Qed.

Lemma Msum_to_Mmult : forall {n m} (T : Matrix n (S m)) (f : nat -> C),
  big_sum (fun i => f i .* get_vec i T) (S m) = T × (f_to_vec (S m) f).              
Proof. intros. 
       prep_matrix_equality. 
       rewrite Msum_Csum. 
       unfold Mmult. 
       apply big_sum_eq_bounded.
       intros. 
       unfold f_to_vec, get_vec, scale.
       bdestruct (x0 <? S m); bdestruct (y =? 0); try lia; try lca. 
Qed.

(* here, we show gs_on_T is nonzero, true since T is lin indep *)
Lemma gram_schmidt_non_zero : forall {n m} (T : Matrix n (S m)),
  linearly_independent T -> gram_schmidt_on_T n m T <> Zero. 
Proof. intros. 
       unfold not, gram_schmidt_on_T; intros. 
       rewrite (Msum_to_Mmult T (delta_T T)) in H0. 
       unfold linearly_independent in H.
       apply H in H0.
       apply C1_neq_C0.
       assert (H'' : f_to_vec (S m) (delta_T T) m 0 = C0).
       { rewrite H0. easy. }
       rewrite <- H''. 
       unfold f_to_vec, delta_T.
       bdestruct (m <? S m); bdestruct (m =? m); try lia; easy.
       apply WF_f_to_vec.
Qed.

Lemma inner_product_zero_normalize : forall {n} (u v : Vector n),
  inner_product u v = C0 -> inner_product u (normalize v) = C0.
Proof. intros. 
       unfold normalize in *.
       rewrite inner_product_scale_r.
       rewrite H.
       lca. 
Qed.

Lemma get_vec_reduce_append_miss : forall {n m} (T : Matrix n (S m)) (v : Vector n) (i : nat),
  i < m -> get_vec i (col_append (reduce_col T m) v) = get_vec i T.
Proof. intros. 
       prep_matrix_equality. 
       unfold get_vec, col_append, reduce_col.
       bdestruct_all; easy. 
Qed.

Lemma get_vec_reduce_append_hit : forall {n m} (T : Matrix n (S m)) (v : Vector n),
  WF_Matrix v -> get_vec m (col_append (reduce_col T m) v) = v.
Proof. intros.        
       unfold get_vec, col_append, reduce_col.
       prep_matrix_equality. 
       bdestruct (y =? 0).
       - bdestruct_all; subst; easy. 
       - rewrite H; try lia; easy.
Qed.

Lemma get_vec_reduce_append_over : forall {n m} (T : Matrix n (S m)) (v : Vector n) (i : nat),
  WF_Matrix T -> i > m -> 
  get_vec i (col_append (reduce_col T m) v) = Zero.
Proof. intros. 
       prep_matrix_equality. 
       unfold get_vec, col_append, reduce_col.
       bdestruct_all; try easy.  
       rewrite H. easy.
       right. lia. 
Qed.

Lemma extend_onb_ind_step_part1 : forall {n m} (T : Matrix n (S m)),
  WF_Matrix T -> linearly_independent T -> orthonormal (reduce_col T m) ->
  orthonormal (col_append (reduce_col T m) (normalize (gram_schmidt_on_T n m T))). 
Proof. intros. 
       split. 
       - unfold orthogonal. 
         intros. 
         bdestruct (m <? i); bdestruct (m <? j); try lia. 
         + rewrite get_vec_reduce_append_over; try easy.
           unfold inner_product.
           rewrite zero_adjoint_eq, Mmult_0_l.
           easy. 
         + rewrite get_vec_reduce_append_over; try easy.
           unfold inner_product.
           rewrite zero_adjoint_eq, Mmult_0_l.
           easy. 
         + rewrite (get_vec_reduce_append_over _ _ j); try easy.
           unfold inner_product.
           rewrite Mmult_0_r.
           easy. 
         + bdestruct (i =? m); bdestruct (j =? m); try lia. 
           * rewrite H5.
             rewrite get_vec_reduce_append_hit.
             bdestruct (j <? m); bdestruct (m <? j); try lia.  
             rewrite get_vec_reduce_append_miss; try easy.
             rewrite inner_product_comm_conj.
             apply Cconj_simplify.
             rewrite Cconj_involutive, Cconj_0.
             apply inner_product_zero_normalize.
             rewrite gram_schmidt_compare.
             apply (gram_schmidt_orthogonal (get_vec m T) _ j) in H1; try lia.
             rewrite (@get_vec_reduce_col n m j m T) in H1; try lia.
             apply H1.
             assert (H' : WF_Matrix (get_vec m T)).
             { apply WF_get_vec; easy. }
             apply inner_product_zero_iff_zero in H'.
             destruct (Ceq_dec (inner_product (get_vec m T) (get_vec m T)) C0); try easy.
             apply H' in e.
             apply_mat_prop lin_indep_pzf.
             apply H10 in H0; try easy.
             exists m; split; try lia; easy.
             unfold normalize.
             apply WF_scale.
             apply WF_gs_on_T; easy.
           * rewrite H6.
             rewrite get_vec_reduce_append_hit.
             bdestruct (i <? m); bdestruct (m <? i); try lia.  
             rewrite get_vec_reduce_append_miss; try easy.
             apply inner_product_zero_normalize.
             rewrite gram_schmidt_compare.
             apply (gram_schmidt_orthogonal (get_vec m T) _ i) in H1; try lia.
             rewrite (@get_vec_reduce_col n m i m T) in H1; try lia.
             apply H1.
             assert (H' : WF_Matrix (get_vec m T)).
             { apply WF_get_vec; easy. }
             apply inner_product_zero_iff_zero in H'.
             destruct (Ceq_dec (inner_product (get_vec m T) (get_vec m T)) C0); try easy.
             apply H' in e.
             apply_mat_prop lin_indep_pzf.
             apply H10 in H0; try easy.
             exists m; split; try lia; easy.
             unfold normalize.
             apply WF_scale.
             apply WF_gs_on_T; easy.
           * bdestruct (i <? m); bdestruct (j <? m); try lia.  
             rewrite get_vec_reduce_append_miss; try easy.
             rewrite get_vec_reduce_append_miss; try easy.
             unfold orthonormal in H1.
             destruct H1 as [H1 _].
             unfold orthogonal in H1.
             apply (@get_vec_reduce_col n m i m T) in H7.
             apply (@get_vec_reduce_col n m j m T) in H8.
             apply H1 in H2.             
             rewrite H7, H8 in H2; easy. 
       - intros. 
         bdestruct (i =? m); bdestruct (i <? m); try lia. 
         + rewrite H3. 
           rewrite get_vec_reduce_append_hit.
           apply normalized_norm_1.
           assert (H' := H).  
           apply WF_gs_on_T in H'. 
           apply norm_zero_iff_zero in H'. 
           destruct (Req_EM_T (norm (gram_schmidt_on_T n m T)) 0%R); try easy.
           apply H' in e.
           apply gram_schmidt_non_zero in H0; easy.
           unfold normalize. 
           apply WF_scale.
           apply WF_gs_on_T; easy.
         + destruct H1 as [_ H1].
           rewrite get_vec_reduce_append_miss; try lia.         
           rewrite <- (@get_vec_reduce_col n m i m T); try lia. 
           apply H1; lia. 
Qed.     

Definition delta_T' {n m} (T : Matrix n m) (v : Vector n) (size : nat) : nat -> C := 
  fun i => if (i <? size)
           then - (proj_coef (get_vec i T) v) 
           else C0.

Lemma gs_on_T_cols_add : forall {n m1 m2} (T1 : Matrix n m1) (T2 : Matrix n m2) (v : Vector n),
  WF_Matrix v ->
  smash (col_append T1 (gram_schmidt_on_T n m1 (col_append T1 v))) T2 = 
  @col_add_many n ((S m1) + m2) m1 (f_to_vec (m1 + m2) (delta_T' T1 v m1)) 
                             (smash (col_append T1 v) T2).
Proof. intros. 
       prep_matrix_equality. 
       unfold smash, col_append, gram_schmidt_on_T, col_add_many.
       bdestruct (y <? S m1); bdestruct (y =? m1); try lia; try easy.
       unfold delta_T, delta_T', gen_new_vec, f_to_vec, get_vec, scale.
       do 2 rewrite Msum_Csum. 
       rewrite <- big_sum_extend_r.
       bdestruct (m1 =? m1); bdestruct (0 =? 0); try lia. 
       rewrite Cplus_comm.
       apply Cplus_simplify; try lca. 
       unfold get_vec.
       assert (p : S m1 + m2 = m1 + (S m2)). lia. 
       rewrite p. 
       rewrite big_sum_sum.
       assert (p1 : forall a b : C, b = C0 -> (a + b = a)%C). 
       intros. rewrite H4. lca. 
       rewrite p1. 
       apply big_sum_eq_bounded; intros.
       bdestruct (x0 =? m1); bdestruct (x0 <? m1); try lia.
       simpl. 
       bdestruct (x0 <? m1 + m2); try lia. 
       bdestruct (x0 <? S m1); try lia; easy.
       apply (@big_sum_0_bounded C C_is_monoid); intros. 
       bdestruct (m1 + x0 <? m1 + m2); bdestruct (m1 + x0 <? m1); 
         try lia; simpl; lca.
Qed.

Lemma smash_scale : forall {n m1 m2} (T1 : Matrix n m1) (T2 : Matrix n m2) (v : Vector n),
  smash (col_append T1 (normalize v)) T2 = 
  col_scale (smash (col_append T1 v) T2) m1 (/ norm v).
Proof. intros. 
       unfold smash, col_append, normalize, col_scale.
       prep_matrix_equality. 
       bdestruct (y <? S m1); bdestruct (y =? m1); try lia; try easy. 
Qed.

Lemma extend_onb_ind_step_part2 : forall {n m1 m2} (T1 : Matrix n m1) (T2 : Matrix n m2)
                                                   (v : Vector n),
  WF_Matrix T1 -> WF_Matrix T2 -> WF_Matrix v -> v <> Zero -> 
  linearly_independent (smash (col_append T1 v) T2) -> 
  linearly_independent (smash (col_append T1 
                                    (normalize (gram_schmidt_on_T n m1 (col_append T1 v)))) T2).
Proof. intros. 
       rewrite smash_scale. 
       apply_mat_prop lin_indep_scale_invr.
       apply H5.
       unfold not; intros. 
       assert (H4' : (norm (gram_schmidt_on_T n m1 (col_append T1 v)) * 
                     / norm (gram_schmidt_on_T n m1 (col_append T1 v)) = 
                     norm (gram_schmidt_on_T n m1 (col_append T1 v)) * C0)%C).
       { rewrite H6; easy. }
       rewrite Cmult_0_r, Cinv_r in H4'. 
       apply C1_neq_C0; easy.
       unfold not; intros.
       assert (H5' : WF_Matrix (gram_schmidt_on_T n m1 (col_append T1 v))).
       { apply WF_gs_on_T.
         apply WF_col_append; easy. }
       apply norm_zero_iff_zero in H5'.
       apply RtoC_inj in H7.
       rewrite H7 in H5'. 
       apply (gram_schmidt_non_zero (col_append T1 v)).
       apply lin_indep_smash in H3; easy.
       apply H5'; lra.
       rewrite gs_on_T_cols_add; try easy.
       apply_mat_prop lin_indep_add_invr.
       apply invr_col_add_col_add_many in H6.
       inversion H6; subst.
       apply H8; try lia; try easy.  
       unfold f_to_vec, delta_T'.
       bdestruct (m1 <? m1 + m2); bdestruct (m1 <? m1); try lia; easy.
Qed.       

Lemma extend_onb_ind_step : forall {n m1 m2} (T1 : Matrix n m1) (T2 : Matrix n m2) (v : Vector n),
  WF_Matrix T1 -> WF_Matrix T2 -> WF_Matrix v -> 
  linearly_independent (smash (col_append T1 v) T2) -> orthonormal T1 ->
  exists v1, WF_Matrix v1 /\ orthonormal (col_append T1 v1) /\ 
             linearly_independent (smash (col_append T1 v1) T2).
Proof. intros. 
       exists (normalize (gram_schmidt_on_T n m1 (col_append T1 v))).
       split. unfold normalize.
       apply WF_scale.
       apply WF_gs_on_T.
       apply WF_col_append; try easy.
       split. 
       - apply lin_indep_smash in H2.
         assert (H4 := extend_onb_ind_step_part1 (col_append T1 v)).
         assert (H' :  reduce_col (col_append T1 v) m1 = T1).
         { intros. 
           prep_matrix_equality. 
           unfold reduce_col, col_append.
           bdestruct (y <? m1); bdestruct (y =? m1); 
             bdestruct (1 + y =? m1); try lia; try easy.
           all : rewrite H; try lia; rewrite H; try lia; lca. }
         rewrite H' in H4.
         apply H4; try easy.
         apply WF_col_append; easy.
       - apply extend_onb_ind_step_part2; try easy.
         apply lin_indep_smash in H2.
         apply_mat_prop lin_indep_pzf.
         unfold not; intros.
         assert (H' : ~ linearly_independent (col_append T1 v)).
         { apply H5.
           exists m1.
           split; try lia.
           rewrite <- H6. 
           prep_matrix_equality. 
           unfold get_vec, col_append.
           bdestruct (y =? 0); bdestruct (m1 =? m1); subst; try easy; try lia. }
         easy. 
Qed.

Lemma extend_onb : forall (n m2 m1 : nat) (T1 : Matrix n (S m1)) (T2 : Matrix n m2),
  WF_Matrix T1 -> WF_Matrix T2 ->  
  linearly_independent (smash T1 T2) -> orthonormal T1 ->
  exists T2' : Matrix n m2, WF_Matrix T2' /\ orthonormal (smash T1 T2').
Proof. induction m2 as [| m2'].
       - intros. 
         exists Zero.
         split. easy.
         rewrite smash_zero; try easy.
         rewrite plus_0_r.
         apply H2.
       - intros. 
         rewrite (split_col T2) in *.
         assert (H3 := (smash_assoc T1 (get_vec 0 T2) (reduce_col T2 0))). 
         simpl in *.
         rewrite <- H3 in H1. 
         rewrite <- smash_append in H1; try easy.
         assert (exists v1, WF_Matrix v1 /\ orthonormal (col_append T1 v1) /\ 
             linearly_independent (smash (col_append T1 v1) (reduce_col T2 0))).
         { apply (extend_onb_ind_step _ _ (get_vec 0 T2)); try easy.
           apply WF_reduce_col. lia. 
           rewrite (split_col T2). easy.
           apply WF_get_vec.
           rewrite (split_col T2). easy.
           assert (add1 : S (m1 + S m2') = S (S m1) + m2'). { lia. }
           assert (add2 : S (m1 + 1) = S (S m1)). { lia. }
           rewrite add1, add2 in H1.
           apply H1. }
         destruct H4 as [v [H4 [H5 H6] ] ].
         assert (H7 : exists T2' : Matrix n m2', 
                    WF_Matrix T2' /\ orthonormal (smash (smash T1 v) T2')).
         { assert (H'' := (@WF_smash n (S m1) (S O) T1 v)).
           assert (H''' : Nat.add (S m1) (S O) = S (S m1)). lia. 
           apply (IHm2' _ (smash T1 v) (reduce_col T2 0)); try easy.             
           assert (H' : Nat.add m1 (S O) = S m1). lia. 
           unfold Nat.add in H'.
           rewrite H'. 
           rewrite H''' in *.
           apply H''.  
           easy. easy.
           apply (WF_reduce_col 0 T2); try lia. 
           rewrite (split_col T2); easy. 
           assert (add1 : S (Nat.add m1 (S m2')) = S (Nat.add (Nat.add m1 (S O)) m2')). lia. 
           rewrite add1 in H1.
           unfold Nat.add in H1.
           unfold Nat.add.
           rewrite <- smash_append; try easy.
           assert (add2 : Nat.add (S (S m1)) m2' = S (Nat.add (Nat.add m1 (S O)) m2')). lia. 
           assert (add3 : (S (S m1)) = S (Nat.add m1 (S O))). lia. 
           rewrite add2, add3 in H6.
           unfold Nat.add in H6.
           apply H6.
           rewrite <- smash_append; try easy.
           assert (add4 : S (S m1) = S (Nat.add m1 (S O))). lia. 
           rewrite add4 in H5.
           unfold Nat.add in H5.
           apply H5. }
         destruct H7. 
         rewrite smash_assoc in H7.
         exists (smash v x).
         split. 
         assert (H' : S m2' = 1 + m2'). lia. rewrite H'.
         apply WF_smash; try easy.
         assert (add5 : Nat.add (Nat.add (S m1) (S O)) m2' = S (Nat.add m1 (S m2'))). lia.
         assert (add6 : (Init.Nat.add (S O) m2') = (S m2')). lia. 
         rewrite add5, add6 in H7.    
         apply H7. 
         apply WF_get_vec.
         rewrite (split_col T2).
         easy. 
Qed.

Lemma get_vec_vec : forall {n} (v : Vector n),
  WF_Matrix v -> get_vec 0 v = v.
Proof. intros. 
       unfold get_vec.
       prep_matrix_equality. 
       bdestruct (y =? 0). 
       - rewrite H0; easy.
       - unfold WF_Matrix in H.  
         rewrite H; try easy.
         right. 
         bdestruct (y <? 1); try lia.          
Qed.

Lemma orthonormal_normalize_v : forall {n} (v : Vector n),
  v <> Zero -> WF_Matrix v -> orthonormal (normalize v).
Proof. intros. 
       split. 
       unfold orthogonal, inner_product. 
       intros. destruct i.
       + assert (H' : get_vec j (normalize v) = Zero).
         { prep_matrix_equality. 
           unfold get_vec, normalize.
           bdestruct (y =? 0); try easy.
           unfold scale. rewrite H0; try lia; lca. }
         rewrite H', Mmult_0_r; easy.
       + assert (H' : get_vec (S i) (normalize v) = Zero).
         { prep_matrix_equality. 
           unfold get_vec, normalize.
           bdestruct (y =? 0); try easy.
           unfold scale. rewrite H0; try lia; lca. }
         rewrite H', zero_adjoint_eq, Mmult_0_l; easy.
       + intros. 
         destruct i; try lia. 
         rewrite get_vec_vec.
         apply normalized_norm_1.
         unfold not; intros; apply H.
         apply norm_zero_iff_zero in H0.
         apply H0; easy.
         unfold normalize.
         auto with wf_db.
Qed.

(* the steps here are a bit confusing, but we use these lemmas to 
   prove the following useful fact *)
Theorem onb_out_of_v : forall {n} (v : Vector n),
  WF_Matrix v -> v <> Zero -> 
  exists T : Square n, WF_Orthonormal T /\ get_vec 0 T = normalize v.
Proof. intros. 
       destruct n as [| n].
       - assert (H' : v = Zero).
         prep_matrix_equality.
         rewrite H; try lia; easy.
         easy.
       - assert (H' : WF_Matrix (normalize v)). 
         { unfold normalize. 
           auto with wf_db. }
         apply lin_indep_out_of_v in H'; try easy.
         destruct H' as [S0 [H1 [H2 H3] ] ].
         rewrite (split_col S0) in H2.
         apply (extend_onb (S n) n 0 (get_vec 0 S0) (reduce_col S0 0)) in H2. 
         destruct H2 as [T [H4 H5] ].
         exists (smash (get_vec 0 S0) T). split; try easy.
         assert (H' : S n = 1 + n). lia. rewrite H'.
         unfold WF_Orthonormal; split. 
         apply WF_smash; try easy.
         apply WF_get_vec; easy.
         easy.
         apply WF_get_vec; easy.
         apply (WF_reduce_col 0) in H1; try easy; lia.  
         rewrite H3; apply orthonormal_normalize_v; easy.
         unfold not; intros; apply H0.
         prep_matrix_equality. 
         assert (H2 : (normalize v) x y = C0).
         { rewrite H1; easy. }
         unfold Zero; simpl. 
         unfold normalize, scale in H2.
         destruct (Ceq_dec (v x y) C0); try easy.
         assert (H3 : norm v <> 0%R).
         { unfold not; intros.
           apply norm_zero_iff_zero in H.
           apply H in H3; easy. }
         assert (H4 : / norm v <> C0).
         { destruct (Ceq_dec (/ norm v) C0); try easy.
           assert (H4' : (norm v * / norm v = norm v * C0)%C).
           rewrite e; easy.
           rewrite Cmult_0_r, Cinv_r in H4'. 
           assert (H5 : C1 <> C0). 
           { apply C0_fst_neq.
             simpl. 
             apply R1_neq_R0. }
           easy.
           apply RtoC_neq; easy. }
         apply (Cmult_neq_0 _ (v x y)) in H4; easy.
Qed.


(***********************************************)
(** * some useful facts about unitary matrices *)
(***********************************************)


Lemma unit_is_orthonormal : forall {n} (U : Square n),
  WF_Unitary U <-> WF_Orthonormal U.
Proof. intros n U. split. 
       - split; try apply H.
         split. 
         * unfold orthogonal. intros.
           rewrite inner_product_is_mult.
           destruct H as [H1 H].   
           rewrite H. 
           unfold I. bdestruct (i =? j); try lia; easy.
         * intros. unfold norm, inner_product.
           assert (H1 : ((get_vec i U) † × get_vec i U) 0%nat 0%nat = 
                        inner_product (get_vec i U) (get_vec i U)).
           { unfold inner_product. reflexivity. }
           rewrite H1. rewrite inner_product_is_mult.
           destruct H.
           rewrite H2. unfold I.
           bdestruct (i =? i); bdestruct (i <? n); try lia. 
           simpl. apply sqrt_1. 
       - intros [H1 [H2 H3] ]. 
         split; try easy.
         apply mat_equiv_eq; auto with wf_db.
         unfold mat_equiv; intros. 
         rewrite <- inner_product_is_mult.
         unfold orthogonal in H2. unfold I.
         bdestruct (i =? j); bdestruct (i <? n); try lia; subst. 
         * unfold norm, inner_product in H3.
           apply H3 in H0.
           apply eq_sym in H0.
           apply sqrt_1_unique in H0.
           unfold RtoC.
           apply c_proj_eq; try easy.
           simpl. 
           apply norm_real. 
         * rewrite H2; try nia; easy.
Qed.

Lemma unit_out_of_v : forall {n} (v : Vector n) (x : nat),
  WF_Matrix v -> v <> Zero -> 
  exists S : Square n, WF_Unitary S /\ get_vec 0 S = normalize v.
Proof. intros.
       apply onb_out_of_v in H; try easy.
       destruct H as [S [H1 H2] ].
       exists S. split; try easy.
       apply unit_is_orthonormal; easy.
Qed.

Lemma det_by_unit : forall {n} (A B X : Square n),
  WF_Matrix A -> WF_Matrix B -> 
  WF_Unitary X -> (forall i, A × (get_vec i X) = B × (get_vec i X)) -> A = B.
Proof. intros. assert (H' : A × X = B × X).
       { apply det_by_get_vec. intros.
         do 2 (rewrite <- get_vec_mult).
         apply H2. }
       rewrite <- Mmult_1_r.
       rewrite <- (Mmult_1_r _ _ A).
       destruct H1.
       apply Minv_flip in H3; auto with wf_db.
       rewrite <- H3.
       do 2 (rewrite <- Mmult_assoc).
       rewrite H'.
       reflexivity. 
       all : easy. 
Qed.


(***********************************************************************************)
(** * We now define diagonal matrices and diagonizable matrices, proving basic lemmas *)
(***********************************************************************************)

Definition WF_Diagonal {n : nat} (A : Square n) : Prop := 
  WF_Matrix A /\ forall i j, i <> j -> A i j = C0.


Lemma diag_Zero : forall n : nat, WF_Diagonal (@Zero n n).
Proof. intros n. split; auto with wf_db. Qed.

Lemma diag_I : forall n : nat, WF_Diagonal (I n). 
Proof. 
  intros.
  split; auto with wf_db.
  intros.
  unfold I. 
  bdestruct (i =? j); try lia; try easy. 
Qed.

Lemma diag_I1 : WF_Diagonal (I 1). Proof. apply diag_I. Qed.

Lemma diag_scale : forall {n : nat} (r : C) (A : Square n), 
  WF_Diagonal A -> WF_Diagonal (r .* A).
Proof.
  intros n r A [H H0]. 
  split; auto with wf_db.
  intros. 
  unfold scale. 
  rewrite H0; try lca; easy.
Qed.

Lemma diag_plus : forall {n} (A B : Square n), 
  WF_Diagonal A -> WF_Diagonal B -> WF_Diagonal (A .+ B).
Proof.
  intros n A B [H H0] [H1 H2]. 
  split; auto with wf_db. 
  intros. 
  unfold Mplus.
  rewrite H0, H2; try easy; lca.
Qed.

Lemma diag_mult : forall {n : nat} (A B : Square n), 
  WF_Diagonal A -> WF_Diagonal B -> WF_Diagonal (A × B).
Proof.
  intros n A B [H H0] [H1 H2].
  split; auto with wf_db. 
  intros.
  unfold Mmult. 
  apply (@big_sum_0 C C_is_monoid).
  intro.
  bdestruct (x =? i).
  + rewrite H2; try lia; lca. 
  + rewrite H0, Cmult_0_l.    
    reflexivity. auto.
Qed.

(* short lemma to prove diag_kron *)
Lemma div_mod_eq : forall (a b m : nat),
  m <> 0 -> (a / m = b / m) -> (a mod m = b mod m) -> a = b.
Proof. intros a b m H0 Hdiv Hmod.
       rewrite (Nat.mod_eq a m), (Nat.mod_eq b m) in Hmod.
       rewrite Hdiv in Hmod.
       assert (H : m * (b / m) + (a - m * (b / m)) = m * (b / m) + (b - m * (b / m))).
       { rewrite Hmod. reflexivity. }
       rewrite <- (le_plus_minus  (m * (b / m)) a) in H.
       rewrite <- (le_plus_minus  (m * (b / m)) b) in H.
       apply H.
       apply Nat.mul_div_le; apply H0.
       rewrite <- Hdiv; apply Nat.mul_div_le; apply H0.
       apply H0. apply H0.
Qed.

Lemma diag_kron : forall {n m : nat} (A : Square n) (B : Square m), 
                  WF_Diagonal A -> WF_Diagonal B -> WF_Diagonal (A ⊗ B).
Proof.
  intros n m A B [H H0] [H1 H2].
  destruct m.
  rewrite (WF0_Zero_l 0); try easy.
  auto with wf_db.
  split; auto with wf_db.
  unfold kron.
  intros.
  bdestruct (i / (S m) =? j / (S m)).
  - bdestruct (i mod (S m) =? j mod (S m)).
    + apply (div_mod_eq i j (S m)) in H5; try easy.
    + rewrite H2; try lca; easy. 
  - rewrite H0; try lca; easy. 
Qed.

Lemma diag_transpose : forall {n : nat} (A : Square n), 
                     WF_Diagonal A -> WF_Diagonal A⊤. 
Proof. intros n A [H H0]. 
       split; auto with wf_db.
       intros. 
       unfold transpose.  
       apply H0. auto. 
Qed.

Lemma diag_adjoint : forall {n : nat} (A : Square n), 
      WF_Diagonal A -> WF_Diagonal A†. 
Proof. intros n A [H H0]. 
       split; auto with wf_db.
       unfold  adjoint, Cconj. 
       intros. 
       rewrite H0. lca. auto.
Qed.

Lemma diag_kron_n : forall (n : nat) {m : nat} (A : Square m),
   WF_Diagonal A ->  WF_Diagonal (kron_n n A).
Proof.
  intros.
  induction n; simpl.
  - apply diag_I.
  - rewrite Nat.mul_comm. 
    apply (@diag_kron (m^n) m _ A). 
    apply IHn. apply H. 
Qed.

Lemma diag_big_kron : forall n (l : list (Square n)), 
                        (forall A, In A l -> WF_Diagonal A) ->
                         WF_Diagonal (⨂ l). 
Proof.                         
  intros.
  induction l.
  - simpl. apply diag_I.
  - simpl. apply (@diag_kron _ (n^(length l)) a (⨂ l)). 
    apply H.
    left. easy. 
    apply IHl. 
    intros A H'. apply H.
    simpl. auto.
Qed. 

Lemma diag_Mmult_n : forall n {m} (A : Square m),
   WF_Diagonal A -> WF_Diagonal (Mmult_n n A).
Proof.
  intros.
  induction n; simpl.
  - apply diag_I.
  - apply diag_mult; assumption. 
Qed.

(** defining what it means to be diagonalizable *)
Definition WF_Diagonalizable {n : nat} (A : Square n) : Prop :=
  WF_Matrix A /\ (exists (X X' B: Square n), 
    WF_Diagonal B /\ WF_Matrix X /\ WF_Matrix X' /\ X × X' = I n /\ B = X × A × X').

Lemma diag_imps_diagble : forall {n} (A : Square n),
  WF_Diagonal A -> WF_Diagonalizable A.
Proof. intros n A [H H0]. unfold WF_Diagonalizable.
       split; auto.
       exists (I n), (I n), A. 
       split.
       split; auto. 
       split; auto with wf_db.
       split; auto with wf_db.
       rewrite Mmult_1_l; auto with wf_db.  
       rewrite Mmult_1_l; auto with wf_db.  
       rewrite Mmult_1_r; auto with wf_db.  
Qed.

Lemma diagble_Zero : forall n : nat, WF_Diagonalizable (@Zero n n).
Proof. intros. apply diag_imps_diagble. 
       apply diag_Zero.
Qed.

Lemma diagble_I : forall n : nat, WF_Diagonalizable (I n). 
Proof. intros. apply diag_imps_diagble.
       apply diag_I.
Qed.

Lemma diagble_I1 : WF_Diagonal (I 1). Proof. apply diag_I. Qed.
  
Lemma diagble_scale : forall {n : nat} (r : C) (A : Square n), 
  WF_Diagonalizable A -> WF_Diagonalizable (r .* A).
Proof.
  intros n r A [H H0].  
  split; auto with wf_db.
  do 3 (destruct H0).
  destruct H0 as [H1 [H2 [H3 [H4 H5] ] ] ].
  exists x, x0, (r .* x1); split. 
  apply diag_scale; apply H1. 
  split; try easy.
  split; try easy. 
  split. 
  apply H4.
  rewrite Mscale_mult_dist_r;
  rewrite Mscale_mult_dist_l.
  rewrite H5.
  reflexivity. 
Qed.

Lemma diagble_switch : forall {n : nat} (A B X X' : Square n),
  WF_Matrix A -> WF_Matrix B -> WF_Matrix X -> WF_Matrix X' -> 
  X × X' = I n -> B = X × A × X' ->
  A = X' × B × X.
Proof. intros. 
       rewrite H4. 
       repeat rewrite <- Mmult_assoc. 
       apply Minv_flip in H3; auto.
       rewrite H3, Mmult_1_l; auto.
       rewrite Mmult_assoc. 
       rewrite H3, Mmult_1_r; auto. 
Qed.       

(**************************************)
(** * Defining Cprod, similar to big_sum *)
(**************************************)

(* could define this using the multiplicative monoid on C, but this would 
   lead to confusing notation, so I just left it *)
Fixpoint Cprod (f : nat -> C) (n : nat) : C := 
  match n with
  | 0 => C1
  | S n' => (Cprod f n' *  f n')%C
  end.


Lemma Cprod_0_bounded : forall (f : nat -> C) (n : nat),
  (exists i, i < n /\ f i = C0) -> Cprod f n = C0. 
Proof. intros. 
       induction n as [| n'].
       - destruct H; lia.
       - destruct H as [i [H1 H2] ].
         bdestruct (i <? n'); bdestruct (i =? n'); try lia. 
         + simpl. rewrite IHn'; try lca.
           exists i. easy.
         + simpl. rewrite <- H0.
           rewrite H2; lca.
Qed.

Lemma Cprod_eq_bounded : forall (f g : nat -> C) (n : nat),
  (forall i : nat, i < n -> f i = g i) -> Cprod f n = Cprod g n.
Proof. intros.
       induction n as [| n'].
       - easy.
       - simpl.
         rewrite IHn', H; try lia; try easy.
         intros. apply H; lia. 
Qed.

Lemma Cprod_extend_r : forall (f : nat -> C) (n : nat),
  (Cprod f n * f n)%C = Cprod f (S n).
Proof. easy. Qed.

Lemma Cprod_extend_l : forall (f : nat -> C) (n : nat),
  (f 0 * (Cprod (fun x => f (S x)) n))%C = Cprod f (S n).
Proof. intros.
       induction n.
       + simpl; lca.
       + simpl.
         rewrite Cmult_assoc.
         rewrite IHn.
         simpl.
         reflexivity.
Qed.

Lemma Cprod_product : forall (f g h : nat -> C) (n : nat),
  (forall i, i < n -> h i = (f i * g i)%C) -> ((Cprod f n) * (Cprod g n))%C = Cprod h n.
Proof. induction n.
       + intros. lca. 
       + intros. simpl. 
         rewrite <- IHn, H; try lca; try lia. 
         intros. apply H; try lia. 
Qed.

(************************************)
(** * Defining upper triangular matrix *) 
(************************************)

Definition upper_triangular {n} (A : Square n) : Prop :=
  forall i j, i > j -> A i j = C0.

Lemma up_tri_Zero : forall n : nat, upper_triangular (@Zero n n).
Proof. intros n. unfold upper_triangular. reflexivity. Qed.

Lemma up_tri_I : forall n : nat, upper_triangular (I n). 
Proof. 
  unfold upper_triangular, I; intros.
  bdestruct (i =? j); try lia; easy.
Qed.

Lemma up_tri_I1 : upper_triangular (I 1). Proof. apply up_tri_I. Qed.

Lemma up_tri_scale : forall {n : nat} (r : C) (A : Square n), 
  upper_triangular A -> upper_triangular (r .* A).
Proof.
  unfold upper_triangular, scale.
  intros.
  rewrite H; try lca; easy.
Qed.

Lemma up_tri_plus : forall {n} (A B : Square n), 
  upper_triangular A -> upper_triangular B -> upper_triangular (A .+ B).
Proof.
  unfold upper_triangular, Mplus.
  intros n A B H H0 i j H1. 
  rewrite H, H0; try lca; easy. 
Qed.


Lemma up_tri_mult : forall {n : nat} (A B : Square n), 
  upper_triangular A -> upper_triangular B -> upper_triangular (A × B).
Proof.
  unfold upper_triangular, Mmult.
  intros n A B H H0 i j D.
  apply (@big_sum_0 C C_is_monoid).
  intros x.
  bdestruct (x <? i); bdestruct (j <? x); try lia.
  + rewrite H; try lca; lia.
  + rewrite H; try lca; lia.
  + rewrite H0; try lca; lia.
Qed.

Lemma up_tri_reduce_0 : forall {n : nat} (A : Square (S n)),
  upper_triangular A -> upper_triangular (reduce A 0 0).
Proof. 
  unfold upper_triangular, reduce.
  intros. 
  bdestruct (i <? 0); bdestruct (j <? 0); try lia.
  apply H; lia. 
Qed.

Lemma det_up_tri_diags : forall {n : nat} (A : Square n),
  upper_triangular A -> 
  Determinant A = Cprod (fun i => A i i) n.
Proof. induction n as [| n'].
       - easy.
       - intros. simpl. 
         destruct n' as [| n''].
         + lca. 
         + assert (H' : (Cprod (fun i : nat => A i i) (S n'') * A (S n'') (S n'') =
                         A 0 0 * Cprod (fun i : nat => (reduce A 0 0) i i) (S n''))%C).
           { rewrite <- Cprod_extend_l.
             rewrite <- Cprod_extend_r.  
             rewrite <- Cmult_assoc; easy. }
           rewrite H'.
           rewrite <- big_sum_extend_l.
           rewrite <- Cplus_0_r.
           rewrite <- Cplus_assoc.
           apply Cplus_simplify.
           simpl parity. 
           rewrite IHn'; try lca.
           apply up_tri_reduce_0; easy.
           unfold upper_triangular in H.
           rewrite H; try lia. 
           rewrite <- Cplus_0_r.
           apply Cplus_simplify; try lca. 
           apply (@big_sum_0_bounded C C_is_monoid).
           intros. 
           rewrite H; try lia; lca. 
Qed.


(**************************************************)
(** * Defining eignestates to be used in type system *)
(**************************************************)


Definition Eigenpair {n : nat} (U : Square n) (p : Vector n * C) : Prop :=
  U × (fst p) = (snd p) .* (fst p).

Lemma all_v_eigen_I : forall (n : nat) (v : Vector n),
   WF_Matrix v -> Eigenpair (I n) (v, C1).
Proof. intros n v H. unfold Eigenpair. 
       simpl. rewrite Mmult_1_l. lma. 
       easy.
Qed.

Lemma diags_have_basis_eigens : forall (n : nat) (U : Square n) (i : nat),
  (i < n) -> WF_Diagonal U -> Eigenpair U (e_i i, U i i).
Proof. unfold WF_Diagonal, Eigenpair, e_i. intros.
       unfold Mmult, scale.
       prep_matrix_equality.
       eapply big_sum_unique. exists i. 
       destruct H0 as [H0 H1].
       split. apply H.
       split.
       - simpl. bdestruct (x =? i).
         * rewrite H2. bdestruct (i =? i); easy.
         * rewrite H1. lca. lia.  
       - intros. simpl. bdestruct (x' =? i); try lia; lca.
Qed.

Local Close Scope nat_scope.

Lemma eigen_scale : forall {n} (A : Square n) (v : Vector n) (c1 c2 : C),
  Eigenpair A (v, c1) -> Eigenpair (c2 .* A) (v, c1 * c2).
Proof. intros. 
       unfold Eigenpair in *; simpl in *. 
       rewrite Mscale_mult_dist_l.
       rewrite H.
       rewrite Mscale_assoc.
       rewrite Cmult_comm.
       reflexivity.
Qed.


Lemma eigen_scale_div : forall {n} (A : Square n) (v : Vector n) (c1 c2 : C),
  c2 <> C0 -> Eigenpair (c2 .* A) (v, Cmult c2 c1) -> Eigenpair A (v, c1).
Proof. intros. 
       unfold Eigenpair in *; simpl in *. 
       rewrite <- Mscale_assoc in H0.
       rewrite Mscale_mult_dist_l in H0.
       apply Mscale_div in H0;
       assumption.
Qed.



Lemma eig_unit_invertible : forall {n} (v : Vector n) (c : C) (X X' B : Square n),
  WF_Matrix v -> WF_Matrix X -> WF_Matrix X' -> X' × X = I n ->  
  Eigenpair B (X × v, c) -> Eigenpair (X' × B × X) (v, c).  
Proof. intros. 
       unfold Eigenpair in *; simpl in *.
       do 2 (rewrite Mmult_assoc).
       rewrite H3.
       distribute_scale. 
       rewrite <- Mmult_assoc.     
       rewrite H2.
       rewrite Mmult_1_l; easy.
Qed.

Lemma eig_unit_conv : forall {n} (v : Vector n) (c : C) (U B : Square n),
  WF_Matrix v -> WF_Unitary U -> 
  Eigenpair B (U × v, c) -> Eigenpair (U† × B × U) (v, c).  
Proof. intros. 
       destruct H0 as [H0 H2].
       unfold Eigenpair in *; simpl in *.
       do 2 (rewrite Mmult_assoc).
       rewrite H1.
       rewrite Mscale_mult_dist_r.
       rewrite <- Mmult_assoc.     
       rewrite H2.
       rewrite Mmult_1_l; easy.
Qed.

Lemma eig_unit_norm1 : forall {n} (U : Square n) (c : C),
  WF_Unitary U -> (exists v, WF_Matrix v /\ v <> Zero /\ Eigenpair U (v, c)) -> (c * c^* = C1)%C.
Proof. intros. destruct H0 as [v [H0 [H1 H2] ] ].
       unfold Eigenpair in H2; simpl in H2. 
       assert (H3 : (U × v)† = (c .* v)†). rewrite H2; easy.
       rewrite Mmult_adjoint, Mscale_adj in H3.
       assert (H4 : ((v) † × (U) †) × (U × v) = (c ^* .* (v) †) × (c .* v)).
       { rewrite H2, H3; easy. } 
       rewrite Mmult_assoc in H4.
       rewrite <- (Mmult_assoc _ U v) in H4.
       destruct H as [H5 H].       
       rewrite H in H4.
       rewrite Mmult_1_l in H4; auto.
       rewrite Mscale_mult_dist_r in H4.
       rewrite Mscale_mult_dist_l in H4.
       rewrite Mscale_assoc in H4.
       assert (H' : ((v) † × v) O O = (c * c ^* .* ((v) † × v)) O O).
       rewrite <- H4; easy.
       assert (H'' : ((v) † × v) O O = inner_product v v). easy.
       unfold scale in H'.
       rewrite H'' in H'.
       apply (Cmult_simplify (inner_product v v) (c * c ^* * inner_product v v)
                            (/ (inner_product v v)) (/ (inner_product v v))) in H'; try easy.
       rewrite <- Cmult_assoc in H'.
       rewrite Cinv_r in H'.
       
       rewrite H'; lca.
       unfold not; intros; apply H1.
       apply inner_product_zero_iff_zero in H0.
       apply H0; easy.
Qed.


(** Next, we show that unitary matrices are diagonalizable *)

(* our approach is to show that there exists X such that XUX^-1 = pad1 c u where u is one 
   fewer dimension than U. Then, by induction, we can show that U is diagonalizable. The 
   reduction takes three steps, and then we induct to prove the result. *) 

Lemma unit_has_eigen : forall {n} (A : Square (S n)),
  WF_Unitary A -> 
  exists (c : C) (v : Vector (S n)),  Eigenpair A (v, c) /\ v <> Zero /\ WF_Matrix v.
Proof. intros n A [Hwf Hu].
       apply exists_eigenvector in Hwf.
       destruct Hwf as [c [v [H [H0 H1] ] ] ].
       exists c. exists v.
       split. unfold Eigenpair.
       simpl; easy.
       auto.
Qed.

Lemma unitary_reduction_step1 : forall {n} (A : Square (S n)),
  WF_Unitary A ->
  exists X, WF_Unitary X /\
  (exists c : C, get_vec 0 (X†×A×X) = c .* e_i 0).
Proof. intros n A [Hwf Hu].
       apply exists_eigenvector in Hwf.
       destruct Hwf as [c [v [H [H0 H1] ] ] ]. 
       assert (H' := H0).
       apply onb_out_of_v in H0; auto.
       destruct H0 as [T [H2 H3] ].
       exists T. split. 
       apply unit_is_orthonormal; easy.
       exists c.
       rewrite matrix_by_basis; try lia. 
       do 2 rewrite Mmult_assoc. 
       rewrite <- matrix_by_basis, H3; try lia.
       unfold normalize.
       rewrite Mscale_mult_dist_r.
       rewrite H1.
       distribute_scale.
       assert (H'' : forall p1 p2 : C, p1 = p2 -> fst p1 = fst p2).
         intros. rewrite H0; easy.
       assert (H4 : v = (norm v) .* normalize v).
       { unfold normalize; distribute_scale.
         rewrite Cinv_r; try lma. 
         apply norm_zero_iff_zero in H.
         unfold not; intros. 
         apply H'.
         apply H.
         unfold RtoC in H0.
         apply H'' in H0.
         simpl in H0.
         easy. }
       rewrite H4, <- H3.
       apply unit_is_orthonormal in H2.
       destruct H2 as [Hwf HTu].
       rewrite matrix_by_basis; try lia.
       distribute_scale.
       rewrite <- Mmult_assoc, HTu. 
       rewrite <- matrix_by_basis, H3, <- H4; try lia.
       rewrite Cmult_comm, Cmult_assoc, Cinv_r, Mmult_1_l; auto with wf_db.
       lma. unfold not;intros. 
       apply H'.
       apply norm_zero_iff_zero in H.
       unfold RtoC in H0.
       apply H'' in H0; simpl in H0.
       apply H; easy.
Qed.

Local Open Scope nat_scope.
(* this proof is horribly long and I feel like theres probably a better way to show this *)
(* TODO : make this better *) 
Lemma unitary_reduction_step2 : forall {n} (A : Square (S n)),
  WF_Unitary A -> 
  (exists c : C, get_vec 0 A = c .* e_i 0) -> 
  (forall (i j : nat), (i = 0 \/ j = 0) /\ i <> j -> A i j = C0).
Proof. intros n A H [c H0] i j H1.    
       assert (Hc : A 0 0 = c). 
       { replace (A 0 0) with ((get_vec 0 A) 0 0) by easy.
         rewrite H0; lca. }
       assert (H2 : (c * c^*)%C = C1). 
       { apply (eig_unit_norm1 A); try easy.
         exists (e_i 0).
         split.
         apply WF_e_i.
         split. unfold not; intros. 
         apply C1_neq_C0.
         replace C1 with (@e_i (S n) 0 0 0) by easy.
         rewrite H2; easy.
         unfold Eigenpair; simpl. 
         rewrite <- matrix_by_basis; try easy; lia. }
       destruct H1 as [ [H1 | H1] H3].
       - apply transpose_unitary in H.
         apply unit_is_orthonormal in H.
         destruct H as [Hwf [Ho Hn] ].
         assert (H4 : norm (get_vec 0 A†) = 1%R).
         { apply Hn; lia. } 
         unfold norm in H4.
         apply eq_sym in H4.
         apply sqrt_1_unique in H4.
         replace 1%R with (fst C1) in H4 by easy.
         apply (c_proj_eq (((get_vec 0 A†) † × get_vec 0 A†) 0 0) C1) in H4.
         unfold Mmult in H4.
         rewrite <- big_sum_extend_l in H4. 
         assert (H' : ((get_vec 0 (A) †) † 0 0 * get_vec 0 (A) † 0 0)%C = C1).
         { unfold get_vec, adjoint. 
           simpl. rewrite Hc.
           rewrite Cconj_involutive; easy. }
         rewrite H' in H4.
         assert (H'' : forall c : C, (C1 + c = C1 -> -C1 + (C1 + c) = -C1 + C1)%C).
         { intros. rewrite H; easy. }
         apply H'' in H4.
         rewrite Cplus_assoc in H4.
         replace (-C1 + C1)%C with C0 in H4 by lca. 
         rewrite Cplus_0_l in H4.
         rewrite H1 in *.
         destruct j; try lia. 
         assert (H5 := big_sum_squeeze (fun x : nat => ((get_vec 0 (A) †) † 0 (S x) * 
                                                get_vec 0 (A) † (S x) 0)%C) n).
         assert (H5' : forall x : nat,
       x < n ->
       fst ((fun x0 : nat => ((get_vec 0 (A) †) † 0 (S x0) * get_vec 0 (A) † (S x0) 0)%C) x) =
       fst C0).
         { apply H5. intros. 
           unfold adjoint, get_vec, Copp. 
           simpl. 
           rewrite Ropp_involutive.
           unfold Rminus.
           replace (- (snd (A 0%nat (S x)) * - snd (A 0%nat (S x))))%R with 
               ((snd (A 0%nat (S x)))^2)%R by lra. 
           replace (fst (A 0%nat (S x)) * fst (A 0%nat (S x)))%R with 
               ((fst (A 0%nat (S x)))^2)%R by lra. 
           apply Rplus_le_le_0_compat.
           all : try apply pow2_ge_0. 
           rewrite H4; easy. }
         simpl in H5'.
         assert (H6 := (H5' j)).
         bdestruct (j <? n).
         + apply H6 in H.
           rewrite Ropp_involutive in H.
           unfold Rminus in H.
           replace (- (snd (A 0%nat (S j)) * - snd (A 0%nat (S j))))%R with 
               ((snd (A 0%nat (S j)))^2)%R in H by lra. 
           replace (fst (A 0%nat (S j)) * fst (A 0%nat (S j)))%R with 
               ((fst (A 0%nat (S j)))^2)%R in H by lra. 
           assert (H7 : Cmod (A 0 (S j)) = 0%R).
           { unfold Cmod. rewrite H.
             apply sqrt_0. }
           apply Cmod_eq_0 in H7; easy.
         + apply WF_adjoint in Hwf.
           rewrite adjoint_involutive in Hwf.
           rewrite Hwf; try lca; lia.
         + unfold Mmult. 
           apply big_sum_snd_0; intros. 
           unfold get_vec, adjoint. 
           simpl. lra. 
       - rewrite H1. 
         replace (A i 0) with (get_vec 0 A i 0) by easy. 
         rewrite H0.
         destruct i; try lia. 
         lca. 
Qed.


Lemma unitary_reduction_step3 : forall {n} (A : Square (S n)),
  WF_Unitary A -> 
  (forall (i j : nat), (i = 0 \/ j = 0) /\ i <> j -> A i j = C0) ->
  exists (A' : Square n), WF_Unitary A' /\ pad1 A' (A 0 0) = A.
Proof. intros n A [Hwf Hu]. 
       exists (reduce A 0 0).
       assert (H' : WF_Matrix (reduce A 0 0)).
       { apply WF_reduce; try lia; easy. } 
       split. split.        
       apply H'.
       apply mat_equiv_eq; auto with wf_db.
       unfold mat_equiv; intros. 
       assert (H2 : ((A) † × A) (S i) (S j) = (I n) i j).
       { rewrite Hu. 
         unfold I.
         bdestruct_all; try easy. }
       rewrite <- H2.
       unfold Mmult.
       rewrite <- big_sum_extend_l.
       rewrite H, Cmult_0_r, Cplus_0_l.
       apply big_sum_eq_bounded; intros. 
       unfold adjoint. 
       unfold reduce.
       apply Cmult_simplify.
       all : simpl; try easy.
       lia. 
       unfold pad1, reduce, col_wedge, row_wedge, scale, e_i.
       prep_matrix_equality.
       simpl. 
       bdestruct_all; simpl. 
       rewrite H1, H2; lca.
       3 : { destruct x; destruct y; try lia. 
             do 2 rewrite Sn_minus_1; easy. }
       4 : { destruct x; destruct y; try lia. 
             do 2 rewrite Sn_minus_1; easy. }
       all : try rewrite (H x y); try lca; try lia. 
Qed.       

Lemma diagble_pad1 : forall {n} (A : Square n) (c : C),
  WF_Diagonalizable A -> WF_Diagonalizable (pad1 A c).
Proof. intros n A c [H [X [X' [B [ [Hwf Hd] [H1 [H2 [H3 H4] ] ] ] ] ] ] ].
       split. apply WF_pad1; auto.
       exists (pad1 X C1), (pad1 X' C1), (pad1 B c).
       split. split; try (apply WF_pad1; auto).
       - intros.
         destruct i; destruct j; try lia;
           unfold pad1, col_wedge, row_wedge, scale, e_i;
           bdestruct_all; try easy; try lca.
         do 2 rewrite Sn_minus_1.
         apply Hd; lia.
         apply Hd; lia. 
       - split; try (apply WF_pad1; auto).
         split; try (apply WF_pad1; auto).
         split. 
         rewrite <- pad1_mult, H3, Cmult_1_r, pad1_I.
         easy.
         do 2 rewrite <- pad1_mult.
         rewrite <- H4, Cmult_1_r, Cmult_1_l.
         easy.
Qed.         

         
(* Now, we can induct and prove the theorem *)
Theorem unit_implies_diagble : forall {n} (A : Square n),
  WF_Unitary A -> WF_Diagonalizable A.
Proof. induction n as [| n']. 
       - intros A [H H0]. 
         apply WF0_Zero_l in H. 
         rewrite H. 
         apply diagble_Zero.
       - intros A H. 
         assert (H0 := H).
         apply unitary_reduction_step1 in H.
         destruct H as [X [H1 [c H2] ] ].
         assert (H3 : WF_Unitary ((X) † × A × X)).
         { do 2 try apply Mmult_unitary.
           apply transpose_unitary.
           all : easy. }
         assert (H4 : (forall (i j : nat), (i = 0 \/ j = 0) /\ i <> j ->
                                           ((X) † × A × X) i j = C0)).
         { apply unitary_reduction_step2; try easy. 
           exists c. easy. }
         apply unitary_reduction_step3 in H3; try easy.
         destruct H3 as [A' [H5 H6] ].
         assert (H7 : WF_Diagonalizable ((X) † × A × X)).
         apply IHn' in H5.
         { rewrite <- H6. 
           apply diagble_pad1.
           easy. }
         destruct H7 as [Hwf Hd].
         split. 
         destruct H0; easy.
         destruct Hd as [X0 [X0' [B [H7 [H8 [H9 [H10 H11] ] ] ] ] ] ].
         exists (X0 × (X) †).
         exists (X × X0').
         exists B.
         destruct H1 as [H1wf H1u].
         split; try easy.
         split; auto with wf_db.
         split; auto with wf_db.
         rewrite Mmult_assoc.
         rewrite <- (Mmult_assoc X †).
         rewrite H1u.
         rewrite Mmult_1_l; try easy.
         split; try easy.
         rewrite H11.
         repeat rewrite Mmult_assoc.
         easy.
Qed.


(************************************************************************************)
(** * Showing that certain types of matrices are equal when their eigenpairs are equal *)
(************************************************************************************)


Definition eq_eigs {n : nat} (U1 U2 : Square n) : Prop := 
  forall p, WF_Matrix (fst p) -> (Eigenpair U1 p -> Eigenpair U2 p). 


Lemma eq_eigs_implies_eq_diag : forall {n} (D1 D2 : Square n),
  WF_Diagonal D1 -> WF_Diagonal D2 -> eq_eigs D1 D2 -> D1 = D2.
Proof. intros n D1 D2 [H1wf H1d] [H2wf H2d] H. 
       assert (H2 : forall x, x < n -> D1 x x = D2 x x).
       { intros.
         assert (H1 := H0).
         apply (diags_have_basis_eigens n D1 x) in H1.
         apply H in H1.
         unfold Eigenpair in H1; simpl in H1.
         assert (H' : (D1 x x .* @e_i n x) x 0 = D1 x x).
         { unfold scale, e_i.
           bdestruct_all; lca. }
         rewrite <- H', <- H1. 
         unfold Mmult. 
         apply (big_sum_unique (D2 x x)). 
         exists x. split; try easy.
         split. unfold e_i. 
         bdestruct_all; lca.
         intros. 
         unfold e_i; bdestruct_all; lca.
         simpl. auto with wf_db.
         split; auto. }
       apply mat_equiv_eq; auto.
       unfold mat_equiv; intros. 
       bdestruct (i =? j).
       - rewrite H3, H2; try lia; easy. 
       - rewrite H1d, H2d; try lia; easy.
Qed.
         

Lemma diagble_eigenpairs_transfer : forall {n} (A B X X' : Square n),
  WF_Matrix A -> WF_Diagonal B -> WF_Matrix X -> WF_Matrix X' ->
  A = X' × B × X -> X × X' = I n ->
  (forall x, x < n -> Eigenpair A (X' × (e_i x), B x x)).
Proof. intros. 
       destruct H0 as [Hwf Hu].
       unfold Eigenpair; simpl.
       rewrite <- Mmult_assoc. 
       rewrite H3.
       do 2 rewrite Mmult_assoc. 
       rewrite <- (Mmult_assoc X), H4, Mmult_1_l; auto with wf_db.
       assert (H' := (diags_have_basis_eigens n B)).
       apply H' in H5. 
       unfold Eigenpair in H5; simpl in H5. 
       rewrite Mmult_assoc, H5. 
       distribute_scale; easy.
       split; auto.
Qed.   

Lemma eq_eigs_implies_eq_diagble : forall {n} (D1 D2 : Square n),
  WF_Diagonalizable D1 -> WF_Diagonalizable D2 -> eq_eigs D1 D2 -> D1 = D2.
Proof. intros n D1 D2 [H1wf H1d] [H2wf H2d] H. 
       destruct H1d as [X1 [X1' [B1 [ [Hb1wf Hb1u] [H12 [H13 [H14 H15] ] ] ] ] ] ].
       destruct H2d as [X2 [X2' [B2 [ [Hb2wf Hb2u] [H22 [H23 [H24 H25] ] ] ] ] ] ].
       apply diagble_switch in H15; apply diagble_switch in H25; auto.
       assert (H0 : D1 × X1' = X1' × B1).
       { rewrite H15.
         repeat rewrite Mmult_assoc.
         rewrite H14, Mmult_1_r; auto. }
       assert (H1 : D2 × X2' = X2' × B2).
       { rewrite H25.
         repeat rewrite Mmult_assoc.
         rewrite H24, Mmult_1_r; auto. }
       assert (H2 : forall i, i < n -> Eigenpair D1 (X1' × (e_i i), B1 i i)).
       { apply (diagble_eigenpairs_transfer D1 B1 X1 X1'); auto. 
         split; auto. }
       assert (H3 : forall i, i < n -> Eigenpair D2 (X1' × (e_i i), B1 i i)).
       { intros. apply H. simpl. 
         auto with wf_db. apply H2; easy. }
       assert (H4 : forall i, i < n -> Eigenpair (X1 × D1 × X1') (e_i i, B1 i i)).
       { intros. apply eig_unit_invertible; auto with wf_db. }
       assert (H5 : forall i, i < n -> Eigenpair (X1 × D2 × X1') (e_i i, B1 i i)).
       { intros. apply eig_unit_invertible; auto with wf_db. }
       assert (H6 : forall i, i < n -> (X1 × D1 × X1' × e_i i = X1 × D2 × X1' × e_i i)).
       { intros. 
         unfold Eigenpair in *; simpl in *.
         rewrite H4, H5; easy. }
       assert (H7 : X1 × D1 × X1' = X1 × D2 × X1').
       { apply det_by_get_vec.
         intros. 
         bdestruct (i <? n).
         - rewrite matrix_by_basis.
           rewrite matrix_by_basis. 
           apply H6. 
           all : easy. 
         - assert (H' : forall (A : Square n) (i : nat), i >= n -> WF_Matrix A -> 
                                                  get_vec i A = @Zero n 1).  
           { intros. 
             unfold get_vec. 
             prep_matrix_equality. 
             bdestruct_all; try easy.
             rewrite H9; try lia; easy. }
           rewrite H'; auto with wf_db.
           rewrite H'; auto with wf_db. }
       assert (H8 : X1' × (X1 × D1 × X1') × X1= X1' × (X1 × D2 × X1') × X1).
       { rewrite H7; easy. }
       repeat rewrite Mmult_assoc in H8.
       apply Minv_flip in H14; auto. 
       rewrite H14 in H8.
       do 2 rewrite Mmult_1_r in H8; auto. 
       do 2 rewrite <- Mmult_assoc in H8.
       rewrite H14 in H8.
       do 2 rewrite Mmult_1_l in H8; auto. 
Qed.

Lemma eq_eigs_implies_eq_unit : forall {n} (U1 U2 : Square n),
  WF_Unitary U1 -> WF_Unitary U2 -> eq_eigs U1 U2 -> U1 = U2.
Proof. intros. 
       apply unit_implies_diagble in H.
       apply unit_implies_diagble in H0.
       apply eq_eigs_implies_eq_diagble; auto. 
Qed.

Theorem eigs_eq_gate : forall {n} (U1 U2 : Square n),
  WF_Unitary U1 -> WF_Unitary U2 -> (U1 = U2 <-> eq_eigs U1 U2).
Proof. intros. split.
       - intros H'; rewrite H'; easy.
       - apply eq_eigs_implies_eq_unit.
         apply H. apply H0.
Qed.

Local Close Scope nat_scope.

(*******************************)
(** * Some actual examples/lemmas *)
(*******************************)


Lemma EigenXp : Eigenpair σx (∣+⟩, C1).
Proof. unfold Eigenpair. solve_matrix. Qed.

Lemma EigenXm : Eigenpair σx (∣-⟩, -C1).
Proof. unfold Eigenpair. solve_matrix. Qed.

Lemma EigenYp : Eigenpair σy (∣R⟩, C1).
Proof. unfold Eigenpair. solve_matrix. Qed.

Lemma EigenYm : Eigenpair σy (∣L⟩, -C1).
Proof. unfold Eigenpair. solve_matrix. Qed.

Lemma EigenZp : Eigenpair σz (∣0⟩, C1).
Proof. unfold Eigenpair. solve_matrix. Qed.

Lemma EigenZm : Eigenpair σz (∣1⟩, -C1).
Proof. unfold Eigenpair. solve_matrix. Qed.

Lemma EigenXXB : Eigenpair (σx ⊗ σx) (∣Φ+⟩, C1).
Proof. unfold Eigenpair. lma'. Qed.

#[export] Hint Resolve EigenXp EigenXm EigenYp EigenYm EigenZp EigenZm EigenXXB all_v_eigen_I : eig_db.
