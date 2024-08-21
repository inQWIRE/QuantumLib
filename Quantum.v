
(** In this file, we define specific objects/concepts specific to quantum computing and we prove lemmas about thems. *)

Require Import Psatz.
Require Import Reals.
Require Export VecSet.
Require Export CauchySchwarz.
Require Import Kronecker.

(* Using our (complex, unbounded) matrices, their complex numbers *)

(*******************************************)
(** * Quantum basis states *)
(*******************************************)

(* Maybe change to IF statements? *)
Definition qubit0 : Vector 2 := 
  fun x y => match x, y with 
          | 0, 0 => C1
          | 1, 0 => C0
          | _, _ => C0
          end.
Definition qubit1 : Vector 2 := 
  fun x y => match x, y with 
          | 0, 0 => C0
          | 1, 0 => C1
          | _, _ => C0
          end.

(* Ket notation: \mid 0 \rangle *)
Notation "∣0⟩" := qubit0.
Notation "∣1⟩" := qubit1.
Notation "⟨0∣" := qubit0†.
Notation "⟨1∣" := qubit1†.
Notation "∣0⟩⟨0∣" := (∣0⟩×⟨0∣).
Notation "∣1⟩⟨1∣" := (∣1⟩×⟨1∣).
Notation "∣1⟩⟨0∣" := (∣1⟩×⟨0∣).
Notation "∣0⟩⟨1∣" := (∣0⟩×⟨1∣).

Definition bra (x : nat) : Matrix 1 2 := if x =? 0 then ⟨0∣ else ⟨1∣.
Definition ket (x : nat) : Matrix 2 1 := if x =? 0 then ∣0⟩ else ∣1⟩.

(* Note the 'mid' symbol for these *)
Notation "'∣' x '⟩'" := (ket x).
Notation "'⟨' x '∣'" := (bra x). (* This gives the Coq parser headaches *)

Notation "∣ x , y , .. , z ⟩" := (kron .. (kron ∣x⟩ ∣y⟩) .. ∣z⟩) (at level 0).
(* Alternative: |0⟩|1⟩. *)
                                                                       
Transparent bra.
Transparent ket.
Transparent qubit0.
Transparent qubit1.

Definition bool_to_ket (b : bool) : Matrix 2 1 := if b then ∣1⟩ else ∣0⟩.
                                                                     
Definition bool_to_matrix (b : bool) : Matrix 2 2 := if b then ∣1⟩⟨1∣ else ∣0⟩⟨0∣.

Definition bool_to_matrix' (b : bool) : Matrix 2 2 := fun x y =>
  match x, y with
  | 0, 0 => if b then 0 else 1
  | 1, 1 => if b then 1 else 0
  | _, _ => 0
  end.  
  
Lemma bool_to_matrix_eq : forall b, bool_to_matrix b = bool_to_matrix' b.
Proof. intros. destruct b; simpl; solve_matrix. Qed.

Lemma bool_to_ket_matrix_eq : forall b,
    outer_product (bool_to_ket b) (bool_to_ket b) = bool_to_matrix b.
Proof. unfold outer_product. destruct b; simpl; reflexivity. Qed.

Definition bools_to_matrix (l : list bool) : Square (2^(length l)) := 
  big_kron (map bool_to_matrix l).

Lemma ket_decomposition : forall (ψ : Vector 2), 
  WF_Matrix ψ ->
  ψ = (ψ 0%nat 0%nat) .* ∣ 0 ⟩ .+ (ψ 1%nat 0%nat) .* ∣ 1 ⟩.
Proof.
  intros.
  prep_matrix_equality.
  unfold scale, Mplus.
  destruct y as [|y']. 
  2:{ rewrite H; try lia. 
      unfold ket, qubit0, qubit1. simpl. 
      repeat (destruct x; try lca). }
  destruct x as [| [| n]]; unfold ket, qubit0, qubit1; simpl; try lca.  
  rewrite H; try lia.
  lca.
Qed. 


                                                          
(* Defining other basis states *)
                                                          
Definition xbasis_plus : Vector 2 := / (√ 2) .* (∣0⟩ .+ ∣1⟩).
Definition xbasis_minus : Vector 2 := / (√ 2) .* (∣0⟩ .+ ((-1) .* ∣1⟩)).
Definition ybasis_plus : Vector 2 := / (√ 2) .* (∣0⟩ .+ Ci .* ∣1⟩).
Definition ybasis_minus : Vector 2 := / (√ 2) .* (∣0⟩ .+ ((-Ci) .* ∣1⟩)).
Definition braminus :=  / √ 2 .* (⟨0∣ .+ (-1 .* ⟨1∣)).
Definition braplus  :=  / √ 2 .* (⟨0∣ .+ ⟨1∣).

Notation "∣+⟩" := xbasis_plus.
Notation "∣-⟩" := xbasis_minus.
Notation "⟨+∣" := braplus.
Notation "⟨-∣" := braminus.
Notation "∣R⟩" := ybasis_plus.
Notation "∣L⟩" := ybasis_minus.

Lemma xbasis_plus_spec : ∣+⟩ = / √ 2 .* (∣0⟩ .+ ∣1⟩).
Proof. reflexivity. Qed.
Lemma xbasis_minus_spec : ∣-⟩ = / √ 2 .* (∣0⟩ .+  (- 1) .* (∣1⟩)).
Proof. reflexivity. Qed.

(* defining the EPR pair *)
Definition EPRpair : Vector 4 := / (√ 2) .* (∣0,0⟩ .+ ∣1,1⟩).

Notation "∣Φ+⟩" := EPRpair.
                                                         
                                                          
(****************)
(** * Unitaries *)
(****************)

Definition hadamard : Matrix 2 2 := 
  (fun x y => match x, y with
          | 0, 0 => (1 / √2)
          | 0, 1 => (1 / √2)
          | 1, 0 => (1 / √2)
          | 1, 1 => -(1 / √2)
          | _, _ => 0
          end).

Fixpoint hadamard_k (k : nat) : Matrix (2^k) (2^k):= 
  match k with
  | 0 => I 1
  | S k' => hadamard ⊗ hadamard_k k'
  end. 

Lemma hadamard_1 : hadamard_k 1 = hadamard.
Proof. apply kron_1_r. Qed.

Definition σx : Matrix 2 2 := 
  fun x y => match x, y with
          | 0, 1 => C1
          | 1, 0 => C1
          | _, _ => C0
          end.

Definition σy : Matrix 2 2 := 
  fun x y => match x, y with
          | 0, 1 => -Ci
          | 1, 0 => Ci
          | _, _ => C0
          end.

Definition σz : Matrix 2 2 := 
  fun x y => match x, y with
          | 0, 0 => C1
          | 1, 1 => -C1
          | _, _ => C0
          end.

Definition sqrtx : Matrix 2 2 :=
  fun x y => match x, y with
          | 0, 0 => (1 + Ci)/2
          | 0, 1 => (1 - Ci)/2
          | 1, 0 => (1 - Ci)/2
          | 1, 1 => (1 + Ci)/2
          | _, _ => C0
          end.

Definition control {n : nat} (A : Matrix n n) : Matrix (2*n) (2*n) :=
  fun x y => if (x <? n) && (y =? x) then 1 else 
          if (n <=? x) && (n <=? y) then A (x-n)%nat (y-n)%nat else 0.

(* Definition cnot := control pauli_x. *)
(* Direct definition makes our lives easier *)
(* Dimensions are given their current form for convenient
   kron_mixed_product applications *)
Definition cnot : Matrix (2*2) (2*2) :=
  fun x y => match x, y with 
          | 0, 0 => C1
          | 1, 1 => C1
          | 2, 3 => C1
          | 3, 2 => C1
          | _, _ => C0
          end.          

Definition notc : Matrix (2*2) (2*2) :=
  fun x y => match x, y with 
          | 1, 3 => 1%C
          | 3, 1 => 1%C
          | 0, 0 => 1%C
          | 2, 2 => 1%C
          | _, _ => 0%C
          end.          

(* Swap Matrices *)

Definition swap : Matrix (2*2) (2*2) :=
  fun x y => match x, y with
          | 0, 0 => C1
          | 1, 2 => C1
          | 2, 1 => C1
          | 3, 3 => C1
          | _, _ => C0
          end.

#[export] Hint Unfold qubit0 qubit1 hadamard σx σy σz control cnot swap bra ket : U_db.

(** ** Rotation Matrices *)
                              
(* The definition given below is different from the standard definition (shown in the comments), 
   but equivalent up to a global phase.

Definition rotation (θ ϕ λ : R) : Matrix 2 2 :=
  fun x y => match x, y with
             | 0, 0 => (Cexp (-(ϕ + λ)/2)) * (cos (θ/2))
             | 0, 1 => - (Cexp (-(ϕ - λ)/2)) * (sin (θ/2))
             | 1, 0 => (Cexp ((ϕ - λ)/2)) * (sin (θ/2))
             | 1, 1 => (Cexp ((ϕ + λ)/2)) * (cos (θ/2))
             | _, _ => C0
             end.
*)
Definition rotation (θ ϕ λ : R) : Matrix 2 2 :=
  fun x y => match x, y with
             | 0, 0 => (cos (θ/2))
             | 0, 1 => - (Cexp λ) * (sin (θ/2))
             | 1, 0 => (Cexp ϕ) * (sin (θ/2))
             | 1, 1 => (Cexp (ϕ + λ)) * (cos (θ/2))
             | _, _ => C0
             end.

Definition phase_shift (ϕ : R) : Matrix 2 2 :=
  fun x y => match x, y with
          | 0, 0 => C1
          | 1, 1 => Cexp ϕ
          | _, _ => C0
          end.

Definition x_rotation  (θ : R) : Matrix 2 2 :=
  fun x y => match x, y with
          | 0, 0 => cos (θ / 2)
          | 0, 1 => -Ci * sin (θ / 2)
          | 1, 0 => -Ci * sin (θ / 2)
          | 1, 1 => cos (θ / 2)
          | _, _ => 0
          end.

Definition y_rotation  (θ : R) : Matrix 2 2 :=
  fun x y => match x, y with
          | 0, 0 => cos (θ / 2)
          | 0, 1 => - sin (θ / 2)
          | 1, 0 => sin (θ / 2)
          | 1, 1 => cos (θ / 2)
          | _, _ => 0
          end.

(* Shifted by i so x/y_rotation PI = σx/y :
Definition x_rotation  (θ : R) : Matrix 2 2 :=
  fun x y => match x, y with
          | 0, 0 => Ci * cos (θ / 2)
          | 0, 1 => sin (θ / 2)
          | 1, 0 => sin (θ / 2)
          | 1, 1 => Ci * cos (θ / 2)
          | _, _ => 0
          end.

Definition y_rotation  (θ : R) : Matrix 2 2 :=
  fun x y => match x, y with
          | 0, 0 => Ci * cos (θ / 2)
          | 0, 1 => -Ci * sin (θ / 2)
          | 1, 0 => Ci * sin (θ / 2)
          | 1, 1 => Ci * cos (θ / 2)
          | _, _ => 0
          end.
 *)

Definition Sgate : Matrix 2 2 := phase_shift (PI / 2).

Definition Tgate :=  phase_shift (PI / 4).

(** Well Formedness of Quantum States and Unitaries **)

Lemma WF_bra0 : WF_Matrix ⟨0∣. Proof. show_wf. Qed. 
Lemma WF_bra1 : WF_Matrix ⟨1∣. Proof. show_wf. Qed.
Lemma WF_qubit0 : WF_Matrix ∣0⟩. Proof. show_wf. Qed.
Lemma WF_qubit1 : WF_Matrix ∣1⟩. Proof. show_wf. Qed.
Lemma WF_braket0 : WF_Matrix ∣0⟩⟨0∣. Proof. show_wf. Qed.
Lemma WF_braket1 : WF_Matrix ∣1⟩⟨1∣. Proof. show_wf. Qed.

#[deprecated(note="Use WF_braket0 instead")]
Notation WF_braqubit0 := WF_braket0 (only parsing).
#[deprecated(note="Use WF_braket1 instead")]
Notation WF_braqubit1 := WF_braket1 (only parsing).

Lemma WF_bool_to_ket : forall b, WF_Matrix (bool_to_ket b). 
Proof. destruct b; show_wf. Qed.
Lemma WF_bool_to_matrix : forall b, WF_Matrix (bool_to_matrix b).
Proof. destruct b; show_wf. Qed.
Lemma WF_bool_to_matrix' : forall b, WF_Matrix (bool_to_matrix' b).
Proof. destruct b; show_wf. Qed.

Lemma WF_ket : forall n, WF_Matrix (ket n).
Proof. destruct n; simpl; show_wf. Qed.
Lemma WF_bra : forall n, WF_Matrix (bra n).
Proof. destruct n; simpl; show_wf. Qed.

Lemma WF_bools_to_matrix : forall l, 
  @WF_Matrix (2^(length l)) (2^(length l))  (bools_to_matrix l).
Proof. 
  induction l; auto with wf_db.
  unfold bools_to_matrix in *; simpl.
  apply WF_kron; try rewrite map_length; try lia.
  apply WF_bool_to_matrix.
  apply IHl.
Qed.


Lemma WF_xbasis_plus : WF_Matrix ∣+⟩. Proof. show_wf. Qed.
Lemma WF_xbasis_minus : WF_Matrix ∣-⟩. Proof. show_wf. Qed.
Lemma WF_braplus : WF_Matrix (⟨+∣). Proof. show_wf. Qed.
Lemma WF_braminus : WF_Matrix (⟨-∣). Proof. show_wf. Qed.
Lemma WF_ybasis_plus : WF_Matrix ∣R⟩. Proof. show_wf. Qed.
Lemma WF_ybasis_minus : WF_Matrix ∣L⟩. Proof. show_wf. Qed.


#[export] Hint Resolve WF_bra0 WF_bra1 WF_qubit0 WF_qubit1 WF_braket0 WF_braket1 : wf_db.
#[export] Hint Resolve WF_bool_to_ket WF_bool_to_matrix WF_bool_to_matrix' : wf_db.
#[export] Hint Resolve WF_ket WF_bra WF_bools_to_matrix : wf_db.
#[export] Hint Resolve WF_xbasis_plus WF_xbasis_minus WF_braplus WF_braminus
  WF_ybasis_plus WF_ybasis_minus : wf_db. 

Lemma WF_EPRpair : WF_Matrix ∣Φ+⟩. Proof. unfold EPRpair. auto with wf_db. Qed.

#[export] Hint Resolve WF_EPRpair : wf_db. 


Lemma WF_hadamard : WF_Matrix hadamard. Proof. show_wf. Qed.
Lemma WF_σx : WF_Matrix σx. Proof. show_wf. Qed.
Lemma WF_σy : WF_Matrix σy. Proof. show_wf. Qed.
Lemma WF_σz : WF_Matrix σz. Proof. show_wf. Qed.
Lemma WF_sqrtx : WF_Matrix sqrtx. Proof. show_wf. Qed.
Lemma WF_cnot : WF_Matrix cnot. Proof. show_wf. Qed.
Lemma WF_notc : WF_Matrix notc. Proof. show_wf. Qed.
Lemma WF_swap : WF_Matrix swap. Proof. show_wf. Qed.

Lemma WF_rotation : forall θ ϕ λ, WF_Matrix (rotation θ ϕ λ). Proof. intros. show_wf. Qed.
Lemma WF_x_rotation : forall θ, WF_Matrix (x_rotation θ). Proof. intros. show_wf. Qed.
Lemma WF_y_rotation : forall θ, WF_Matrix (y_rotation θ). Proof. intros. show_wf. Qed.
Lemma WF_phase : forall ϕ, WF_Matrix (phase_shift ϕ). Proof. intros. show_wf. Qed.

Lemma WF_Sgate : WF_Matrix Sgate. Proof. show_wf. Qed.
Lemma WF_Tgate: WF_Matrix Tgate. Proof. show_wf. Qed.

Lemma WF_control : forall (n : nat) (U : Matrix n n), 
      WF_Matrix U -> WF_Matrix (control U).
Proof.
  intros n U WFU.
  unfold control, WF_Matrix in *.
  intros x y [Hx | Hy];
  bdestruct (x <? n); bdestruct (y =? x); bdestruct (n <=? x); bdestruct (n <=? y);
    simpl; try reflexivity; try lia. 
  all: rewrite WFU; [reflexivity|lia].
Qed.

#[export] Hint Resolve WF_hadamard WF_σx WF_σy WF_σz WF_sqrtx WF_cnot WF_notc WF_swap : wf_db.
#[export] Hint Resolve WF_phase WF_Sgate WF_Tgate WF_rotation WF_x_rotation WF_y_rotation : wf_db.

#[export] Hint Extern 2 (WF_Matrix (phase_shift _)) => apply WF_phase : wf_db.
#[export] Hint Extern 2 (WF_Matrix (control _)) => apply WF_control : wf_db.

Lemma sqrtx_sqrtx : sqrtx × sqrtx = σx.
Proof.
  prep_matrix_equivalence.
  by_cell; lca.
Qed.

Lemma cnot_eq : cnot = control σx.
Proof.
  prep_matrix_equivalence.
  now by_cell.
Qed.

Lemma x_rotation_pi : x_rotation PI = -Ci .* σx.
Proof.
  prep_matrix_equivalence.
  unfold x_rotation.
  autorewrite with trig_db.
  by_cell; lca.
Qed.

Lemma y_rotation_pi : y_rotation PI = -Ci .* σy.
Proof.
  prep_matrix_equivalence.
  unfold y_rotation.
  autorewrite with trig_db.
  by_cell; lca.
Qed.

Lemma hadamard_rotation : rotation (PI/2) 0 PI = hadamard.
Proof.
  prep_matrix_equivalence.
  unfold rotation, hadamard.
  replace (PI / 2 / 2)%R with (PI / 4)%R by lra.
  autorewrite with trig_db.
  (* autorewrite with R_db. *)
  rewrite Rplus_0_l, Cexp_PI, Cexp_0, Cmult_1_l.
  rewrite <- RtoC_opp, <- !RtoC_mult, <- RtoC_div.
  by_cell; lca.
Qed.

Lemma pauli_x_rotation : rotation PI 0 PI = σx.
Proof.
  unfold σx, rotation. 
  prep_matrix_equality.
  destruct_m_eq; try reflexivity;
  unfold Cexp; apply injective_projections; simpl;
  autorewrite with trig_db;
  lra.
Qed.

Lemma pauli_y_rotation : rotation PI (PI/2) (PI/2) = σy.
Proof. 
  unfold σy, rotation. 
  prep_matrix_equality.
  destruct_m_eq; try reflexivity;
  unfold Cexp; apply injective_projections; simpl;
  autorewrite with trig_db;
  lra.
Qed.

Lemma pauli_z_rotation : rotation 0 0 PI = σz.
Proof. 
  unfold σz, rotation. 
  prep_matrix_equality.
  destruct_m_eq; try reflexivity;
  unfold Cexp; apply injective_projections; simpl;
  autorewrite with R_db;
  autorewrite with trig_db;
  lra.
Qed.

Lemma Rx_rotation : forall θ, rotation θ (3*PI/2) (PI/2) = x_rotation θ.
Proof.
  intros.
  unfold rotation, x_rotation. 
  prep_matrix_equality.
  destruct_m_eq;
  autorewrite with C_db Cexp_db; reflexivity.
Qed.

Lemma Ry_rotation : forall θ, rotation θ 0 0 = y_rotation θ.
Proof. 
  intros.
  unfold rotation, y_rotation. 
  prep_matrix_equality.
  destruct_m_eq;
  autorewrite with C_db Cexp_db; try reflexivity.
Qed.

Lemma phase_shift_rotation : forall θ, rotation 0 0 θ = phase_shift θ.
Proof. 
  intros.
  unfold phase_shift, rotation. 
  prep_matrix_equality.
  destruct_m_eq; try reflexivity;
  unfold Cexp; apply injective_projections; simpl;
  autorewrite with R_db;
  autorewrite with trig_db;
  lra.
Qed.

Lemma I_rotation : rotation 0 0 0 = I 2.
Proof.
  prep_matrix_equivalence.
  unfold rotation.
  rewrite Rdiv_0_l, Rplus_0_l, Cexp_0.
  autorewrite with trig_db.
  by_cell; lca.
Qed.


(* Lemmas *)

Lemma sqrtx_decompose: sqrtx = hadamard × phase_shift (PI/2) × hadamard.
Proof.
  prep_matrix_equivalence.
  unfold phase_shift, hadamard, Cdiv.
  Csimpl.
  rewrite Cexp_PI2.
  do 2 reduce_matrices.
  group_radicals.
  by_cell; lca.
Qed.

(* Additional tactics for ∣0⟩, ∣1⟩, cnot and σx. *)

Lemma Mmult00 : ⟨0∣ × ∣0⟩ = I 1. Proof. solve_matrix_fast. Qed.
Lemma Mmult01 : ⟨0∣ × ∣1⟩ = Zero. Proof. solve_matrix_fast. Qed.
Lemma Mmult10 : ⟨1∣ × ∣0⟩ = Zero. Proof. solve_matrix_fast. Qed.
Lemma Mmult11 : ⟨1∣ × ∣1⟩ = I 1. Proof. solve_matrix_fast. Qed.

Lemma MmultX1 : σx × ∣1⟩ = ∣0⟩. Proof. solve_matrix_fast. Qed.
Lemma Mmult1X : ⟨1∣ × σx = ⟨0∣. Proof. solve_matrix_fast. Qed.
Lemma MmultX0 : σx × ∣0⟩ = ∣1⟩. Proof. solve_matrix_fast. Qed.
Lemma Mmult0X : ⟨0∣ × σx = ⟨1∣. Proof. solve_matrix_fast. Qed.

Lemma MmultXX : σx × σx = I 2. Proof. solve_matrix_fast. Qed.
Lemma MmultYY : σy × σy = I 2. Proof. solve_matrix_fast. Qed.
Lemma MmultZZ : σz × σz = I 2. Proof. solve_matrix_fast. Qed.
Lemma MmultHH : hadamard × hadamard = I 2. Proof. 
  solve_matrix_fast_with idtac (cbn; C_field; lca).
Qed.

Lemma MmultZH : σz × hadamard = hadamard × σx. Proof. lma'. Qed.
Lemma MmultXH : σx × hadamard = hadamard × σz. Proof. lma'. Qed.
Lemma MmultHZ : hadamard × σz = σx × hadamard. Proof. now rewrite MmultXH. Qed.
Lemma MmultHX : hadamard × σx = σz × hadamard. Proof. now rewrite MmultZH. Qed.
Lemma MmultHY : hadamard × σy = (- C1) .* (σy × hadamard). Proof. lma'. Qed.
Lemma MmultYH : σy × hadamard = (- C1) .* (hadamard × σy).
Proof. 
  rewrite MmultHY, Mscale_assoc.
  replace (- C1 * - C1)%C with (C1) by lca.
  now rewrite Mscale_1_l.
Qed.

Lemma Mmult_phase_11 a : ∣1⟩⟨1∣ × phase_shift a = phase_shift a × ∣1⟩⟨1∣.
Proof. lma'. Qed.

Lemma Mmult_phase_00 a : ∣0⟩⟨0∣ × phase_shift a = phase_shift a × ∣0⟩⟨0∣.
Proof. lma'. Qed.

Lemma Mmult_phase_X_phase_X a a' : 
  σx × phase_shift a × σx × phase_shift a' = 
  phase_shift a' × σx × phase_shift a × σx.
Proof. lma'. Qed.

Lemma Mplus01 : ∣0⟩⟨0∣ .+ ∣1⟩⟨1∣ = I 2. Proof. solve_matrix_fast. Qed.
Lemma Mplus10 : ∣1⟩⟨1∣ .+ ∣0⟩⟨0∣ = I 2. Proof. solve_matrix_fast. Qed.

Lemma EPRpair_creation : cnot × (hadamard ⊗ I 2) × ∣0,0⟩ = EPRpair.
Proof. solve_matrix_fast_with (rewrite kron_I_r) lca. Qed.
                            
Lemma σx_on_right0 : forall (q : Vector 2), (q × ⟨0∣) × σx = q × ⟨1∣.
Proof. intros. rewrite Mmult_assoc, Mmult0X. reflexivity. Qed.

Lemma σx_on_right1 : forall (q : Vector 2), (q × ⟨1∣) × σx = q × ⟨0∣.
Proof. intros. rewrite Mmult_assoc, Mmult1X. reflexivity. Qed.

Lemma σx_on_left0 : forall (q : Matrix 1 2), σx × (∣0⟩ × q) = ∣1⟩ × q.
Proof. intros. rewrite <- Mmult_assoc, MmultX0. reflexivity. Qed.

Lemma σx_on_left1 : forall (q : Matrix 1 2), σx × (∣1⟩ × q) = ∣0⟩ × q.
Proof. intros. rewrite <- Mmult_assoc, MmultX1. reflexivity. Qed.

Lemma cancel00 : forall (q1 : Matrix 2 1) (q2 : Matrix 1 2), 
  WF_Matrix q2 ->
  (q1 × ⟨0∣) × (∣0⟩ × q2) = q1 × q2.
Proof. 
  intros. 
  rewrite Mmult_assoc. 
  rewrite <- (Mmult_assoc ⟨0∣).
  rewrite Mmult00.             
  Msimpl; reflexivity.
Qed.

Lemma cancel01 : forall (q1 : Matrix 2 1) (q2 : Matrix 1 2), 
  (q1 × ⟨0∣) × (∣1⟩ × q2) = Zero.
Proof. 
  intros. 
  rewrite Mmult_assoc. 
  rewrite <- (Mmult_assoc ⟨0∣).
  rewrite Mmult01.             
  Msimpl_light; reflexivity.
Qed.

Lemma cancel10 : forall (q1 : Matrix 2 1) (q2 : Matrix 1 2), 
  (q1 × ⟨1∣) × (∣0⟩ × q2) = Zero.
Proof. 
  intros. 
  rewrite Mmult_assoc. 
  rewrite <- (Mmult_assoc ⟨1∣).
  rewrite Mmult10.             
  Msimpl_light; reflexivity.
Qed.

Lemma cancel11 : forall (q1 : Matrix 2 1) (q2 : Matrix 1 2), 
  WF_Matrix q2 ->
  (q1 × ⟨1∣) × (∣1⟩ × q2) = q1 × q2.
Proof. 
  intros. 
  rewrite Mmult_assoc. 
  rewrite <- (Mmult_assoc ⟨1∣).
  rewrite Mmult11.             
  Msimpl; reflexivity.
Qed.

#[global] Hint Rewrite Mmult00 Mmult01 Mmult10 Mmult11 Mmult0X MmultX0 Mmult1X MmultX1 : Q_db.
#[global] Hint Rewrite MmultXX MmultYY MmultZZ MmultHH Mplus01 Mplus10 EPRpair_creation : Q_db.
#[global] Hint Rewrite σx_on_right0 σx_on_right1 σx_on_left0 σx_on_left1 : Q_db.
#[global] Hint Rewrite cancel00 cancel01 cancel10 cancel11 using (auto with wf_db) : Q_db.


(* TODO: move these swap lemmas to Permutation.v? *)

(* The input k is really k+1, to appease to Coq termination gods *)
(* NOTE: Check that the offsets are right *)
(* Requires: i + 1 < n *)
Fixpoint swap_to_0_aux (n i : nat) {struct i} : Matrix (2^n) (2^n) := 
  match i with
  | O => swap ⊗ I (2^(n-2))
  | S i' =>  (I (2^i) ⊗ swap ⊗ I (2^(n-i-2))) × (* swap i-1 with i *)
            swap_to_0_aux n i' × 
            (I (2^i) ⊗ swap ⊗ I (2^(n-i-2))) (* swap i-1 with 0 *)
  end.

(* Requires: i < n *)
Definition swap_to_0 (n i : nat) : Matrix (2^n) (2^n) := 
  match i with 
  | O => I (2^n) 
  | S i' => swap_to_0_aux n i'
  end.
  
(* Swapping qubits i and j in an n-qubit system, where i < j *) 
(* Requires i < j, j < n *)
Fixpoint swap_two_aux (n i j : nat) : Matrix (2^n) (2^n) := 
  match i with 
  | O => swap_to_0 n j 
  | S i' => I 2 ⊗ swap_two_aux (n-1) (i') (j-1)
  end.

(* Swapping qubits i and j in an n-qubit system *)
(* Requires i < n, j < n *)
Definition swap_two (n i j : nat) : Matrix (2^n) (2^n) :=
  if i =? j then I (2^n) 
  else if i <? j then swap_two_aux n i j
  else swap_two_aux n j i.

(* Simpler version of swap_to_0 that shifts other elements *)
(* Requires: i+1 < n *)
Fixpoint move_to_0_aux (n i : nat) {struct i}: Matrix (2^n) (2^n) := 
  match i with
  | O => swap ⊗ I (2^(n-2))
  | S i' => (move_to_0_aux n i') × (I (2^i) ⊗ swap ⊗ I (2^(n-i-2))) 
                  
  end.
             
(* Requires: i < n *)
Definition move_to_0 (n i : nat) : Matrix (2^n) (2^n) := 
  match i with 
  | O => I (2^n) 
  | S i' => move_to_0_aux n i'
  end.
 
(* Always moves up in the matrix from i to k *)
(* Requires: k < i < n *)
Fixpoint move_to (n i k : nat) : Matrix (2^n) (2^n) := 
  match k with 
  | O => move_to_0 n i 
  | S k' => I 2 ⊗ move_to (n-1) (i-1) (k')
  end.

(*
Eval compute in ((swap_two 1 0 1) 0 0)%nat.
Eval compute in (print_matrix (swap_two 1 0 2)).
*)

Lemma swap_eq_kron_comm : swap = kron_comm 2 2.
Proof. solve_matrix_fast_with idtac reflexivity. Qed.

Lemma swap_swap : swap × swap = I (2*2). 
Proof. rewrite swap_eq_kron_comm. apply kron_comm_mul_inv. Qed.

Lemma swap_swap_r : forall (A : Matrix (2*2) (2*2)), 
  WF_Matrix A ->
  A × swap × swap = A.
Proof.
  intros.
  rewrite Mmult_assoc.
  rewrite swap_swap.
  now apply Mmult_1_r.
Qed.

#[global] Hint Rewrite swap_swap swap_swap_r using (auto 100 with wf_db): Q_db.

Lemma braplus_transpose_ketplus :
⟨+∣⊤ = ∣+⟩.
Proof. solve_matrix_fast. Qed.

Lemma braminus_transpose_ketminus :
⟨-∣⊤ = ∣-⟩.
Proof. solve_matrix_fast. Qed.

Lemma Mmultplus0 : 
	⟨+∣ × ∣0⟩ = / (√2)%R .* I 1.
Proof.
	unfold braplus.
	rewrite Mscale_mult_dist_l.
	rewrite Mmult_plus_distr_r.
	rewrite Mmult00.
	rewrite Mmult10.
  lma.
Qed.

Lemma Mmult0plus : 
	⟨0∣ × ∣+⟩ = / (√2)%R .* I 1.
Proof.
	unfold xbasis_plus.
	rewrite Mscale_mult_dist_r.
	rewrite Mmult_plus_distr_l.
	rewrite Mmult00.
	rewrite Mmult01.
	lma.
Qed.

Lemma Mmultplus1 : 
	⟨+∣ × ∣1⟩ = / (√2)%R .* I 1.
Proof.
	unfold braplus.
	rewrite Mscale_mult_dist_l.
	rewrite Mmult_plus_distr_r.
	rewrite Mmult01.
	rewrite Mmult11.
	lma.
Qed.

Lemma Mmult1plus : 
	⟨1∣ × ∣+⟩ = / (√2)%R .* I 1.
Proof.
	unfold xbasis_plus.
	rewrite Mscale_mult_dist_r.
	rewrite Mmult_plus_distr_l.
	rewrite Mmult10.
	rewrite Mmult11.
	lma.
Qed.

Lemma Mmultminus0 : 
	⟨-∣ × ∣0⟩ = / (√2)%R .* I 1.
Proof.
	unfold braminus.
	rewrite Mscale_mult_dist_l.
	rewrite Mmult_plus_distr_r.
	rewrite Mmult00.
	rewrite Mscale_mult_dist_l.
	rewrite Mmult10.
	lma.
Qed.

Lemma Mmult0minus : 
	⟨0∣ × ∣-⟩ = / (√2)%R .* I 1.
Proof.
	unfold xbasis_minus.
	rewrite Mscale_mult_dist_r.
	rewrite Mmult_plus_distr_l.
	rewrite Mmult00.
	rewrite Mscale_mult_dist_r.
	rewrite Mmult01.
	lma.
Qed.

Lemma Mmultminus1 : 
	⟨-∣ × ∣1⟩ = - / (√2)%R .* I 1.
Proof.
	unfold braminus.
	rewrite Mscale_mult_dist_l.
	rewrite Mmult_plus_distr_r.
	rewrite Mmult01.
	rewrite Mscale_mult_dist_l.
	rewrite Mmult11.
	lma.
Qed.

Lemma Mmult1minus : 
	⟨1∣ × ∣-⟩ = - / (√2)%R .* I 1.
Proof.
	unfold xbasis_minus.
	rewrite Mscale_mult_dist_r.
	rewrite Mmult_plus_distr_l.
	rewrite Mmult10.
	rewrite Mscale_mult_dist_r.
	rewrite Mmult11.
	lma.
Qed.

Lemma Mmultminusminus : 
	⟨-∣ × ∣-⟩ = I 1.
Proof.
  prep_matrix_equivalence.
  unfold braminus.
	unfold xbasis_minus.
  distribute_scale.
  group_radicals.
  by_cell; lca.
Qed.

Lemma Mmultplusminus : 
	⟨+∣ × ∣-⟩ = Zero.
Proof.
  prep_matrix_equivalence.
  unfold braplus, xbasis_minus.
  distribute_scale.
  group_radicals.
  by_cell; lca.
Qed.

Lemma Mmultminusplus : 
	⟨-∣ × ∣+⟩ = Zero.
Proof.
  prep_matrix_equivalence.
	unfold xbasis_plus, braminus.
  distribute_scale.
  group_radicals.
  by_cell; lca.
Qed.

Lemma Mmultplusplus : 
	⟨+∣ × ∣+⟩ = I 1.
Proof.
  prep_matrix_equivalence.
	unfold xbasis_plus, braplus.
  distribute_scale.
  group_radicals.
  by_cell; lca.
Qed.

#[export] Hint Rewrite 
	Mmult00 Mmult01 Mmult10 Mmult11 
	Mmultplus0 Mmultplus1 Mmultminus0 Mmultminus1
	Mmult0plus Mmult0minus Mmult1plus Mmult1minus
	Mmultplusplus Mmultplusminus Mmultminusplus Mmultminusminus
	: ketbra_mult_db.

Lemma bra0transpose :
	⟨0∣⊤ = ∣0⟩.
Proof. solve_matrix_fast. Qed.

Lemma bra1transpose :
	⟨1∣⊤ = ∣1⟩.
Proof. solve_matrix_fast. Qed.

Lemma ket0transpose :
	∣0⟩⊤ = ⟨0∣.
Proof. solve_matrix_fast. Qed.

Lemma ket1transpose :
	∣1⟩⊤ = ⟨1∣.
Proof. solve_matrix_fast. Qed.

Lemma Mplus_plus_minus : ∣+⟩ .+ ∣-⟩ = (√2)%R .* ∣0⟩.
Proof. 
  solve_matrix_fast_with 
    (unfold xbasis_plus, xbasis_minus; autounfold with U_db) 
    (cbn; try lca; Csimpl; C_field; lca).
Qed.

Lemma Mplus_plus_minus_opp : ∣+⟩ .+ -1 .* ∣-⟩ = (√2)%R .* ∣1⟩.
Proof.
  solve_matrix_fast_with 
    (unfold xbasis_plus, xbasis_minus; autounfold with U_db) 
    (cbn; try lca; Csimpl; C_field; lca).
Qed.

Lemma Mplus_minus_plus : ∣-⟩ .+ ∣+⟩ = (√2)%R .* ∣0⟩.
Proof. 
  solve_matrix_fast_with 
    (unfold xbasis_plus, xbasis_minus; autounfold with U_db) 
    (cbn; try lca; Csimpl; C_field; lca).
Qed.

Lemma Mplus_minus_opp_plus : -1 .* ∣-⟩ .+ ∣+⟩ = (√2)%R .* ∣1⟩.
Proof.
  solve_matrix_fast_with 
    (unfold xbasis_plus, xbasis_minus; autounfold with U_db) 
    (cbn; try lca; Csimpl; C_field; lca).
Qed.

Lemma Mplus_0_1 : ∣0⟩ .+ ∣1⟩ = (√2)%R .* ∣+⟩.
Proof. 
  solve_matrix_fast_with 
    (unfold xbasis_plus, xbasis_minus; autounfold with U_db) 
    (cbn; try lca; Csimpl; C_field; lca).
Qed.

Lemma Mplus_0_1_opp : ∣0⟩ .+ -1 .* ∣1⟩ = (√2)%R .* ∣-⟩.
Proof. 
  solve_matrix_fast_with 
    (unfold xbasis_plus, xbasis_minus; autounfold with U_db) 
    (cbn; try lca; Csimpl; C_field; lca).
Qed.

Lemma Mplus_1_0 : ∣1⟩ .+ ∣0⟩ = (√2)%R .* ∣+⟩.
Proof. 
  solve_matrix_fast_with 
    (unfold xbasis_plus, xbasis_minus; autounfold with U_db) 
    (cbn; try lca; Csimpl; C_field; lca).
Qed.

Lemma Mplus_1_opp_0 : -1 .* ∣1⟩ .+ ∣0⟩ = (√2)%R .* ∣-⟩.
Proof.
  solve_matrix_fast_with 
    (unfold xbasis_plus, xbasis_minus; autounfold with U_db) 
    (cbn; try lca; Csimpl; C_field; lca).
Qed.

Lemma σz_decomposition : σz = ∣0⟩⟨0∣ .+ -1 .* ∣1⟩⟨1∣.
Proof. solve_matrix_fast. Qed.

(* It may be possible to remove the WF_Matrix B hypothesis *)
Lemma direct_sum_decomp : forall (m n o p : nat) (A B : Matrix m n), 
  WF_Matrix A -> WF_Matrix B ->
  A .⊕ B = ∣0⟩⟨0∣ ⊗ A .+ ∣1⟩⟨1∣ ⊗ B.
Proof.
  intros m n o p A B HA HB.
  prep_matrix_equivalence.
  unfold direct_sum, kron, Mplus.
  intros i j Hi Hj.
  bdestruct (i <? m); bdestruct (j <? n).
  - rewrite ?Nat.div_small, ?Nat.mod_small by easy; lca.
  - simpl.
    rewrite Nat.div_small, HA by lia.
    replace (j/n)%nat with 1%nat by 
      (symmetry; rewrite div_eq_iff; lia).
    lca.
  - simpl.
    rewrite (Nat.div_small j n), HA by lia.
    replace (i/m)%nat with 1%nat by 
      (symmetry; rewrite div_eq_iff; lia).
    lca.
  - simpl.
    replace (i/m)%nat with 1%nat by 
      (symmetry; rewrite div_eq_iff; lia).
    replace (j/n)%nat with 1%nat by 
      (symmetry; rewrite div_eq_iff; lia).
    rewrite 2!Modulus.mod_n_to_2n by lia.
    lca.
Qed.



Lemma cnot_decomposition : ∣1⟩⟨1∣ ⊗ σx .+ ∣0⟩⟨0∣ ⊗ I 2 = cnot.
Proof. solve_matrix_fast. Qed.                                               

Lemma notc_decomposition : σx ⊗ ∣1⟩⟨1∣ .+ I 2 ⊗ ∣0⟩⟨0∣ = notc.
Proof. solve_matrix_fast. Qed.                                               





(***************************)
(** Unitaries are unitary **)
(***************************)

(* For this section, we could just convert all single-qubit unitaries into their 
   rotation form and use rotation_unitary. *)

Definition WF_Unitary {n: nat} (U : Matrix n n): Prop :=
  WF_Matrix U /\ U † × U = I n.

#[export] Hint Unfold WF_Unitary : U_db.

(* More precise *)
(* Definition unitary_matrix' {n: nat} (A : Matrix n n): Prop := Minv A A†. *)

Lemma H_unitary : WF_Unitary hadamard.
Proof.
  split; [auto_wf|].
  solve_matrix_fast_with (autounfold with U_db)
    (now autorewrite with C_db).
Qed.

Lemma σx_unitary : WF_Unitary σx.
Proof. 
  split; [auto_wf|].
  solve_matrix_fast.
Qed.

Lemma σy_unitary : WF_Unitary σy.
Proof.
  split; [auto_wf|].
  solve_matrix_fast.
Qed.

Lemma σz_unitary : WF_Unitary σz.
Proof.
  split; [auto_wf|].
  solve_matrix_fast.
Qed.

Lemma phase_unitary : forall ϕ, @WF_Unitary 2 (phase_shift ϕ).
Proof.
  intros ϕ.
  split; [auto_wf|].
  lma'.
  unfold adjoint.
  cbn.
  autorewrite with C_db.
  rewrite <- Cmod_sqr, Cmod_Cexp.
  lca.
Qed.

Lemma S_unitary : WF_Unitary Sgate. Proof. apply phase_unitary. Qed.

Lemma T_unitary : WF_Unitary Tgate. Proof. apply phase_unitary. Qed.

Lemma rotation_unitary : forall θ ϕ λ, @WF_Unitary 2 (rotation θ ϕ λ).
Proof.
  intros.
  split; [auto_wf|].
  prep_matrix_equivalence.
  by_cell;
  autounfold with U_db; cbn; 
  rewrite <- 2?Cmod_sqr, 2?Cmod_mult, 1?Cmod_opp, 2?Cmod_Cexp;
  Csimpl.
  - rewrite Rmult_1_l.
    rewrite !Cmod_R.
    rewrite 2!RtoC_pow, <- RtoC_plus.
    apply c_proj_eq; [|easy].
    cbn [fst RtoC].
    rewrite <- !Rsqr_pow2, <- !Rsqr_abs.
    pose proof (sin2_cos2 (θ / 2)).
    lra.
  - rewrite Cconj_mult_distr, !Cexp_conj_neg.
    Csimpl.
    rewrite Cplus_comm, Cmult_assoc, (Cmult_comm _ (Cexp _)).
    rewrite Cmult_assoc, <- Cexp_add.
    rewrite Rplus_comm, <- Rplus_assoc, Rplus_opp_l, Rplus_0_l.
    C_field.
  - rewrite !Cconj_mult_distr, Cconj_opp, !Cexp_conj_neg.
    Csimpl.
    rewrite Cplus_comm, Cmult_assoc, (Cmult_comm _ (Cexp _)).
    rewrite Cmult_assoc, <- Cexp_add.
    rewrite Ropp_plus_distr, <- Rplus_assoc, 
      Rplus_opp_r, Rplus_0_l.
    C_field.
  - rewrite !Rmult_1_l.
    rewrite !Cmod_R.
    rewrite 2!RtoC_pow, <- RtoC_plus.
    apply c_proj_eq; [|easy].
    cbn [fst RtoC].
    rewrite <- !Rsqr_pow2, <- !Rsqr_abs.
    pose proof (sin2_cos2 (θ / 2)).
    lra.
Qed.

Lemma x_rotation_unitary : forall θ, @WF_Unitary 2 (x_rotation θ).
Proof. intros. rewrite <- Rx_rotation. apply rotation_unitary. Qed.

Lemma y_rotation_unitary : forall θ, @WF_Unitary 2 (y_rotation θ).
Proof. intros. rewrite <- Ry_rotation. apply rotation_unitary. Qed.

Lemma control_eq_direct_sum : forall n (A : Matrix n n),
  control A = I n .⊕ A.
Proof.
  intros n A.
  prep_matrix_equality.
  unfold direct_sum.
  autounfold with U_db.
  Modulus.bdestructΩ'.
Qed.

Lemma control_unitary : forall n (A : Matrix n n),
                          WF_Unitary A -> WF_Unitary (control A). 
Proof.
  intros n A H.
  destruct H as [WF U].
  split; auto with wf_db.
  rewrite control_eq_direct_sum.
  restore_dims.
  rewrite direct_sum_adjoint.
  rewrite <- direct_sum_Mmult by auto_wf.
  rewrite U.
  Msimpl.
  rewrite direct_sum_id.
  f_equal; lia.
Qed.

#[export] Hint Resolve H_unitary S_unitary T_unitary σx_unitary σy_unitary σz_unitary : unit_db.
#[export] Hint Resolve phase_unitary rotation_unitary x_rotation_unitary y_rotation_unitary control_unitary : unit_db.


Lemma transpose_unitary : forall n (A : Matrix n n), WF_Unitary A -> WF_Unitary (A⊤).
Proof.
  intros n A [HA U].
  split; [auto_wf|].
  change ((A⊤)†) with ((A†)⊤).
  rewrite <- Mmult_transpose.
  rewrite Minv_flip; auto with wf_db.
  apply id_transpose_eq.
Qed.
                      
Lemma adjoint_unitary : forall n (A : Matrix n n), WF_Unitary A -> WF_Unitary (A†).
Proof.
  intros n A [HA U].
  split; [auto_wf|].
  rewrite adjoint_involutive.
  rewrite Minv_flip; auto with wf_db.
Qed.

Lemma cnot_unitary : WF_Unitary cnot.
Proof.
  split; [auto_wf|].
  solve_matrix_fast.
Qed.

Lemma notc_unitary : WF_Unitary notc.
Proof.
  split; [auto_wf|].
  solve_matrix_fast.
Qed.

Lemma id_unitary : forall n, WF_Unitary (I n). 
Proof.
  split; [auto_wf|].
  now Msimpl_light.
Qed.

Lemma swap_unitary : WF_Unitary swap.
Proof. 
  split; [auto_wf|].
  rewrite swap_eq_kron_comm.
  now rewrite kron_comm_adjoint, kron_comm_mul_inv.
Qed.

Lemma zero_not_unitary : forall n, ~ (WF_Unitary (@Zero (2^n) (2^n))).
Proof.
  intros n.
  intros F.
  destruct F as [_ U].
  apply (f_equal2_inv 0 0)%nat in U.
  revert U.
  rewrite Mmult_0_r.
  unfold I, Zero.
  simpl.
  Modulus.simplify_bools_moddy_lia_one_kernel.
  pose proof C1_neq_C0.
  auto.
Qed.

Lemma kron_unitary : forall {m n} (A : Matrix m m) (B : Matrix n n),
  WF_Unitary A -> WF_Unitary B -> WF_Unitary (A ⊗ B).
Proof.
  intros m n A B [WFA UA] [WFB UB].
  unfold WF_Unitary in *.
  split; [auto_wf|].
  rewrite kron_adjoint.
  rewrite kron_mixed_product.
  rewrite UA, UB.
  rewrite id_kron. 
  easy.
Qed.

Lemma big_kron_unitary : forall (n : nat) (ls : list (Square n)), 
  (forall a, In a ls -> WF_Unitary a) -> WF_Unitary (⨂ ls).
Proof. 
  intros. induction ls as [| h].
  - apply id_unitary.
  - simpl.
    apply kron_unitary.
    + apply (H h).
      left. easy.
    + apply IHls.
      intros. 
      apply H. right. easy.
Qed.

(* alternate version for more general length application *)
Lemma big_kron_unitary' : forall (n m : nat) (ls : list (Square n)), 
  length ls = m -> (forall a, In a ls -> WF_Unitary a) -> 
  @WF_Unitary (n^m) (⨂ ls).
Proof. 
  intros; subst. 
  now apply big_kron_unitary.
Qed.

Lemma Mmult_unitary : forall (n : nat) (A : Square n) (B : Square n),
  WF_Unitary A ->
  WF_Unitary B ->
  WF_Unitary (A × B).  
Proof.
  intros n A B [WFA UA] [WFB UB].
  split; [auto_wf|].
  Msimpl.
  rewrite Mmult_assoc.
  rewrite <- (Mmult_assoc A†).
  rewrite UA.
  Msimpl.
  apply UB.
Qed.

Lemma scale_unitary : forall (n : nat) (c : C) (A : Square n),
  WF_Unitary A ->
  (c * c ^*)%C = C1 ->
  WF_Unitary (c .* A).  
Proof.
  intros n c A [WFA UA] H.
  split.
  auto with wf_db.
  distribute_adjoint.
  distribute_scale.
  rewrite UA, Cmult_comm, H.
  apply Mscale_1_l.
Qed.

Lemma pad1_unitary : forall (n : nat) (c : C) (A : Square n),
  WF_Unitary A ->
  (c * c ^*)%C = C1 ->
  WF_Unitary (pad1 A c).
Proof. 
  intros n c A [WFA U] Hc.
  split; [auto_wf|].
  rewrite pad1_adjoint, <- pad1_mult.
  rewrite U, Cmult_comm, Hc, pad1_I. 
  easy.
Qed.

#[export] Hint Resolve transpose_unitary adjoint_unitary cnot_unitary notc_unitary id_unitary : unit_db.
#[export] Hint Resolve swap_unitary zero_not_unitary kron_unitary big_kron_unitary big_kron_unitary' Mmult_unitary scale_unitary pad1_unitary : unit_db.


Lemma unitary_conj_trans_real {n} {A : Matrix n n} (HA : WF_Unitary A) i j :
  snd ((A †%M × A) i j) = 0.
Proof.
  destruct HA as [_ Heq].
  apply (f_equal_inv i) in Heq.
  apply (f_equal_inv j) in Heq.
  rewrite Heq.
  unfold I.
  Modulus.bdestructΩ'.
Qed.

Lemma unitary_conj_trans_nonneg {n} {A : Matrix n n} 
  (HA : WF_Unitary A) i j :
  0 <= fst ((A †%M × A) i j).
Proof.
  rewrite (proj2 HA).
  unfold I; Modulus.bdestructΩ'; simpl; lra.
Qed.



Lemma hadamard_st : hadamard ⊤ = hadamard.
Proof. solve_matrix_fast. Qed.

Lemma adjoint_transpose_comm : forall m n (A : Matrix m n),
  A † ⊤ = A ⊤ †.
Proof. reflexivity. Qed.

(********************)
(* Self-adjointness *)
(********************)



Definition hermitian {n} (A : Square n) :=
  A† = A.



Lemma I_hermitian : forall {n}, hermitian (I n).
Proof.
  intros.
  apply id_adjoint_eq.
Qed.

Lemma hadamard_hermitian : hermitian hadamard. 
Proof. solve_matrix_fast. Qed.

Lemma σx_hermitian : hermitian σx.
Proof. solve_matrix_fast. Qed.

Lemma σy_hermitian : hermitian σy.
Proof. solve_matrix_fast. Qed.

Lemma σz_hermitian : hermitian σz.
Proof. solve_matrix_fast. Qed.

Lemma cnot_hermitian : hermitian cnot.
Proof. solve_matrix_fast. Qed.

Lemma swap_hermitian : hermitian swap.
Proof. solve_matrix_fast. Qed.



(* some more general herm lemmas *)

Lemma plus_hermitian : forall {n} (A B : Square n),  
  hermitian A -> hermitian B ->
  hermitian (A .+ B).
Proof. 
  intros n A B HA HB.
  unfold hermitian. 
  distribute_adjoint. 
  rewrite HA, HB.
  easy.
Qed.

Lemma adjoint_hermitian : forall {n} (A : Square n),  
  hermitian A ->
  hermitian A†.
Proof. 
  intros n A HA.
  unfold hermitian. 
  rewrite 2!HA.
  easy.
Qed.

Lemma unit_conj_hermitian : forall {n} (A U : Square n), 
  hermitian A -> WF_Unitary U ->
  hermitian (U × A × U†). 
Proof. 
  intros n A U HA [HUWF HU]. 
  unfold hermitian in *.
  rewrite 2 Mmult_adjoint, adjoint_involutive, Mmult_assoc, HA.
  easy.
Qed.

Lemma AAadjoint_hermitian : forall {m n} (A : Matrix m n),
  hermitian (A × A†).
Proof. 
  intros.
  unfold hermitian.
  rewrite Mmult_adjoint, adjoint_involutive.
  easy.
Qed.

Lemma AadjointA_hermitian : forall {m n} (A : Matrix m n),
  hermitian (A† × A).
Proof. 
  intros.
  unfold hermitian.
  rewrite Mmult_adjoint, adjoint_involutive.
  easy.
Qed.

Lemma control_adjoint : forall n (U : Square n), (control U)† = control (U†).
Proof.
  intros n U.
  rewrite !control_eq_direct_sum.
  restore_dims.
  now rewrite direct_sum_adjoint, id_adjoint_eq.
Qed.

Lemma control_hermitian : forall (n : nat) (A : Square n), 
  hermitian A -> hermitian (control A).  
Proof.
  intros n A HA.
  unfold hermitian in *.
  rewrite control_adjoint.
  rewrite HA.
  easy.
Qed.

Lemma phase_adjoint : forall ϕ, (phase_shift ϕ)† = phase_shift (-ϕ). 
Proof.
  intros ϕ.
  prep_matrix_equivalence.
  unfold phase_shift, adjoint.
  rewrite <- Cexp_conj_neg.
  by_cell; lca.
Qed.


(* x and y rotation adjoints aren't x and rotations? *)

Lemma rotation_adjoint : forall θ ϕ λ, (rotation θ ϕ λ)† = rotation (-θ) (-λ) (-ϕ).
Proof.
  intros.
  prep_matrix_equivalence.
  unfold rotation, adjoint.
  rewrite Rdiv_opp_l, cos_neg, sin_neg.
  by_cell; rewrite ?Cconj_mult_distr; Csimpl.
  - reflexivity.
  - rewrite Cexp_conj_neg.
    lca.
  - rewrite Cconj_opp, Cexp_conj_neg.
    lca.
  - rewrite Cexp_conj_neg.
    now rewrite Ropp_plus_distr, Rplus_comm.
Qed.

Lemma braket0_hermitian : hermitian ∣0⟩⟨0∣. Proof. lma. Qed.
Lemma braket1_hermitian : hermitian ∣1⟩⟨1∣. Proof. lma. Qed.

(* Rewrite hangs on trying to rewrite hermitian, so we need to manually 
   expose the underlying equality. This was the cause of a bad bug 
   causing Qsimpl to hang. *)
(* #[global] Hint Rewrite hadamard_hermitian σx_hermitian σy_hermitian σz_hermitian cnot_hermitian swap_hermitian braket1_hermitian braket0_hermitian control_adjoint phase_adjoint rotation_adjoint : Q_db. *)

Local Ltac make_herm H :=
  let T := type of H in 
  let T' := eval unfold hermitian in T in 
  exact (H : T').

Definition hadamard_hermitian_rw := ltac:(make_herm hadamard_hermitian).
Definition σx_hermitian_rw := ltac:(make_herm σx_hermitian).
Definition σy_hermitian_rw := ltac:(make_herm σy_hermitian).
Definition σz_hermitian_rw := ltac:(make_herm σz_hermitian).
Definition cnot_hermitian_rw := ltac:(make_herm cnot_hermitian).
Definition swap_hermitian_rw := ltac:(make_herm swap_hermitian).
Definition braket1_hermitian_rw := ltac:(make_herm braket1_hermitian).
Definition braket0_hermitian_rw := ltac:(make_herm braket0_hermitian).
Definition control_adjoint_rw := ltac:(make_herm control_adjoint).
Definition phase_adjoint_rw := ltac:(make_herm phase_adjoint).
Definition rotation_adjoint_rw := ltac:(make_herm rotation_adjoint).


#[global] Hint Rewrite hadamard_hermitian_rw 
  σx_hermitian_rw σy_hermitian_rw σz_hermitian_rw cnot_hermitian_rw 
  swap_hermitian_rw braket1_hermitian_rw braket0_hermitian_rw 
  control_adjoint_rw phase_adjoint_rw rotation_adjoint_rw : Q_db.

(* THESE ARE TO BE PHASED OUT *) 
(* TODO: Is this true now that rewriting with 
  hermitian is known to be impossible? *)



#[deprecated(note="Use I_hermitian instead")]
Notation id_sa := I_hermitian (only parsing).

#[deprecated(note="Use hadamard_hermitian instead")]
Notation hadamard_sa := hadamard_hermitian (only parsing).

#[deprecated(note="Use σx_hermitian instead")]
Notation σx_sa := σx_hermitian (only parsing).

#[deprecated(note="Use σy_hermitian instead")]
Notation σy_sa := σy_hermitian (only parsing).

#[deprecated(note="Use σz_hermitian instead")]
Notation σz_sa := σz_hermitian (only parsing).

#[deprecated(note="Use cnot_hermitian instead")]
Notation cnot_sa := cnot_hermitian (only parsing).

#[deprecated(note="Use swap_hermitian instead")]
Notation swap_sa := swap_hermitian (only parsing).

#[deprecated(note="Use control_hermitian instead")]
Notation control_sa := control_hermitian (only parsing).


#[deprecated(note="Use braket0_hermitian instead")]
Notation braqubit0_sa := braket0_hermitian (only parsing).

#[deprecated(note="Use braket1_hermitian instead")]
Notation braqubit1_sa := braket1_hermitian (only parsing).



(*
Definition id_sa := id_adjoint_eq.

Lemma hadamard_sa : hadamard† = hadamard.
Proof.
  prep_matrix_equality.
  repeat (try destruct x; try destruct y; try lca; trivial).
Qed.

Lemma σx_sa : σx† = σx.
Proof. 
  prep_matrix_equality. 
  repeat (try destruct x; try destruct y; try lca; trivial).
Qed.

Lemma σy_sa : σy† = σy.
Proof.
  prep_matrix_equality. 
  repeat (try destruct x; try destruct y; try lca; trivial).
Qed.

Lemma σz_sa : σz† = σz.
Proof.
  prep_matrix_equality. 
  repeat (try destruct x; try destruct y; try lca; trivial).
Qed.


Lemma cnot_sa : cnot† = cnot.
Proof.
  prep_matrix_equality. 
  repeat (try destruct x; try destruct y; try lca; trivial).
Qed.

Lemma swap_sa : swap† = swap.
Proof.
  prep_matrix_equality. 
  repeat (try destruct x; try destruct y; try lca; trivial).
Qed.




Lemma control_sa : forall (n : nat) (A : Square n), 
    A† = A -> (control A)† = (control A).
Proof.
  intros n A H.
  rewrite control_adjoint.
  rewrite H.
  easy.
Qed.  


Lemma braqubit0_sa : ∣0⟩⟨0∣† = ∣0⟩⟨0∣. Proof. lma. Qed.
Lemma braqubit1_sa : ∣1⟩⟨1∣† = ∣1⟩⟨1∣. Proof. lma. Qed.

*)


(* Rather use control_adjoint :
#[global] Hint Rewrite control_sa using (autorewrite with M_db; reflexivity) : M_db. *)



(*********************)
(** ** Phase Lemmas **)
(*********************)

Lemma phase_0 : phase_shift 0 = I 2.
Proof. 
  prep_matrix_equivalence.
  unfold phase_shift, I.
  rewrite Cexp_0.
  by_cell; reflexivity.
Qed.

Lemma phase_2pi : phase_shift (2 * PI) = I 2.
  prep_matrix_equivalence.
  unfold phase_shift, I. 
  rewrite Cexp_2PI.
  by_cell; reflexivity.
Qed.

Lemma phase_pi : phase_shift PI = σz.
Proof.
  unfold phase_shift, σz.
  rewrite Cexp_PI.
  rewrite <- RtoC_opp.
  reflexivity.
Qed.

Lemma phase_neg_pi : phase_shift (-PI) = σz.
Proof.
  unfold phase_shift, σz.
  rewrite Cexp_neg.
  rewrite Cexp_PI.
  replace (/ -1) with (Copp (RtoC 1)) by lca.
  reflexivity.
Qed.

Lemma phase_mul : forall θ θ', phase_shift θ × phase_shift θ' = phase_shift (θ + θ').
Proof.
  intros.
  solve_matrix_fast_with idtac (cbn; rewrite 1?Cexp_add; lca).
Qed.  

Lemma phase_pow : forall θ n, n ⨉ (phase_shift θ) = phase_shift (INR n * θ).
Proof. 
  intros. 
  induction n.
  - simpl; rewrite Rmult_0_l, phase_0.
    reflexivity. 
  - replace (INR (S n) * θ)%R with (θ + INR n * θ)%R by (rewrite S_INR; lra).
    rewrite <- phase_mul, <- IHn.
    easy.
Qed.  

(* Old, can probably remove *)
Lemma phase_PI4_m8 : forall k,
  phase_shift (IZR k * PI / 4) = phase_shift (IZR (k - 8) * PI / 4).
Proof.
  intros. unfold phase_shift. rewrite Cexp_PI4_m8. reflexivity.
Qed.

Lemma phase_mod_2PI : forall k, phase_shift (IZR k * PI) = phase_shift (IZR (k mod 2) * PI).
Proof.
  intros. unfold phase_shift. rewrite Cexp_mod_2PI. reflexivity.
Qed.

Lemma phase_mod_2PI_scaled : forall (k sc : Z), 
  sc <> 0%Z ->
  phase_shift (IZR k * PI / IZR sc) = phase_shift (IZR (k mod (2 * sc)) * PI / IZR sc).
Proof.
  intros. unfold phase_shift. rewrite Cexp_mod_2PI_scaled; easy. 
Qed.


#[global] Hint Rewrite phase_0 phase_2pi phase_pi phase_neg_pi : Q_db.


(* now we get some more identities: *)


Lemma MmultSS : Sgate × Sgate = σz. 
Proof. unfold Sgate.
       rewrite phase_mul.
       replace (PI / 2 + PI / 2)%R with PI by lra.
       rewrite phase_pi.
       easy.
Qed.

Lemma MmultTT : Tgate × Tgate = Sgate. 
Proof. unfold Sgate, Tgate.
       rewrite phase_mul.
       apply f_equal; lra.
Qed.

#[global] Hint Rewrite MmultSS MmultTT : Q_db.


(*****************************)
(* Positive Semidefiniteness *)
(*****************************)

(* TODO: should unify this def with the newly defined inner_product *)
Definition positive_semidefinite {n} (A : Square n) : Prop :=
  forall (z : Vector n), WF_Matrix z -> fst ((z† × A × z) O O) >= 0.  

Lemma positive_semidefinite_AAadjoint : forall {m n} (A : Matrix m n),
  positive_semidefinite (A × A†).
Proof. 
  intros. 
  unfold positive_semidefinite.
  intros. 
  replace (((z) † × (A × (A) †) × z) 0%nat 0%nat) with (⟨ A† × z, A† × z ⟩).
  - apply Rle_ge; apply inner_product_ge_0.
  - unfold inner_product.
    distribute_adjoint.
    rewrite adjoint_involutive, 3 Mmult_assoc. 
    easy.
Qed.

Lemma positive_semidefinite_AadjointA : forall {m n} (A : Matrix m n),
  positive_semidefinite (A† × A).
Proof. 
  intros. 
  assert (H' := (positive_semidefinite_AAadjoint A†)).
  rewrite adjoint_involutive in H'.
  easy.
Qed.

Lemma positive_semidefinite_unitary_conj : forall {n} (A U : Square n),
  WF_Unitary U ->
  positive_semidefinite A ->
  positive_semidefinite (U† × A × U).
Proof. 
  intros n A U [HUWF HU] HA. 
  unfold positive_semidefinite in *.
  intros z Hz. 
  replace ((z) † × ((U) † × A × U) × z) with (((z) † × (U†)) × A × (U × z))
    by (now rewrite !Mmult_assoc).
  rewrite <- Mmult_adjoint.
  apply HA.
  auto_wf.
Qed.

Lemma positive_semidefinite_unitary_conj_conv : forall {n} (A U : Square n),
  WF_Unitary U ->
  positive_semidefinite (U† × A × U) ->
  positive_semidefinite A.
Proof. 
  intros n A U [HUWF HU] HA.
  unfold positive_semidefinite in *.
  intros z Hz.
  replace ((z) † × A × z) with (((U† × z)† × (U† × A × U) × (U† × z))).
  - apply HA; auto_wf.
  - distribute_adjoint.
    rewrite adjoint_involutive.
    apply Minv_flip in HU; [|auto_wf..].
    rewrite 3 Mmult_assoc, <- (Mmult_assoc _ _ z), HU, Mmult_1_l by auto.
    rewrite <- 2 (Mmult_assoc U), HU, <- 2 Mmult_assoc, Mmult_1_r 
      by auto with wf_db.
    reflexivity. 
Qed.

Lemma pure_psd : forall (n : nat) (ϕ : Vector n), (WF_Matrix ϕ) -> 
  positive_semidefinite (ϕ × ϕ†). 
Proof.
  intros n ϕ WFϕ z WFZ.
  rewrite !Mmult_assoc.
  remember (ϕ† × z) as ψ.
  rewrite <- !Mmult_assoc.
  rewrite <- (adjoint_involutive _ _ ϕ).
  rewrite <- Mmult_adjoint.
  rewrite <- Heqψ.
  unfold Mmult. simpl.
  rewrite <- Ropp_mult_distr_l.
  rewrite Rplus_0_l.
  unfold Rminus.
  rewrite Ropp_involutive.
  rewrite <- 2!Rsqr_def.
  apply Rle_ge.
  apply Rplus_le_le_0_compat; apply Rle_0_sqr.
Qed.

Lemma braket0_psd : positive_semidefinite ∣0⟩⟨0∣.
Proof. apply pure_psd. auto_wf. Qed.

Lemma braket1_psd : positive_semidefinite ∣1⟩⟨1∣.
Proof. apply pure_psd. auto_wf. Qed.

Lemma H0_psd : positive_semidefinite (hadamard × ∣0⟩⟨0∣ × hadamard).
Proof. 
  rewrite !Mmult_assoc.
  rewrite <- hadamard_hermitian_rw.
  rewrite <- Mmult_adjoint.
  rewrite <- !Mmult_assoc.
  rewrite hadamard_hermitian_rw.
  apply pure_psd.
  auto_wf.
Qed.


(*************************)
(* Pure and Mixed States *)
(*************************)

Notation Density n := (Matrix n n) (only parsing). 

Definition Classical {n} (ρ : Density n) := forall i j, i <> j -> ρ i j = 0.

Definition Pure_State_Vector {n} (φ : Vector n): Prop := 
  WF_Matrix φ /\ φ† × φ = I  1.

Definition Pure_State {n} (ρ : Density n) : Prop := 
  exists φ, Pure_State_Vector φ /\ ρ = φ × φ†.

Inductive Mixed_State {n} : Matrix n n -> Prop :=
| Pure_S : forall ρ, Pure_State ρ -> Mixed_State ρ
| Mix_S : forall (p : R) ρ1 ρ2, 0 < p < 1 -> 
  Mixed_State ρ1 -> Mixed_State ρ2 ->
  Mixed_State (p .* ρ1 .+ (1-p)%R .* ρ2).  

Lemma WF_Pure : forall {n} (ρ : Density n), Pure_State ρ -> WF_Matrix ρ.
Proof. intros. destruct H as [φ [[WFφ IP1] Eρ]]. rewrite Eρ. auto_wf. Qed.
#[export] Hint Resolve WF_Pure : wf_db.

Lemma WF_Mixed : forall {n} (ρ : Density n), Mixed_State ρ -> WF_Matrix ρ.
Proof. intros n p H. induction H; auto_wf. Qed.
#[export] Hint Resolve WF_Mixed : wf_db.

Lemma pure0 : Pure_State ∣0⟩⟨0∣. 
Proof. exists ∣0⟩. split; [|easy]. split; [auto_wf|]. apply Mmult00. Qed.

Lemma pure1 : Pure_State ∣1⟩⟨1∣. 
Proof. exists ∣1⟩. split; [|easy]. split; [auto_wf|]. apply Mmult11. Qed.

Lemma pure_id1 : Pure_State (I 1).
Proof. 
  exists (I 1). 
  split; [|now Msimpl_light]. 
  split; [auto_wf|].
  now Msimpl_light.
Qed.
 
Lemma pure_dim1 : forall (ρ : Square 1), Pure_State ρ -> ρ = I 1.
Proof.
  intros p H. 
  assert (H' := H).
  apply WF_Pure in H'.
  destruct H as [φ [[WFφ IP1] Eρ]]. 
  apply Minv_flip in IP1; [|auto_wf..].
  rewrite Eρ; easy.
Qed.

Lemma pure_state_unitary_pres : forall {n} (ϕ : Vector n) (U : Square n),
  Pure_State_Vector ϕ -> WF_Unitary U -> Pure_State_Vector (U × ϕ).
Proof. 
  unfold Pure_State_Vector.
  intros n ϕ U [H H0] [H1 H2].
  split; [auto_wf|].
  distribute_adjoint.
  rewrite Mmult_assoc, <- (Mmult_assoc _ U), H2, Mmult_1_l; auto.
Qed.

Lemma pure_state_vector_kron : forall {n m} (ϕ : Vector n) (ψ : Vector m),
  Pure_State_Vector ϕ -> Pure_State_Vector ψ -> Pure_State_Vector (ϕ ⊗ ψ).
Proof.
  unfold Pure_State_Vector.
  intros n m ϕ ψ [WFu Pu] [WFv Pv].
  split.
  - apply WF_kron; auto.
  - Msimpl. rewrite Pu, Pv. apply kron_1_r.
Qed.

Lemma pure_state_kron : forall m n (ρ : Square m) (φ : Square n),
  Pure_State ρ -> Pure_State φ -> Pure_State (ρ ⊗ φ).
Proof.
  intros m n ρ φ [u [? Eρ]] [v [? Eφ]].
  exists (u ⊗ v).
  split.
  - apply pure_state_vector_kron; assumption.
  - Msimpl. now subst.
Qed.

Lemma mixed_state_kron : forall m n (ρ : Square m) (φ : Square n),
  Mixed_State ρ -> Mixed_State φ -> Mixed_State (ρ ⊗ φ).
Proof.
  intros m n ρ φ Mρ Mφ.
  induction Mρ.
  induction Mφ.
  - apply Pure_S. apply pure_state_kron; easy.
  - rewrite kron_plus_distr_l.
    rewrite 2 Mscale_kron_dist_r.
    apply Mix_S; easy.
  - rewrite kron_plus_distr_r.
    rewrite 2 Mscale_kron_dist_l.
    apply Mix_S; easy.
Qed.

Lemma pure_state_trace_1 : forall {n} (ρ : Density n), Pure_State ρ -> 
  trace ρ = 1.
Proof.
  intros n ρ [u [[WFu Uu] E]]. 
  subst.
  clear WFu.
  unfold trace.
  unfold Mmult, adjoint in *.
  simpl in *.
  apply (f_equal (fun A => A O O)) in Uu.
  unfold I in Uu; simpl in Uu.
  rewrite <- Uu.
  apply big_sum_eq_bounded.
  intros k Hk.
  lca.
Qed.

Lemma mixed_state_trace_1 : forall {n} (ρ : Density n), Mixed_State ρ -> trace ρ = 1.
Proof.
  intros n ρ H. 
  induction H. 
  - apply pure_state_trace_1. easy.
  - rewrite trace_plus_dist.
    rewrite 2 trace_mult_dist.
    rewrite IHMixed_State1, IHMixed_State2.
    lca.
Qed.

(* The following two lemmas say that for any mixed states, the elements along the 
   diagonal are real numbers in the [0,1] interval. *)

Lemma mixed_state_diag_in01 : forall {n} (ρ : Density n) i, Mixed_State ρ -> 
  0 <= fst (ρ i i) <= 1.
Proof.
  intros.
  induction H as [u Hu | p].
  - bdestruct (i <? n); 
    [|rewrite (ltac:(auto_wf) : WF_Matrix u) by lia; cbn; lra].
    assert (Hnonneg : forall j, 0 <= fst (u j j)).
    1: {
      intros j.
      destruct Hu as (x & Hx & Hux).
      subst u.
      unfold Mmult.
      cbn [big_sum].
      rewrite Cplus_0_l.
      unfold adjoint.
      rewrite Cmult_comm, <- Cmod_sqr, RtoC_pow.
      apply Rpow_pos.
      apply Cmod_ge_0.
    }
    split; [easy|].
    pose proof (pure_state_trace_1 u Hu) as Htrace.
    apply (f_equal fst) in Htrace.
    unfold trace in Htrace.
    (* rewrite Re_big_sum in Htrace. *)
    simpl in Htrace.
    rewrite <- Htrace.
    apply (big_sum_member_le (fun j => u j j)); easy.
  - simpl.
    rewrite !Rmult_0_l, !Rminus_0_r.
    split.
    + assert (0 <= p * fst (ρ1 i i))
        by (apply Rmult_le_pos; lra).
      assert (0 <= (1 - p) * fst (ρ2 i i))
        by (apply Rmult_le_pos; lra).
      lra.
    + assert (p * fst (ρ1 i i) <= p)%R 
        by (rewrite <- Rmult_1_r;
        apply Rmult_le_compat_l; lra).
      assert ((1 - p) * fst (ρ2 i i) <= (1-p))%R 
        by (rewrite <- Rmult_1_r;
        apply Rmult_le_compat_l; lra).
      lra.
Qed.

Lemma mixed_state_diag_real : forall {n} (ρ : Density n) i , 
  Mixed_State ρ -> 
  snd (ρ i i) = 0.
Proof.
  intros.
  induction H.
  + unfold Pure_State in H. 
  - destruct H as [φ [[WFφ IP1] Eρ]].
    rewrite Eρ.
    simpl. 
    lra.
  + simpl.
    rewrite IHMixed_State1, IHMixed_State2.
    repeat rewrite Rmult_0_r, Rmult_0_l.
    lra.
Qed.

Lemma mixed_dim1 : forall (ρ : Square 1), Mixed_State ρ -> ρ = I 1.
Proof.
  intros.  
  induction H.
  + apply pure_dim1; trivial.
  + rewrite IHMixed_State1, IHMixed_State2.
    prep_matrix_equality.
    lca.
Qed.



(** Density matrices and superoperators **)

Definition Superoperator m n := Density m -> Density n.

Definition WF_Superoperator {m n} (f : Superoperator m n) := 
  (forall ρ, Mixed_State ρ -> Mixed_State (f ρ)).   

Definition super {m n} (M : Matrix m n) : Superoperator n m := fun ρ => 
  M × ρ × M†.

Lemma super_I : forall n ρ, WF_Matrix ρ ->
  super (I n) ρ = ρ.
Proof.
  intros.
  unfold super.
  Msimpl.
  reflexivity.
Qed.

Lemma WF_super : forall  m n (U : Matrix m n) (ρ : Square n), 
  WF_Matrix U -> WF_Matrix ρ -> WF_Matrix (super U ρ).
Proof.
  unfold super.
  auto with wf_db.
Qed.

#[export] Hint Resolve WF_super : wf_db.

Lemma super_outer_product : forall m (φ : Matrix m 1) (U : Matrix m m), 
    super U (outer_product φ φ) = outer_product (U × φ) (U × φ).
Proof.
  intros. unfold super, outer_product.
  autorewrite with M_db Q_db.
  rewrite !Mmult_assoc. 
  reflexivity.
Qed.

Definition compose_super {m n p} 
  (g : Superoperator n p) (f : Superoperator m n) : Superoperator m p := 
  fun ρ => g (f ρ).

Lemma WF_compose_super : forall m n p 
  (g : Superoperator n p) (f : Superoperator m n) (ρ : Square m), 
  WF_Matrix ρ ->
  (forall A, WF_Matrix A -> WF_Matrix (f A)) ->
  (forall A, WF_Matrix A -> WF_Matrix (g A)) ->
  WF_Matrix (compose_super g f ρ).
Proof.
  unfold compose_super.
  auto.
Qed.

#[export] Hint Resolve WF_compose_super : wf_db.


Lemma compose_super_correct : forall {m n p} 
  (g : Superoperator n p) (f : Superoperator m n),
  WF_Superoperator g -> 
  WF_Superoperator f ->
  WF_Superoperator (compose_super g f).
Proof.
  intros m n p g f pf_g pf_f.
  unfold WF_Superoperator.
  intros ρ mixed.
  unfold compose_super.
  apply pf_g. apply pf_f. auto.
Qed.

Definition sum_super {m n} (f g : Superoperator m n) : Superoperator m n :=
  fun ρ => (1/2)%R .* f ρ .+ (1 - 1/2)%R .* g ρ.

Lemma sum_super_correct : forall m n (f g : Superoperator m n),
  WF_Superoperator f -> WF_Superoperator g -> 
  WF_Superoperator (sum_super f g).
Proof.
  intros m n f g wf_f wf_g ρ pf_ρ.
  unfold sum_super. 
  pose proof (wf_f _ pf_ρ).
  pose proof (wf_g _ pf_ρ).
  apply (Mix_S (1/2) (f ρ) (g ρ)); auto. 
  lra.
Qed.

(* Maybe we shouldn't call these superoperators? Neither is trace-preserving *)
Definition SZero {m n} : Superoperator m n := fun ρ => Zero.
Definition Splus {m n} (S T : Superoperator m n) : Superoperator m n :=
  fun ρ => S ρ .+ T ρ.

(* These are *)
Definition new0_op : Superoperator 1 2 := super ∣0⟩.
Definition new1_op : Superoperator 1 2 := super ∣1⟩.
Definition meas_op : Superoperator 2 2 := Splus (super ∣0⟩⟨0∣) (super ∣1⟩⟨1∣).
Definition discard_op : Superoperator 2 1 := Splus (super ⟨0∣) (super ⟨1∣).

Lemma pure_unitary : forall {n} (U ρ : Matrix n n), 
  WF_Unitary U -> Pure_State ρ -> Pure_State (super U ρ).
Proof.
  intros n U ρ [WFU H] [φ [[WFφ IP1] Eρ]].
  rewrite Eρ.
  exists (U × φ).
  split.
  - split; auto with wf_db.
    rewrite (Mmult_adjoint U φ).
    rewrite Mmult_assoc.
    rewrite <- (Mmult_assoc (U†)).
    rewrite H, Mmult_1_l, IP1; easy.
  - unfold super.
    rewrite (Mmult_adjoint U φ).
    repeat rewrite Mmult_assoc.
    reflexivity.
Qed.    

Lemma mixed_unitary : forall {n} (U ρ : Matrix n n), 
  WF_Unitary U -> Mixed_State ρ -> Mixed_State (super U ρ).
Proof.
  intros n U ρ H M.
  induction M.
  + apply Pure_S.
    apply pure_unitary; trivial.
  + unfold WF_Unitary, super in *.
    rewrite Mmult_plus_distr_l.
    rewrite Mmult_plus_distr_r.
    rewrite 2 Mscale_mult_dist_r.
    rewrite 2 Mscale_mult_dist_l.
    apply Mix_S; trivial.
Qed.

Lemma super_unitary_correct : forall {n} (U : Matrix n n), 
  WF_Unitary U -> WF_Superoperator (super U).
Proof.
  intros n U H ρ Mρ.
  apply mixed_unitary; easy.
Qed.

Lemma compose_super_assoc : forall {m n p q}
      (f : Superoperator m n) (g : Superoperator n p) (h : Superoperator p q), 
      compose_super (compose_super f g) h
    = compose_super f (compose_super g h).
Proof. easy. Qed.

Lemma compose_super_eq : forall {m n p} (A : Matrix m n) (B : Matrix n p), 
      compose_super (super A) (super B) = super (A × B).
Proof.
  intros.
  unfold compose_super, super.
  apply functional_extensionality. intros ρ.
  rewrite Mmult_adjoint.
  rewrite !Mmult_assoc.
  reflexivity.
Qed.

(**************)
(* Automation *)
(**************)

Ltac Qsimpl := try restore_dims; autorewrite with M_db_light M_db Q_db.


(****************************************)
(* Tests and Lemmas about swap matrices *)
(****************************************)

Lemma swap_spec : forall (q q' : Vector 2), 
  WF_Matrix q -> WF_Matrix q' ->
  swap × (q ⊗ q') = q' ⊗ q.
Proof.
  intros q q' WF WF'.
  rewrite swap_eq_kron_comm.
  rewrite kron_comm_commutes_l by easy.
  rewrite kron_comm_1_l.
  apply Mmult_1_r; auto_wf.
Qed.  

#[global] Hint Rewrite swap_spec using auto_wf : Q_db.

Lemma swap_transpose : swap ⊤%M = swap.
Proof. now rewrite swap_eq_kron_comm, kron_comm_transpose. Qed.

Lemma swap_spec' : 
  swap = ((ket 0 × bra 0)  ⊗ (ket 0 × bra 0) .+ (ket 0 × bra 1)  ⊗ (ket 1 × bra 0)
  .+ (ket 1 × bra 0)  ⊗ (ket 0 × bra 1) .+ (ket 1 × bra 1)  ⊗ (ket 1 × bra 1)).
Proof.
  solve_matrix_fast_with idtac (cbv; lca).
Qed.

Example swap_to_0_test_24 : forall (q0 q1 q2 q3 : Vector 2), 
  WF_Matrix q0 -> WF_Matrix q1 -> WF_Matrix q2 -> WF_Matrix q3 ->
  swap_to_0 4 2 × (q0 ⊗ q1 ⊗ q2 ⊗ q3) = (q2 ⊗ q1 ⊗ q0 ⊗ q3). 
Proof.
  intros q0 q1 q2 q3 WF0 WF1 WF2 WF3.
  unfold swap_to_0, swap_to_0_aux.
  simpl.
  rewrite !Mmult_assoc.
  rewrite (kron_assoc q0 q1) by auto with wf_db.
  restore_dims.
  rewrite 2!kron_mixed_product, swap_spec, 2!Mmult_1_l,
    <- kron_assoc by auto_wf.
  restore_dims.
  rewrite (kron_assoc (_ ⊗ _)) by auto_wf.
  rewrite kron_mixed_product, Mmult_1_l, swap_spec by auto_wf.
  restore_dims.
  rewrite <- kron_assoc, (kron_assoc q2) by auto_wf.
  rewrite 2!kron_mixed_product.
  rewrite 2!Mmult_1_l, swap_spec by auto_wf.
  restore_dims.
  rewrite <- !kron_assoc by auto_wf.
  reflexivity.
Qed.

Lemma swap_two_base : swap_two 2 1 0 = swap.
Proof. unfold swap_two. simpl. apply kron_1_r. Qed.

Lemma swap_second_two : swap_two 3 1 2 = I 2 ⊗ swap.
Proof.
  unfold swap_two.
  simpl.
  rewrite kron_1_r.
  reflexivity.
Qed.

Lemma swap_0_2 : swap_two 3 0 2 = (I 2 ⊗ swap) × (swap ⊗ I 2) × (I 2 ⊗ swap).
Proof.
  unfold swap_two.
  simpl.
  now rewrite kron_1_r.
Qed.

(*
Proposition swap_to_0_spec : forall (q q0 : Matrix 2 1) (n k : nat) (l1 l2 : list (Matrix 2 1)), 
   length l1 = (k - 1)%nat ->
   length l2 = (n - k - 2)%nat ->   
   @Mmult (2^n) (2^n) 1 (swap_to_0 n k) (⨂ ([q0] ++ l1 ++ [q] ++ l2)) = 
     ⨂ ([q] ++ l1 ++ [q0] ++ l2).

Proposition swap_two_spec : forall (q q0 : Matrix 2 1) (n0 n1 n2 n k : nat) (l0 l1 l2 : list (Matrix 2 1)), 
   length l0 = n0 ->
   length l1 = n1 ->
   length l2 = n2 ->   
   n = (n0 + n1 + n2 + 2)%nat ->
   @Mmult (2^n) (2^n) 1 
     (swap_two n n0 (n0+n1+1)) (⨂ (l0 ++ [q0] ++ l1 ++ [q] ++ l2)) = 
     ⨂ (l0 ++ [q] ++ l1 ++ [q0] ++ l2).
*)

Example move_to_0_test_24 : forall (q0 q1 q2 q3 : Vector 2), 
  WF_Matrix q0 -> WF_Matrix q1 -> WF_Matrix q2 -> WF_Matrix q3 ->
  move_to_0 4 2 × (q0 ⊗ q1 ⊗ q2 ⊗ q3) = (q2 ⊗ q0 ⊗ q1 ⊗ q3). 
Proof.
  intros q0 q1 q2 q3 WF0 WF1 WF2 WF3.
  unfold move_to_0, move_to_0_aux.
  repeat rewrite Mmult_assoc.
  rewrite (kron_assoc q0 q1) by auto with wf_db.
  simpl.
  restore_dims.
  rewrite 2!kron_mixed_product, 2!Mmult_1_l, swap_spec, <- kron_assoc by easy.
  restore_dims.
  rewrite kron_assoc by auto_wf.
  rewrite kron_mixed_product, Mmult_1_l, swap_spec by auto_wf.
  restore_dims.
  rewrite <- kron_assoc by auto_wf.
  reflexivity.
Qed.

(* *)


