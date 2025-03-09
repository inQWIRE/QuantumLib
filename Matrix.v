
(** In this file, we define matrices and prove many basic facts from linear algebra *)

Require Import Psatz. 
Require Import String.
Require Import Program.
Require Export Complex. 
Require Import List.
Require Import Setoid.
Require Import Modulus.


(* TODO: Use matrix equality everywhere, declare equivalence relation *)
(* TODO: Make all nat arguments to matrix lemmas implicit *)


(** * Matrix definitions and infrastructure **)



(* TODO: make this file with general field
Section LinearAlgebra.
  Variables (F : Type).
  Variable (H0 : Monoid F).
  Variable (H1 : Group F).
  Variable (H2 : Comm_Group F).
  Variable (H3 : Ring F).
  Variable (H4 : Comm_Ring F).
  Variable (H5 : Field F).
End LinearAlgebra.
*)



Declare Scope matrix_scope.
Delimit Scope matrix_scope with M.
Open Scope matrix_scope.

Local Open Scope nat_scope.

Definition Matrix (m n : nat) := nat -> nat -> C.

Definition WF_Matrix {m n: nat} (A : Matrix m n) : Prop := 
  forall x y, x >= m \/ y >= n -> A x y = C0. 

(* makes a matrix well formed *)
Definition make_WF {m n} (A : Matrix m n) : Matrix m n :=
  fun i j => if (i <? m) && (j <? n) then A i j else C0. 



Notation Vector n := (Matrix n 1).

Notation Square n := (Matrix n n).

(** Equality via functional extensionality *)
Ltac prep_matrix_equality :=
  let x := fresh "x" in 
  let y := fresh "y" in 
  apply functional_extensionality; intros x;
  apply functional_extensionality; intros y.

(** Matrix equivalence *)

Definition mat_equiv {m n : nat} (A B : Matrix m n) : Prop := 
  forall i j, i < m -> j < n -> A i j = B i j.

Infix "==" := mat_equiv (at level 70) : matrix_scope.

Lemma mat_equiv_refl : forall m n (A : Matrix m n), mat_equiv A A.
Proof. unfold mat_equiv; reflexivity. Qed.

Lemma mat_equiv_eq : forall {m n : nat} (A B : Matrix m n),
  WF_Matrix A -> 
  WF_Matrix B -> 
  A == B ->
  A = B.
Proof.
  intros m n A' B' WFA WFB Eq.
  prep_matrix_equality.
  unfold mat_equiv in Eq.
  bdestruct (x <? m).
  bdestruct (y <? n).
  + apply Eq; easy.
  + rewrite WFA, WFB; trivial; right; try lia.
  + rewrite WFA, WFB; trivial; left; try lia.
Qed.

Lemma WF_Matrix_dim_change : forall (m n m' n' : nat) (A : Matrix m n),
  m = m' ->
  n = n' ->
  @WF_Matrix m n A ->
  @WF_Matrix m' n' A.
Proof. intros. subst. easy. Qed.

(** Equality via bounded equality for WF matrices **)
Ltac prep_matrix_equivalence :=
  apply mat_equiv_eq;
  [solve [auto 100 with wf_db | 
  auto 100 using WF_Matrix_dim_change with wf_db zarith]..|].

(** Printing *)

Parameter print_C : C -> string.
Fixpoint print_row {m n} i j (A : Matrix m n) : string :=
  match j with
  | 0   => "\n"
  | S j' => print_C (A i j') ++ ", " ++ print_row i j' A
  end.
Fixpoint print_rows {m n} i j (A : Matrix m n) : string :=
  match i with
  | 0   => ""
  | S i' => print_row i' n A ++ print_rows i' n A
  end.
Definition print_matrix {m n} (A : Matrix m n) : string :=
  print_rows m n A.

(** 2D list representation *)
    
Definition list2D_to_matrix (l : list (list C)) : 
  Matrix (length l) (length (hd [] l)) :=
  (fun x y => nth y (nth x l []) 0%R).

Lemma WF_list2D_to_matrix : forall m n li, 
    length li = m ->
    (forall li', In li' li -> length li' = n)  ->
    @WF_Matrix m n (list2D_to_matrix li).
Proof.
  intros m n li L F x y [l | r].
  - unfold list2D_to_matrix. 
    rewrite (nth_overflow _ []).
    destruct y; easy.
    rewrite L. apply l.
  - unfold list2D_to_matrix. 
    rewrite (nth_overflow _ C0).
    easy.
    destruct (nth_in_or_default x li []) as [IN | DEF].
    apply F in IN.
    rewrite IN. apply r.
    rewrite DEF.
    simpl; lia.
Qed.

Lemma show_WF_list2D_to_matrix m n li : 
  length li = m ->
  forallb (fun x => length x =? n) li = true ->
  @WF_Matrix m n (list2D_to_matrix li).
Proof.
  intros Hlen.
  rewrite forallb_forall.
  intros Hin.
  setoid_rewrite Nat.eqb_eq in Hin.
  apply WF_list2D_to_matrix.
  easy.
  intros l Hl.
  rewrite Hin by easy.
  easy.
Qed.

(** Example *)
Definition M23 : Matrix 2 3 :=
  fun x y => 
  match (x, y) with
  | (0, 0) => 1%R
  | (0, 1) => 2%R
  | (0, 2) => 3%R
  | (1, 0) => 4%R
  | (1, 1) => 5%R
  | (1, 2) => 6%R
  | _ => C0
  end.

Definition M23' : Matrix 2 3 := 
  list2D_to_matrix  
  ([ [RtoC 1; RtoC 2; RtoC 3];
    [RtoC 4; RtoC 5; RtoC 6] ]).

Lemma M23eq : M23 = M23'.
Proof.
  unfold M23'.
  compute.
  prep_matrix_equality.
  do 4 (try destruct x; try destruct y; simpl; trivial).
Qed.


(** * Operands and operations **)


Definition Zero {m n : nat} : Matrix m n := fun x y => 0%R.

Definition I (n : nat) : Square n := 
  (fun x y => if (x =? y) && (x <? n) then C1 else C0).

Definition const_matrix {m n} (c : C) : Matrix m n :=
  make_WF (fun _ _ => c).

(* in many cases, n needs to be made explicit, but not always, hence it is made implicit here *)
Definition e_i {n : nat} (i : nat) : Vector n :=
  fun x y => (if (x =? i) && (x <? n) && (y =? 0) then C1 else C0). 



(* Optional coercion to scalar (should be limited to 1 × 1 matrices):
Definition to_scalar (m n : nat) (A: Matrix m n) : C := A 0 0.
Coercion to_scalar : Matrix >-> C.
*)

(* This isn't used, but is interesting *)
Definition I__inf := fun x y => if x =? y then C1 else C0.
Notation "I∞" := I__inf : matrix_scope.

Definition trace {n : nat} (A : Square n) := 
  big_sum (fun x => A x x) n.

Definition scale {m n : nat} (r : C) (A : Matrix m n) : Matrix m n := 
  fun x y => (r * A x y)%C.

Definition dot {n : nat} (A : Vector n) (B : Vector n) : C :=
  big_sum (fun x => A x 0  * B x 0)%C n.

Definition Mplus {m n : nat} (A B : Matrix m n) : Matrix m n :=
  fun x y => (A x y + B x y)%C.

Definition Mopp {m n : nat} (A : Matrix m n) : Matrix m n :=
  scale (-C1) A.

Definition Mminus {m n : nat} (A B : Matrix m n) : Matrix m n :=
  Mplus A (Mopp B).

Definition Mmult {m n o : nat} (A : Matrix m n) (B : Matrix n o) : Matrix m o := 
  fun x z => big_sum (fun y => A x y * B y z)%C n.

(* Only well-defined when o and p are non-zero *)
Definition kron {m n o p : nat} (A : Matrix m n) (B : Matrix o p) : 
  Matrix (m*o) (n*p) :=
  fun x y => Cmult (A (x / o) (y / p)) (B (x mod o) (y mod p)).

Definition direct_sum {m n o p : nat} (A : Matrix m n) (B : Matrix o p) :
  Matrix (m+o) (n+p) :=
  fun x y =>  if (x <? m) || (y <? n) then A x y else B (x - m) (y - n).

Definition transpose {m n} (A : Matrix m n) : Matrix n m := 
  fun x y => A y x.

Definition adjoint {m n} (A : Matrix m n) : Matrix n m := 
  fun x y => (A y x)^*.

(* note that the convention of quantum computing differs from abstract math, 
   hence this def *)
Definition inner_product {n} (u v : Vector n) : C := 
  Mmult (adjoint u) (v) 0 0.

Definition outer_product {n} (u v : Vector n) : Square n := 
  Mmult u (adjoint v).

(** Kronecker of n copies of A *)
Fixpoint kron_n n {m1 m2} (A : Matrix m1 m2) : Matrix (m1^n) (m2^n) :=
  match n with
  | 0    => I 1
  | S n' => kron (kron_n n' A) A
  end.

(** Kronecker product of a list *)
Fixpoint big_kron {m n} (As : list (Matrix m n)) : 
  Matrix (m^(length As)) (n^(length As)) := 
  match As with
  | [] => I 1
  | A :: As' => kron A (big_kron As')
  end.

(** Product of n copies of A *)
Fixpoint Mmult_n n {m} (A : Square m) : Square m :=
  match n with
  | 0    => I m
  | S n' => Mmult A (Mmult_n n' A)
  end.

(** Direct sum of n copies of A *)
Fixpoint direct_sum_n n {m1 m2} (A : Matrix m1 m2) : Matrix (n*m1) (n*m2) :=
  match n with
  | 0    => @Zero 0 0
  | S n' => direct_sum A (direct_sum_n n' A)
  end.


(** * Showing that M is a vector space *)
#[global] Program Instance M_is_monoid : forall n m, Monoid (Matrix n m) := 
  { Gzero := @Zero n m
  ; Gplus := Mplus
  }.
Solve All Obligations with program_simpl; prep_matrix_equality; lca. 

#[global] Program Instance M_is_group : forall n m, Group (Matrix n m) :=
  { Gopp := Mopp }.
Solve All Obligations with program_simpl; prep_matrix_equality; lca. 

#[global] Program Instance M_is_comm_group : forall n m, Comm_Group (Matrix n m).
Solve All Obligations with program_simpl; prep_matrix_equality; lca. 


#[global] Program Instance M_is_module_space : forall n m, Module_Space (Matrix n m) C :=
  { Vscale := scale }.
Solve All Obligations with program_simpl; prep_matrix_equality; lca. 

#[global] Program Instance M_is_vector_space : forall n m, Vector_Space (Matrix n m) C.


(** Notations *)
Infix "∘" := dot (at level 40, left associativity) : matrix_scope.
Infix ".+" := Mplus (at level 50, left associativity) : matrix_scope.
Infix ".*" := scale (at level 40, left associativity) : matrix_scope.
Infix "×" := Mmult (at level 40, left associativity) : matrix_scope.
Infix "⊗" := kron (at level 40, left associativity) : matrix_scope.
Infix ".⊕" := direct_sum (at level 20) : matrix_scope. (* should have different level and assoc *)
Infix "≡" := mat_equiv (at level 70) : matrix_scope.
Notation "A ⊤" := (transpose A) (at level 0) : matrix_scope. 
Notation "A †" := (adjoint A) (at level 0) : matrix_scope. 
Notation Σ := (@big_sum C C_is_monoid).  (* we intoduce Σ notation here *)
Notation "n ⨂ A" := (kron_n n A) (at level 30, no associativity) : matrix_scope.
Notation "⨂ A" := (big_kron A) (at level 60): matrix_scope.
Notation "n ⨉ A" := (Mmult_n n A) (at level 30, no associativity) : matrix_scope.
Notation "⟨ u , v ⟩" := (inner_product u v) (at level 0) : matrix_scope. 
#[export] Hint Unfold Zero I e_i trace dot Mplus scale Mmult kron mat_equiv transpose
            adjoint const_matrix make_WF : U_db.
  
Ltac destruct_m_1 :=
  match goal with
  | [ |- context[match ?x with 
                 | 0   => _
                 | S _ => _
                 end] ] => is_var x; destruct x
  end.
Ltac destruct_m_eq := repeat (destruct_m_1; simpl).

Ltac lma := 
  autounfold with U_db;
  prep_matrix_equality;
  destruct_m_eq; 
  lca.

Ltac solve_end :=
  match goal with
  | H : lt _ O |- _ => apply Nat.nlt_0_r in H; contradict H
  end.

Ltac by_cell_no_intros :=
  let i := fresh "i" in 
  let j := fresh "j" in 
  let Hi := fresh "Hi" in 
  let Hj := fresh "Hj" in 
  intros i j Hi Hj; try solve_end;
  repeat (destruct i as [|i]; simpl; [|apply <- Nat.succ_lt_mono in Hi]; try solve_end); clear Hi;
  repeat (destruct j as [|j]; simpl; [|apply <- Nat.succ_lt_mono in Hj]; try solve_end); clear Hj.

Ltac by_cell := 
  intros;
  by_cell_no_intros.

Ltac lma' :=
  apply mat_equiv_eq;
  repeat match goal with
  | [ |- WF_Matrix (?A) ]  => auto with wf_db (* (try show_wf) *)
  | [ |- mat_equiv (?A) (?B) ] => by_cell; try lca                 
  end.

(* lemmas which are useful for simplifying proofs involving matrix operations *)
Lemma kron_simplify : forall (n m o p : nat) (a b : Matrix n m) (c d : Matrix o p), 
    a = b -> c = d -> a ⊗ c = b ⊗ d.
Proof. intros; subst; easy. 
Qed.

Lemma n_kron_simplify : forall (n m : nat) (a b : Matrix n m) (n m : nat), 
    a = b -> n = m -> n ⨂ a = m ⨂ b.
Proof. intros; subst; easy. 
Qed.

Lemma Mtranspose_simplify : forall (n m : nat) (a b : Matrix n m), 
    a = b -> a⊤ = b⊤.
Proof. intros; subst; easy. 
Qed.

Lemma Madjoint_simplify : forall (n m : nat) (a b : Matrix n m), 
    a = b -> a† = b†.
Proof. intros; subst; easy. 
Qed.

Lemma Mmult_simplify : forall (n m o : nat) (a b : Matrix n m) (c d : Matrix m o), 
    a = b -> c = d -> a × c = b × d.
Proof. intros; subst; easy. 
Qed.

Lemma Mmult_n_simplify : forall (n : nat) (a b : Square n) (c d : nat), 
    a = b -> c = d -> c ⨉ a = d ⨉ b.
Proof. intros; subst; easy. 
Qed.

Lemma dot_simplify : forall (n : nat) (a b c d: Vector n), 
    a = b -> c = d -> a ∘ c = b ∘ c.
Proof. intros; subst; easy. 
Qed.

Lemma Mplus_simplify : forall (n m: nat) (a b : Matrix n m) (c d : Matrix n m), 
    a = b -> c = d -> a .+ c = b .+ d.
Proof. intros; subst; easy. 
Qed.

Lemma Mscale_simplify : forall (n m: nat) (a b : Matrix n m) (c d : C), 
    a = b -> c = d -> c .* a = d .* b.
Proof. intros; subst; easy. 
Qed.

(** * Proofs about mat_equiv *)

Lemma mat_equiv_sym : forall {n m : nat} (A B : Matrix n m),
  A ≡ B -> B ≡ A.
Proof.
  intros n m A B HAB i j Hi Hj.
  rewrite HAB by easy.
  easy.
Qed.

Lemma mat_equiv_trans : forall {n m : nat} (A B C : Matrix n m),
  A ≡ B -> B ≡ C -> A ≡ C.
Proof.
  intros n m A B C HAB HBC i j Hi Hj.
  rewrite HAB, HBC by easy.
  easy.
Qed.

#[global] Add Parametric Relation {n m} : (Matrix n m) mat_equiv
  reflexivity proved by (mat_equiv_refl _ _)
  symmetry proved by (mat_equiv_sym)
  transitivity proved by (mat_equiv_trans)
  as mat_equiv_rel.

Lemma mat_equiv_eq_iff {n m} : forall (A B : Matrix n m),
  WF_Matrix A -> WF_Matrix B -> A ≡ B <-> A = B.
Proof.
  intros; split; try apply mat_equiv_eq; 
  intros; try subst A; easy.
Qed.

Lemma Mmult_simplify_mat_equiv : forall {n m o} 
  (A B : Matrix n m) (C D : Matrix m o),
  A ≡ B -> C ≡ D -> A × C ≡ B × D.
Proof.
  intros n m o A B C D HAB HCD.
  intros i j Hi Hj.
  unfold Mmult.
  apply big_sum_eq_bounded.
  intros k Hk.
  rewrite HAB, HCD by easy.
  easy.
Qed.

Add Parametric Morphism {n m o} : (@Mmult n m o)
  with signature (@mat_equiv n m) ==> (@mat_equiv m o) ==> (@mat_equiv n o)
  as mmult_mat_equiv_morph.
Proof. intros; apply Mmult_simplify_mat_equiv; easy. Qed.

Lemma kron_simplify_mat_equiv {n m o p} : forall (A B : Matrix n m) 
  (C D : Matrix o p), A ≡ B -> C ≡ D -> A ⊗ C ≡ B ⊗ D.
Proof.
  intros A B C D HAB HCD i j Hi Hj.
  unfold kron.
  rewrite HAB, HCD; try easy.
  1,2: apply Nat.mod_upper_bound; lia.
  1,2: apply Nat.Div0.div_lt_upper_bound; lia.
Qed.

Add Parametric Morphism {n m o p} : (@kron n m o p) 
  with signature (@mat_equiv n m) ==> (@mat_equiv o p) 
    ==> (@mat_equiv (n*o) (m*p)) as kron_mat_equiv_morph.
Proof. intros; apply kron_simplify_mat_equiv; easy. Qed.

Lemma Mplus_simplify_mat_equiv : forall {n m} 
  (A B C D : Matrix n m),
  A ≡ B -> C ≡ D -> A .+ C ≡ B .+ D.
Proof.
  intros n m A B C D HAB HCD. 
  intros i j Hi Hj; unfold ".+"; 
  rewrite HAB, HCD; try easy. 
Qed.

Add Parametric Morphism {n m} : (@Mplus n m)
  with signature (@mat_equiv n m) ==> (@mat_equiv n m) ==> (@mat_equiv n m)
  as Mplus_mat_equiv_morph.
Proof. intros; apply Mplus_simplify_mat_equiv; easy. Qed.

Lemma scale_simplify_mat_equiv : forall {n m} 
  (x y : C) (A B : Matrix n m), 
  x = y -> A ≡ B -> x .* A ≡ y .* B.
Proof.
  intros n m x y A B Hxy HAB i j Hi Hj.
  unfold scale.
  rewrite Hxy, HAB; easy.
Qed.

Add Parametric Morphism {n m} : (@scale n m)
  with signature (@eq C) ==> (@mat_equiv n m) ==> (@mat_equiv n m)
  as scale_mat_equiv_morph.
Proof. intros; apply scale_simplify_mat_equiv; easy. Qed.

Lemma Mopp_simplify_mat_equiv : forall {n m} (A B : Matrix n m), 
  A ≡ B -> Mopp A ≡ Mopp B.
Proof.
  intros n m A B HAB i j Hi Hj.
  unfold Mopp, scale.
  rewrite HAB; easy.
Qed.

Add Parametric Morphism {n m} : (@Mopp n m)
  with signature (@mat_equiv n m) ==> (@mat_equiv n m)
  as Mopp_mat_equiv_morph.
Proof. intros; apply Mopp_simplify_mat_equiv; easy. Qed.

Lemma Mminus_simplify_mat_equiv : forall {n m} 
  (A B C D : Matrix n m),
  A ≡ B -> C ≡ D -> Mminus A C ≡ Mminus B D.
Proof.
  intros n m A B C D HAB HCD. 
  intros i j Hi Hj; unfold Mminus, Mopp, Mplus, scale;
  rewrite HAB, HCD; try easy. 
Qed.

Add Parametric Morphism {n m} : (@Mminus n m)
  with signature (@mat_equiv n m) ==> (@mat_equiv n m) ==> (@mat_equiv n m)
  as Mminus_mat_equiv_morph.
Proof. intros; apply Mminus_simplify_mat_equiv; easy. Qed.

Lemma dot_simplify_mat_equiv : forall {n} (A B : Vector n) 
  (C D : Vector n), A ≡ B -> C ≡ D -> dot A C = dot B D.
Proof.
  intros n A B C D HAB HCD.
  apply big_sum_eq_bounded.
  intros k Hk.
  rewrite HAB, HCD; unfold "<"%nat; easy.
Qed.

Add Parametric Morphism {n} : (@dot n)
  with signature (@mat_equiv n 1) ==> (@mat_equiv n 1) ==> (@eq C)
  as dot_mat_equiv_morph.
Proof. intros; apply dot_simplify_mat_equiv; easy. Qed.

Lemma transpose_simplify_mat_equiv {n m} : forall (A B : Matrix n m),
  A ≡ B -> A ⊤ ≡ B ⊤.
Proof.
  intros A B HAB i j Hi Hj.
  unfold transpose; auto.
Qed.

Lemma transpose_simplify_mat_equiv_inv {n m} : forall (A B : Matrix n m),
  A ⊤ ≡ B ⊤ -> A ≡ B.
Proof. 
  intros A B HAB i j Hi Hj.
  unfold transpose in *; auto.
Qed.

Add Parametric Morphism {n m} : (@transpose n m)
  with signature (@mat_equiv n m) ==> (@mat_equiv m n)
  as transpose_mat_equiv_morph.
Proof. intros; apply transpose_simplify_mat_equiv; easy. Qed.

Lemma adjoint_simplify_mat_equiv {n m} : forall (A B : Matrix n m),
  A ≡ B -> A † ≡ B †.
Proof.
  intros A B HAB i j Hi Hj.
  unfold adjoint;
  rewrite HAB by easy; easy.
Qed.

Add Parametric Morphism {n m} : (@adjoint n m)
  with signature (@mat_equiv n m) ==> (@mat_equiv m n)
  as adjoint_mat_equiv_morph.
Proof. intros; apply adjoint_simplify_mat_equiv; easy. Qed.

Lemma trace_of_mat_equiv : forall n (A B : Square n),
  A ≡ B -> trace A = trace B.
Proof.
  intros n A B HAB.
  (* unfold trace. *)
  apply big_sum_eq_bounded; intros i Hi.
  rewrite HAB; auto.
Qed.

Add Parametric Morphism {n} : (@trace n)
  with signature (@mat_equiv n n) ==> (eq)
  as trace_mat_equiv_morph.
Proof. intros; apply trace_of_mat_equiv; easy. Qed.

Lemma mat_equiv_equivalence : forall {n m}, 
  equivalence (Matrix n m) mat_equiv.
Proof.
  intros n m.
  constructor.
  - intros A. apply (mat_equiv_refl).
  - intros A; apply mat_equiv_trans.
  - intros A; apply mat_equiv_sym.
Qed.

Lemma big_sum_mat_equiv : forall {o p} (f g : nat -> Matrix o p)
  (Eq_on: forall x : nat, f x ≡ g x) (n : nat), big_sum f n ≡ big_sum g n.
Proof.
  intros o p f g Eq_on n.
  induction n.
  - easy.
  - simpl.
    rewrite IHn, Eq_on; easy.
Qed.

Add Parametric Morphism {n m} : (@big_sum (Matrix n m) (M_is_monoid n m))
  with signature 
  (Morphisms.pointwise_relation nat (@mat_equiv n m)) ==> (@eq nat) ==> 
  (@mat_equiv n m)
  as big_sum_mat_equiv_morph.
Proof. intros f g Eq_on k. apply big_sum_mat_equiv; easy. Qed.


(** * Proofs about well-formedness **)



Lemma WF_Matrix_dim_change_iff m n m' n' (A : Matrix m n) :
  m = m' -> n = n' ->
  @WF_Matrix m' n' A <-> WF_Matrix A.
Proof.
  intros.
  now subst.
Qed.

Lemma WF_make_WF : forall {m n} (A : Matrix m n), WF_Matrix (make_WF A).
Proof. intros. 
       unfold WF_Matrix, make_WF; intros. 
       destruct H as [H | H].
       bdestruct (x <? m); try lia; easy. 
       bdestruct (y <? n); bdestruct (x <? m); try lia; easy.
Qed.

Lemma WF_const_matrix m n c : 
  WF_Matrix (@const_matrix m n c).
Proof.
  apply WF_make_WF.
Qed.

Lemma WF_Zero : forall m n : nat, WF_Matrix (@Zero m n).
Proof. intros m n. unfold WF_Matrix. reflexivity. Qed.

Lemma WF_Zero_alt : forall m n o p : nat, 
  @WF_Matrix m n (@Zero o p).
Proof. intros m n. unfold WF_Matrix. reflexivity. Qed.

Lemma WF_I : forall n : nat, WF_Matrix (I n). 
Proof. 
  unfold WF_Matrix, I. intros n x y H. simpl.
  destruct H; bdestruct (x =? y); bdestruct (x <? n); trivial; lia.
Qed.

Lemma WF_I1 : WF_Matrix (I 1). Proof. apply WF_I. Qed.

Lemma WF_e_i : forall {n : nat} (i : nat),
  WF_Matrix (@e_i n i).
Proof. unfold WF_Matrix, e_i.
       intros; destruct H as [H | H].
       bdestruct (x =? i); bdestruct (x <? n); bdestruct (y =? 0); try lia; easy.
       bdestruct (x =? i); bdestruct (x <? n); bdestruct (y =? 0); try lia; easy.
Qed.

Lemma WF_scale : forall {m n : nat} (r : C) (A : Matrix m n), 
  WF_Matrix A -> WF_Matrix (scale r A).
Proof.
  unfold WF_Matrix, scale.
  intros m n r A H x y H0. simpl.
  rewrite H; trivial.
  rewrite Cmult_0_r.
  reflexivity.
Qed.

Lemma WF_plus : forall {m n} (A B : Matrix m n), 
  WF_Matrix A -> WF_Matrix B -> WF_Matrix (A .+ B).
Proof.
  unfold WF_Matrix, Mplus.
  intros m n A B H H0 x y H1. simpl.
  rewrite H, H0; trivial.
  rewrite Cplus_0_l.
  reflexivity.
Qed.

Lemma WF_mult : forall {m n o : nat} (A : Matrix m n) (B : Matrix n o), 
  WF_Matrix A -> WF_Matrix B -> WF_Matrix (A × B).
Proof.
  unfold WF_Matrix, Mmult.
  intros m n o A B H H0 x y D. 
  apply (@big_sum_0 C C_is_monoid).
  destruct D; intros z.
  + rewrite H; [lca | auto].
  + rewrite H0; [lca | auto].
Qed.

Lemma WF_kron : forall {m n o p q r : nat} (A : Matrix m n) (B : Matrix o p), 
                  q = m * o -> r = n * p -> 
                  WF_Matrix A -> WF_Matrix B -> @WF_Matrix q r (A ⊗ B).
Proof.
  unfold WF_Matrix, kron.
  intros m n o p q r A B Nn No H H0 x y H1. subst.
  bdestruct (o =? 0). rewrite H0; [lca|lia]. 
  bdestruct (p =? 0). rewrite H0; [lca|lia]. 
  rewrite H.
  rewrite Cmult_0_l; reflexivity.
  destruct H1.
  unfold ge in *.
  left. 
  apply Nat.div_le_lower_bound; trivial.
  rewrite Nat.mul_comm.
  assumption.
  right.
  apply Nat.div_le_lower_bound; trivial.
  rewrite Nat.mul_comm.
  assumption.
Qed. 

Lemma WF_direct_sum : forall {m n o p q r : nat} (A : Matrix m n) (B : Matrix o p), 
                  q = m + o -> r = n + p -> 
                  WF_Matrix A -> WF_Matrix B -> @WF_Matrix q r (A .⊕ B).
Proof. 
  unfold WF_Matrix, direct_sum. 
  intros; subst.
  destruct H3; bdestruct_all; simpl; try apply H1; try apply H2. 
  all : lia.
Qed.

Lemma WF_transpose : forall {m n : nat} (A : Matrix m n), 
                     WF_Matrix A -> WF_Matrix A⊤. 
Proof. unfold WF_Matrix, transpose. intros m n A H x y H0. apply H. 
       destruct H0; auto. Qed.

Lemma WF_adjoint : forall {m n : nat} (A : Matrix m n), 
      WF_Matrix A -> WF_Matrix A†. 
Proof. unfold WF_Matrix, adjoint, Cconj. intros m n A H x y H0. simpl. 
rewrite H. lca. lia. Qed.

Lemma WF_outer_product : forall {n} (u v : Vector n),
    WF_Matrix u ->
    WF_Matrix v ->
    WF_Matrix (outer_product u v).
Proof. intros. apply WF_mult; [|apply WF_adjoint]; assumption. Qed.

Lemma WF_kron_n : forall n {m1 m2} (A : Matrix m1 m2),
   WF_Matrix A ->  WF_Matrix (kron_n n A).
Proof.
  intros.
  induction n; simpl.
  - apply WF_I.
  - apply WF_kron; try lia; assumption. 
Qed.

Lemma WF_big_kron : forall n m (l : list (Matrix m n)) (A : Matrix m n), 
                        (forall i, WF_Matrix (nth i l A)) ->
                         WF_Matrix (⨂ l). 
Proof.                         
  intros n m l A H.
  induction l.
  - simpl. apply WF_I.
  - simpl. apply WF_kron; trivial. apply (H O).
    apply IHl. intros i. apply (H (S i)).
Qed.

(* alternate version that uses In instead of nth *)
Lemma WF_big_kron' : forall n m (l : list (Matrix m n)), 
                        (forall A, In A l -> WF_Matrix A) ->
                         WF_Matrix (⨂ l). 
Proof.                         
  intros n m l H. 
  induction l.
  - simpl. apply WF_I.
  - simpl. apply WF_kron; trivial. apply H; left; easy. 
    apply IHl. intros A' H0. apply H; right; easy.
Qed.

Lemma WF_Mmult_n : forall n {m} (A : Square m),
   WF_Matrix A -> WF_Matrix (Mmult_n n A).
Proof.
  intros.
  induction n; simpl.
  - apply WF_I.
  - apply WF_mult; assumption. 
Qed.

Lemma WF_direct_sum_n : forall n {m1 m2} (A : Matrix m1 m2),
   WF_Matrix A -> WF_Matrix (direct_sum_n n A).
Proof.
  intros.
  induction n; simpl.
  - apply WF_Zero.
  - apply WF_direct_sum; try lia; assumption. 
Qed.

Lemma WF_Msum : forall d1 d2 n (f : nat -> Matrix d1 d2), 
  (forall i, (i < n)%nat -> WF_Matrix (f i)) -> 
  WF_Matrix (big_sum f n).
Proof.
  intros. 
  apply big_sum_prop_distr; intros. 
  apply WF_plus; auto.
  apply WF_Zero.
  auto. 
Qed.

Local Close Scope nat_scope.


(** * Tactics for showing well-formedness *)


Local Open Scope nat.
Local Open Scope R.
Local Open Scope C.

(* Much less awful *)
Ltac show_wf := 
  unfold WF_Matrix;
  let x := fresh "x" in
  let y := fresh "y" in
  let H := fresh "H" in
  intros x y [H | H];
  apply le_plus_minus' in H; rewrite H;
  cbv;
  destruct_m_eq;
  try lca.

(* Create HintDb wf_db. *)
#[export] Hint Resolve WF_Zero WF_Zero_alt WF_const_matrix WF_I WF_I1 WF_e_i 
  WF_mult WF_plus  WF_scale WF_transpose WF_adjoint WF_outer_product 
  WF_big_kron WF_kron_n WF_kron WF_Mmult_n WF_make_WF WF_Msum 
  WF_direct_sum WF_direct_sum_n : wf_db.
#[export] Hint Extern 2 (_ = _) => unify_pows_two : wf_db.

(* Utility tactics *)
Ltac has_hyp P :=
  match goal with
    | [ _ : P |- _ ] => idtac
  end.

Ltac no_hyp P :=
  match goal with
    | [ _ : P |- _ ] => fail 1
    | _             => idtac
  end.

(* staggered, because it seems to speed things up (it shouldn't) *)
Ltac auto_wf :=
  try match goal with
      |- WF_Matrix _ => auto with wf_db;
                      auto 10 with wf_db;
                      auto 20 with wf_db;
                      auto 40 with wf_db;
                      auto 80 with wf_db;
                      auto 160 with wf_db
      end.

(* Puts all well-formedness conditions for M into the context *)
Ltac collate_wf' M :=
  match M with
  (* already in context *)
  | ?A        => has_hyp (WF_Matrix A)
  (* recursive case *)
  | ?op ?A ?B => collate_wf' A;
                collate_wf' B;
                assert (WF_Matrix (op A B)) by auto with wf_db
  (* base case *)
  | ?A =>        assert (WF_Matrix A) by auto with wf_db
  (* not a matrix *)
  | _         => idtac
  end.
  
(* Aggregates well-formedness conditions for context *)
Ltac collate_wf :=
  match goal with
  | |- ?A = ?B      => collate_wf' A; collate_wf' B
  | |- ?A == ?B     => collate_wf' A; collate_wf' B
  | |- WF_Matrix ?A => collate_wf' A
  | |- context[?A]  => collate_wf' A 
  end.

Ltac solve_wf := collate_wf; easy. 

(** * Basic matrix lemmas *)

Lemma make_WF_equiv n m (A : Matrix n m) : 
  make_WF A ≡ A.
Proof.
  unfold make_WF.
  intros i j Hi Hj.
  bdestructΩ'.
Qed.

Lemma mat_equiv_make_WF : forall {m n} (T : Matrix m n),
  T == make_WF T.
Proof. unfold make_WF, mat_equiv; intros. 
       bdestruct (i <? m); bdestruct (j <? n); try lia; easy.
Qed.

Lemma eq_make_WF : forall {n m} (T : Matrix m n),
  WF_Matrix T -> T = make_WF T.
Proof. intros. 
       apply mat_equiv_eq; auto with wf_db.
       apply mat_equiv_make_WF.
Qed.

Lemma Mplus_make_WF : forall {n m} (A B : Matrix m n),
  make_WF A .+ make_WF B = make_WF (A .+ B).
Proof. intros. 
       apply mat_equiv_eq; auto with wf_db.
       unfold mat_equiv; intros. 
       unfold make_WF, Mplus.
       bdestruct (i <? m); bdestruct (j <? n); try lia; simpl. 
       easy.
Qed.
  
Lemma Mmult_make_WF : forall {m n o} (A : Matrix m n) (B : Matrix n o),
  make_WF A × make_WF B = make_WF (A × B).
Proof. intros. 
       apply mat_equiv_eq; auto with wf_db.
       unfold mat_equiv; intros. 
       unfold make_WF, Mmult.
       bdestruct (i <? m); bdestruct (j <? o); try lia; simpl. 
       apply big_sum_eq_bounded; intros. 
       bdestruct (x <? n); try lia; easy. 
Qed.

Lemma WF0_Zero_l :forall (n : nat) (A : Matrix 0%nat n), WF_Matrix A -> A = Zero.
Proof.
  intros n A WFA.
  prep_matrix_equality.
  rewrite WFA.
  reflexivity.
  lia.
Qed.

Lemma WF0_Zero_r :forall (n : nat) (A : Matrix n 0%nat), WF_Matrix A -> A = Zero.
Proof.
  intros n A WFA.
  prep_matrix_equality.
  rewrite WFA.
  reflexivity.
  lia.
Qed.

Lemma WF0_Zero :forall (A : Matrix 0%nat 0%nat), WF_Matrix A -> A = Zero.
Proof.
  apply WF0_Zero_l.
Qed.

Lemma I0_Zero : I 0 = Zero.
Proof.
  apply WF0_Zero.
  apply WF_I.
Qed.

Lemma trace_plus_dist : forall (n : nat) (A B : Square n), 
    trace (A .+ B) = (trace A + trace B)%C. 
Proof. 
  intros.
  unfold trace, Mplus.
  rewrite (@big_sum_plus C _ _ C_is_comm_group). 
  easy.  
Qed.

Lemma trace_mult_dist : forall n p (A : Square n), trace (p .* A) = (p * trace A)%C. 
Proof.
  intros.
  unfold trace, scale.
  rewrite (@big_sum_mult_l C _ _ _ C_is_ring). 
  easy.
Qed.

Lemma trace_0_l : forall (A : Square 0), 
  trace A = 0.
Proof.
  intros A.
  unfold trace. 
  easy.
Qed.

Lemma trace_0_r : forall n, 
  trace (@Zero n n) = 0.
Proof.
  intros A.
  unfold trace.
  rewrite big_sum_0; easy.
Qed.

Lemma trace_mmult_eq_ptwise : forall {n m} (A : Matrix n m) (B : Matrix m n),
  trace (A×B) = Σ (fun i => Σ (fun j => A i j * B j i) m) n.
Proof.
  reflexivity.
Qed.

Lemma trace_mmult_comm : forall {n m} (A : Matrix n m) (B : Matrix m n),
  trace (A×B) = trace (B×A).
Proof.
  intros n m A B.
  rewrite 2!trace_mmult_eq_ptwise.
  rewrite big_sum_swap_order.
  do 2 (apply big_sum_eq_bounded; intros).
  apply Cmult_comm.
Qed.

Lemma trace_transpose : forall {n} (A : Square n),
  trace (A ⊤) = trace A.
Proof.
  reflexivity.
Qed.

Lemma trace_kron : forall {n p} (A : Square n) (B : Square p),
  trace (A ⊗ B) = trace A * trace B.
Proof.
  intros n p A B.
  destruct p;
  [rewrite Nat.mul_0_r, 2!trace_0_l; lca|].
  unfold trace.
  simpl_rewrite big_sum_product; [|easy].
  reflexivity.
Qed.

Lemma trace_big_sum : forall n k f,
  trace (big_sum (G:=Square n) f k) = Σ (fun x => trace (f x)) k.
Proof.
  intros n k f.
  induction k.
  - rewrite trace_0_r; easy.
  - rewrite <- 2!big_sum_extend_r, <-IHk.
    simpl. 
    rewrite trace_plus_dist.
    easy.
Qed.

Lemma Mplus_0_l : forall (m n : nat) (A : Matrix m n), Zero .+ A = A.
Proof. intros. lma. Qed.

Lemma Mplus_0_r : forall (m n : nat) (A : Matrix m n), A .+ Zero = A.
Proof. intros. lma. Qed.
    
Lemma Mmult_0_l : forall (m n o : nat) (A : Matrix n o), @Zero m n × A = Zero.
Proof.
  intros m n o A. 
  unfold Mmult, Zero.
  prep_matrix_equality.
  apply (@big_sum_0 C C_is_monoid).
  intros.
  lca. 
Qed.

Lemma Mmult_0_r : forall (m n o : nat) (A : Matrix m n), A × @Zero n o = Zero.
Proof.
  intros m n o A. 
  unfold Zero, Mmult.
  prep_matrix_equality.
  apply (@big_sum_0 C C_is_monoid).
  intros.
  lca. 
Qed.

(* using <= because our form big_sum is exclusive. *)
Lemma Mmult_1_l_gen: forall (m n : nat) (A : Matrix m n) (x z k : nat), 
  (k <= m)%nat ->
  ((k <= x)%nat -> big_sum (fun y : nat => I m x y * A y z) k = 0) /\
  ((k > x)%nat -> big_sum (fun y : nat => I m x y * A y z) k = A x z).
Proof.  
  intros m n A x z k B.
  induction k.
  * simpl. split. reflexivity. lia.
  * destruct IHk as [IHl IHr]. lia.  
    split.
    + intros leSkx.
      simpl.
      unfold I.
      bdestruct (x =? k); try lia.
      autorewrite with C_db.
      apply IHl.
      lia.
    + intros gtSkx.
      simpl in *.
      unfold I in *.
      bdestruct (x =? k); bdestruct (x <? m); subst; try lia.
      rewrite IHl by lia; simpl; lca.
      rewrite IHr by lia; simpl; lca.
Qed.

Lemma Mmult_1_l_mat_eq : forall (m n : nat) (A : Matrix m n), I m × A == A.
Proof.
  intros m n A i j Hi Hj.
  unfold Mmult.
  edestruct (@Mmult_1_l_gen m n) as [Hl Hr].
  apply Nat.le_refl.
  unfold get.
  apply Hr.
  simpl in *.
  lia.
Qed.  

Lemma Mmult_1_l: forall (m n : nat) (A : Matrix m n), 
  WF_Matrix A -> I m × A = A.
Proof.
  intros m n A H.
  apply mat_equiv_eq; trivial.
  auto with wf_db.
  apply Mmult_1_l_mat_eq.
Qed.

Lemma Mmult_1_r_gen: forall (m n : nat) (A : Matrix m n) (x z k : nat), 
  (k <= n)%nat ->
  ((k <= z)%nat -> big_sum (fun y : nat => A x y * (I n) y z) k = 0) /\
  ((k > z)%nat -> big_sum (fun y : nat => A x y * (I n) y z) k = A x z).
Proof.  
  intros m n A x z k B.
  induction k.
  simpl. split. reflexivity. lia.
  destruct IHk as [IHl IHr].
  lia.
  split.
  + intros leSkz.
    simpl in *.
    unfold I.
    bdestruct (k =? z); try lia.
    autorewrite with C_db.
    apply IHl; lia.
  + intros gtSkz.
    simpl in *.
    unfold I in *.
    bdestruct (k =? z); subst.
    - bdestruct (z <? n); try lia.
      rewrite IHl by lia; lca.
    - rewrite IHr by lia; simpl; lca.
Qed.

Lemma Mmult_1_r_mat_eq : forall (m n : nat) (A : Matrix m n), A × I n ≡ A.
Proof.
  intros m n A i j Hi Hj.
  unfold Mmult.
  edestruct (@Mmult_1_r_gen m n) as [Hl Hr].
  apply Nat.le_refl.
  unfold get; simpl.
  apply Hr.
  lia.
Qed.  

Lemma Mmult_1_r: forall (m n : nat) (A : Matrix m n), 
  WF_Matrix A -> A × I n = A.
Proof.
  intros m n A H.
  apply mat_equiv_eq; trivial.
  auto with wf_db.
  apply Mmult_1_r_mat_eq.
Qed.

Lemma Mmult_1_comm {n m} (A : Matrix n m) (HA : WF_Matrix A) : 
  I n × A = A × I m.
Proof.
  now rewrite Mmult_1_r, Mmult_1_l.
Qed.

(* Cool facts about I∞, not used in the development *) 
Lemma Mmult_inf_l : forall(m n : nat) (A : Matrix m n),
  WF_Matrix A -> I∞ × A = A.
Proof. 
  intros m n A H.
  prep_matrix_equality.
  unfold Mmult.
  edestruct (@Mmult_1_l_gen m n) as [Hl Hr].
  apply Nat.le_refl.
  bdestruct (m <=? x).
  rewrite H by auto.
  apply (@big_sum_0_bounded C C_is_monoid).
  intros z L. 
  unfold I__inf, I.
  bdestruct (x =? z). lia. lca.  
  unfold I__inf, I in *.
  erewrite big_sum_eq.
  apply Hr.
  assumption.
  bdestruct (x <? m); [|lia]. 
  apply functional_extensionality. intros. rewrite andb_true_r. reflexivity.
Qed.

Lemma Mmult_inf_r : forall(m n : nat) (A : Matrix m n),
  WF_Matrix A -> A × I∞ = A.
Proof. 
  intros m n A H.
  prep_matrix_equality.
  unfold Mmult.
  edestruct (@Mmult_1_r_gen m n) as [Hl Hr].
  apply Nat.le_refl.
  bdestruct (n <=? y).
  rewrite H by auto.
  apply (@big_sum_0_bounded C C_is_monoid).
  intros z L. 
  unfold I__inf, I.
  bdestruct (z =? y). lia. lca.  
  unfold I__inf, I in *.
  erewrite big_sum_eq.
  apply Hr.
  assumption.
  apply functional_extensionality. intros z. 
  bdestruct (z =? y); bdestruct (z <? n); simpl; try lca; try lia. 
Qed.

Lemma Mplus_const {m n} c d : 
  @const_matrix m n c .+ const_matrix d = const_matrix (c + d).
Proof.
  prep_matrix_equivalence.
  unfold const_matrix.
  rewrite !make_WF_equiv.
  by_cell; reflexivity.
Qed.

Lemma kron_const {m n o p} c d : 
  @const_matrix m n c ⊗ @const_matrix o p d = 
  const_matrix (c * d).
Proof.
  prep_matrix_equivalence.
  unfold const_matrix.
  rewrite !make_WF_equiv.
  by_cell; reflexivity.
Qed.

Lemma Mmult_const {m n o} c d :
  @const_matrix m n c × @const_matrix n o d =
  const_matrix (c * d * INR n).
Proof.
  prep_matrix_equivalence.
  unfold const_matrix.
  rewrite !make_WF_equiv.
  intros i j Hi Hj.
  unfold Mmult.
  now rewrite big_sum_constant, times_n_C.
Qed.

Lemma kron_0_l : forall (m n o p : nat) (A : Matrix o p), 
  @Zero m n ⊗ A = Zero.
Proof.
  intros m n o p A.
  prep_matrix_equality.
  unfold Zero, kron.
  rewrite Cmult_0_l.
  reflexivity.
Qed.

Lemma kron_0_r : forall (m n o p : nat) (A : Matrix m n), 
   A ⊗ @Zero o p = Zero.
Proof.
  intros m n o p A.
  prep_matrix_equality.
  unfold Zero, kron.
  rewrite Cmult_0_r.
  reflexivity.
Qed.

Lemma kron_1_r : forall (m n : nat) (A : Matrix m n), A ⊗ I 1 = A.
Proof.
  intros m n A.
  prep_matrix_equality.
  unfold I, kron.
  rewrite 2 Nat.div_1_r.
  rewrite 2 Nat.mod_1_r.
  simpl.
  autorewrite with C_db.
  reflexivity.
Qed.

Lemma kron_1_r_mat_equiv : forall {n m} (A : Matrix n m),
  A ⊗ Matrix.I 1 ≡ A.
Proof.
  intros; now rewrite kron_1_r.
Qed.

Lemma kron_1_l_mat_equiv : forall {n m} (A : Matrix n m),
  Matrix.I 1 ⊗ A ≡ A.
Proof.
  intros n m A.
  intros i j Hi Hj.
  unfold kron, I.
  rewrite 2!Nat.div_small, 2!Nat.mod_small by lia.
  rewrite Cmult_1_l.
  easy.
Qed.

(* This side is more limited *)
Lemma kron_1_l : forall (m n : nat) (A : Matrix m n), 
  WF_Matrix A -> I 1 ⊗ A = A.
Proof.
  intros m n A WF.
  apply mat_equiv_eq; 
    [auto using WF_Matrix_dim_change with wf_db..|].
  apply kron_1_l_mat_equiv.
Qed.

Lemma kron_1_1_mid_comm {n m} (A : Matrix n 1) (B : Matrix 1 m) 
  (HA : WF_Matrix A) (HB : WF_Matrix B) : 
  A ⊗ B = B ⊗ A.
Proof.
  apply mat_equiv_eq; [auto with wf_db..|].
  intros i j.
  unfold kron.
  intros Hi Hj.
  rewrite !Nat.mod_1_r, !Nat.div_1_r, 
    !Nat.mod_small, !Nat.div_small by lia.
  lca.
Qed.

Lemma kron_2_0_mid_comm {n m} (A : Matrix n (2 ^ 0)) (B : Matrix (2 ^ 0) m) 
  (HA : WF_Matrix A) (HB : WF_Matrix B) : 
  A ⊗ B = B ⊗ A.
Proof.
  now apply kron_1_1_mid_comm.
Qed.  

Theorem transpose_involutive : forall (m n : nat) (A : Matrix m n), (A⊤)⊤ = A.
Proof. reflexivity. Qed.

Theorem adjoint_involutive : forall (m n : nat) (A : Matrix m n), A†† = A.
Proof. intros. lma. Qed.  

Lemma transpose_matrices : forall {n m} (A B : Matrix n m),
	A ⊤ = B ⊤ -> A = B.
Proof.
	intros.
	rewrite <- transpose_involutive.
	rewrite <- H.
	rewrite transpose_involutive.
	easy.
Qed.

Lemma adjoint_matrices : forall {n m} (A B : Matrix n m),
	A † = B † -> A = B.
Proof.
	intros.
	rewrite <- adjoint_involutive.
	rewrite <- H.
	rewrite adjoint_involutive.
	easy.
Qed.

Lemma id_transpose_eq : forall n, (I n)⊤ = (I n).
Proof.
  intros n. unfold transpose, I.
  prep_matrix_equality.
  bdestruct (y =? x); bdestruct (x =? y); bdestruct (y <? n); bdestruct (x <? n);
    trivial; lia.
Qed.

Lemma zero_transpose_eq : forall m n, (@Zero m n)⊤ = @Zero n m.
Proof. reflexivity. Qed.

Lemma id_adjoint_eq : forall n, (I n)† = (I n).
Proof.
  intros n.
  unfold adjoint, I.
  prep_matrix_equality.
  bdestruct (y =? x); bdestruct (x =? y); bdestruct (y <? n); bdestruct (x <? n);
    try lia; lca.
Qed.

Lemma zero_adjoint_eq : forall m n, (@Zero m n)† = @Zero n m.
Proof. unfold adjoint, Zero. rewrite Cconj_0. reflexivity. Qed.

Theorem Mplus_comm : forall (m n : nat) (A B : Matrix m n), A .+ B = B .+ A.
Proof.
  unfold Mplus. 
  intros m n A B.
  prep_matrix_equality.
  apply Cplus_comm.
Qed.

Theorem Mplus_assoc : forall (m n : nat) (A B C : Matrix m n), A .+ B .+ C = A .+ (B .+ C).
Proof.
  unfold Mplus. 
  intros m n A B C.
  prep_matrix_equality.
  rewrite Cplus_assoc.
  reflexivity.
Qed.


Theorem Mmult_assoc : forall {m n o p : nat} (A : Matrix m n) (B : Matrix n o) 
  (C: Matrix o p), A × B × C = A × (B × C).
Proof.
  intros m n o p A B C.
  unfold Mmult.
  prep_matrix_equality.
  induction n.
  + simpl.
    clear B.
    induction o. reflexivity.
    simpl. rewrite IHo. lca.
  + simpl. 
    rewrite <- IHn.
    simpl.
    rewrite (@big_sum_mult_l Complex.C _ _ _ C_is_ring).
    rewrite <- (@big_sum_plus Complex.C _ _ C_is_comm_group).
    apply big_sum_eq.
    apply functional_extensionality. intros z.
    rewrite Cmult_plus_distr_r.
    rewrite Cmult_assoc.
    reflexivity.
Qed.

Lemma Mmult_plus_distr_l : forall (m n o : nat) (A : Matrix m n) (B C : Matrix n o), 
                           A × (B .+ C) = A × B .+ A × C.
Proof. 
  intros m n o A B C.
  unfold Mplus, Mmult.
  prep_matrix_equality.
  rewrite <- (@big_sum_plus Complex.C _ _ C_is_comm_group).
  apply big_sum_eq.
  apply functional_extensionality. intros z.
  rewrite Cmult_plus_distr_l. 
  reflexivity.
Qed.

Lemma Mmult_plus_distr_r : forall (m n o : nat) (A B : Matrix m n) (C : Matrix n o), 
                           (A .+ B) × C = A × C .+ B × C.
Proof. 
  intros m n o A B C.
  unfold Mplus, Mmult.
  prep_matrix_equality.
  rewrite <- (@big_sum_plus Complex.C _ _ C_is_comm_group).
  apply big_sum_eq.
  apply functional_extensionality. intros z.
  rewrite Cmult_plus_distr_r. 
  reflexivity.
Qed.

Lemma kron_plus_distr_l : forall (m n o p : nat) (A : Matrix m n) (B C : Matrix o p), 
                           A ⊗ (B .+ C) = A ⊗ B .+ A ⊗ C.
Proof. 
  intros m n o p A B C.
  unfold Mplus, kron.
  prep_matrix_equality.
  rewrite Cmult_plus_distr_l.
  easy.
Qed.

Lemma kron_plus_distr_r : forall (m n o p : nat) (A B : Matrix m n) (C : Matrix o p), 
                           (A .+ B) ⊗ C = A ⊗ C .+ B ⊗ C.
Proof. 
  intros m n o p A B C.
  unfold Mplus, kron.
  prep_matrix_equality.
  rewrite Cmult_plus_distr_r. 
  reflexivity.
Qed.

Lemma Mscale_0_l : forall (m n : nat) (A : Matrix m n), C0 .* A = Zero.
Proof.
  intros m n A.
  prep_matrix_equality.
  unfold Zero, scale.
  rewrite Cmult_0_l.
  reflexivity.
Qed.

Lemma Mscale_0_r : forall (m n : nat) (c : C), c .* @Zero m n = Zero.
Proof.
  intros m n c.
  prep_matrix_equality.
  unfold Zero, scale.
  rewrite Cmult_0_r.
  reflexivity.
Qed.

Lemma Mscale_1_l : forall (m n : nat) (A : Matrix m n), C1 .* A = A.
Proof.
  intros m n A.
  prep_matrix_equality.
  unfold scale.
  rewrite Cmult_1_l.
  reflexivity.
Qed.

Lemma Mscale_1_r : forall (n : nat) (c : C),
    c .* I n = fun x y => if (x =? y) && (x <? n) then c else C0.
Proof.
  intros n c.
  prep_matrix_equality.
  unfold scale, I.
  destruct ((x =? y) && (x <? n)).
  rewrite Cmult_1_r; reflexivity.
  rewrite Cmult_0_r; reflexivity.
Qed.

Lemma Mscale_assoc : forall (m n : nat) (x y : C) (A : Matrix m n),
  x .* (y .* A) = (x * y) .* A.
Proof.
  intros. unfold scale. prep_matrix_equality.
  rewrite Cmult_assoc; reflexivity.
Qed.

Lemma Mscale_div : forall {n m} (c : C) (A B : Matrix n m),
  c <> C0 -> c .* A = c .* B -> A = B.
Proof. intros. 
       rewrite <- Mscale_1_l. rewrite <- (Mscale_1_l n m A).
       rewrite <- (Cinv_l c).
       rewrite <- Mscale_assoc.
       rewrite H0. 
       lma.
       apply H.
Qed.

Lemma Mscale_inv : forall {n m} (A B : Matrix n m) c, 
  c <> C0 -> c .* A = B <-> A = (/ c) .* B.
Proof.
  intros.
  split; intro H0; [rewrite <- H0 | rewrite H0];
  rewrite Mscale_assoc.
  - rewrite Cinv_l; [ lma | assumption].  
  - rewrite Cinv_r; [ lma | assumption].  
Qed.

Lemma Mscale_plus_distr_l : forall (m n : nat) (x y : C) (A : Matrix m n),
  (x + y) .* A = x .* A .+ y .* A.
Proof.
  intros. unfold Mplus, scale. prep_matrix_equality. apply Cmult_plus_distr_r.
Qed.

Lemma Mscale_plus_distr_r : forall (m n : nat) (x : C) (A B : Matrix m n),
  x .* (A .+ B) = x .* A .+ x .* B.
Proof.
  intros. unfold Mplus, scale. prep_matrix_equality. apply Cmult_plus_distr_l.
Qed.

Lemma Mscale_mult_dist_l : forall (m n o : nat) (x : C) (A : Matrix m n) (B : Matrix n o), 
    ((x .* A) × B) = x .* (A × B).
Proof.
  intros m n o x A B.
  unfold scale, Mmult.
  prep_matrix_equality.
  rewrite (@big_sum_mult_l C _ _ _ C_is_ring). 
  apply big_sum_eq.
  apply functional_extensionality. intros z.
  rewrite Cmult_assoc.
  reflexivity.
Qed.

Lemma Mscale_mult_dist_r : forall (m n o : nat) (x : C) (A : Matrix m n) (B : Matrix n o),
    (A × (x .* B)) = x .* (A × B).
Proof.
  intros m n o x A B.
  unfold scale, Mmult.
  prep_matrix_equality.
  rewrite (@big_sum_mult_l C _ _ _ C_is_ring). 
  apply big_sum_eq.
  apply functional_extensionality. intros z.
  repeat rewrite Cmult_assoc.
  rewrite (Cmult_comm _ x).
  reflexivity.
Qed.

Lemma Mscale_kron_dist_l : forall (m n o p : nat) (x : C) (A : Matrix m n) (B : Matrix o p), 
    ((x .* A) ⊗ B) = x .* (A ⊗ B).
Proof.
  intros m n o p x A B.
  unfold scale, kron.
  prep_matrix_equality.
  rewrite Cmult_assoc.
  reflexivity.
Qed.

Lemma Mscale_kron_dist_r : forall (m n o p : nat) (x : C) (A : Matrix m n) (B : Matrix o p), 
    (A ⊗ (x .* B)) = x .* (A ⊗ B).
Proof.
  intros m n o p x A B.
  unfold scale, kron.
  prep_matrix_equality.
  rewrite Cmult_assoc.  
  rewrite (Cmult_comm (A _ _) x).
  rewrite Cmult_assoc.  
  reflexivity.
Qed.

Lemma Mscale_trans : forall (m n : nat) (x : C) (A : Matrix m n),
    (x .* A)⊤ = x .* A⊤.
Proof. reflexivity. Qed.

Lemma Mscale_adj : forall (m n : nat) (x : C) (A : Matrix m n),
    (x .* A)† = x^* .* A†.
Proof.
  intros m n x A.
  unfold scale, adjoint.
  prep_matrix_equality.
  rewrite Cconj_mult_distr.          
  reflexivity.
Qed.

Lemma Mplus_transpose : forall (m n : nat) (A : Matrix m n) (B : Matrix m n),
  (A .+ B)⊤ = A⊤ .+ B⊤.
Proof. reflexivity. Qed.

Lemma Mmult_transpose : forall (m n o : nat) (A : Matrix m n) (B : Matrix n o),
      (A × B)⊤ = B⊤ × A⊤.
Proof.
  intros m n o A B.
  unfold Mmult, transpose.
  prep_matrix_equality.
  apply big_sum_eq.  
  apply functional_extensionality. intros z.
  rewrite Cmult_comm.
  reflexivity.
Qed.

Lemma kron_transpose : forall (m n o p : nat) (A : Matrix m n) (B : Matrix o p ),
  (A ⊗ B)⊤ = A⊤ ⊗ B⊤.
Proof. reflexivity. Qed.

Lemma kron_transpose' [m n o p] (A : Matrix m n) (B : Matrix o p) :
  forall mo' mp',
  @Matrix.transpose mo' mp' (A ⊗ B) = 
  (@Matrix.transpose m n A) ⊗ (@Matrix.transpose o p B).
Proof. reflexivity. Qed.

Lemma Mplus_adjoint : forall (m n : nat) (A : Matrix m n) (B : Matrix m n),
  (A .+ B)† = A† .+ B†.
Proof.  
  intros m n A B.
  unfold Mplus, adjoint.
  prep_matrix_equality.
  rewrite Cconj_plus_distr.
  reflexivity.
Qed.

Lemma Mmult_adjoint : forall {m n o : nat} (A : Matrix m n) (B : Matrix n o),
      (A × B)† = B† × A†.
Proof.
  intros m n o A B.
  unfold Mmult, adjoint.
  prep_matrix_equality.
  rewrite (@big_sum_func_distr C C _ C_is_group _ C_is_group). (* not great *) 
  apply big_sum_eq.  
  apply functional_extensionality. intros z.
  rewrite Cconj_mult_distr.
  rewrite Cmult_comm.
  reflexivity.
  intros; lca. 
Qed.

Lemma direct_sum_adjoint : forall {m n o p : nat} 
  (A : Matrix m n) (B : Matrix o p),
  (A .⊕ B) † = A † .⊕ B †.
Proof.
  intros m n o p A B.
  prep_matrix_equality.
  unfold adjoint, direct_sum.
  bdestructΩ'.
Qed.

Lemma direct_sum_Mmult {m n o p q r} (A : Matrix m n) (B : Matrix n o)
  (C : Matrix p q) (D : Matrix q r) : WF_Matrix A -> WF_Matrix B ->
  WF_Matrix C -> WF_Matrix D ->
  (A × B) .⊕ (C × D) = (A .⊕ C) × (B .⊕ D).
Proof.
  intros HA HB HC HD.
  assert (HAB : WF_Matrix (A × B)) by auto_wf.
  assert (HCD : WF_Matrix (C × D)) by auto_wf.
  prep_matrix_equivalence.
  intros i j Hi Hj.
  unfold direct_sum.
  bdestruct (i <? m); bdestruct (j <? o).
  - simpl.
    symmetry.
    unfold Mmult.
    do 2 simplify_bools_lia_one_kernel.
    erewrite big_sum_eq_bounded.
    2:{
      intros k Hk.
      simpl_bools.
      instantiate (1 := fun k => if k <? n then A i k * B k j else C0).
      simpl.
      bdestructΩ'.
      rewrite HA by lia.
      lca.
    }
    rewrite big_sum_sum.
    simpl.
    rewrite Cplus_comm.
    rewrite big_sum_0_bounded by (intros; bdestructΩ').
    Csimpl.
    apply big_sum_eq_bounded; intros; bdestructΩ'.
  - simpl.
    rewrite HAB by lia.
    symmetry; unfold Mmult.
    rewrite big_sum_0_bounded; [easy|].
    intros k Hk.
    rewrite HB by lia.
    simplify_bools_lia_one_kernel.
    simplify_bools_lia_one_kernel.
    bdestructΩ'; [lca|].
    rewrite HA by lia; lca.
  - simpl.
    rewrite HAB by lia.
    symmetry; unfold Mmult.
    rewrite big_sum_0_bounded; [easy|].
    intros k Hk.
    rewrite HA by lia.
    simplify_bools_lia_one_kernel.
    simplify_bools_lia_one_kernel.
    bdestructΩ'; [lca|].
    rewrite HB by lia; lca.
  - simpl.
    symmetry.
    unfold Mmult.
    do 2 simplify_bools_lia_one_kernel.
    erewrite big_sum_eq_bounded.
    2:{
      intros k Hk.
      simpl_bools.
      instantiate (1 := fun k => if k <? n then C0 else 
      (C (i - m)%nat (k - n)%nat * D (k - n)%nat (j - o)%nat)).
      bdestructΩ'.
      rewrite HA by lia.
      lca.
    }
    rewrite big_sum_sum.
    rewrite big_sum_0_bounded by (intros; bdestructΩ').
    simpl.
    Csimpl.
    apply big_sum_eq_bounded.
    intros k Hk.
    simplify_bools_lia_one_kernel.
    now rewrite add_sub'.
Qed.

Lemma direct_sum_id : forall n m,
  I n .⊕ I m = I (n + m).
Proof.
  intros n m.
  prep_matrix_equivalence.
  unfold I, direct_sum.
  intros i j Hi Hj.
  simplify_bools_lia_one_kernel.
  bdestructΩ'.
Qed.

Lemma kron_adjoint : forall {m n o p : nat} (A : Matrix m n) (B : Matrix o p),
  (A ⊗ B)† = A† ⊗ B†.
Proof. 
  intros. unfold adjoint, kron. 
  prep_matrix_equality.
  rewrite Cconj_mult_distr.
  reflexivity.
Qed.

Lemma id_kron : forall (m n : nat),  I m ⊗ I n = I (m * n).
Proof.
  intros.
  unfold I, kron.
  prep_matrix_equality.
  bdestruct (x =? y); rename H into Eq; subst.
  + repeat rewrite Nat.eqb_refl; simpl.
    destruct n.
    - simpl.
      rewrite Nat.mul_0_r.
      bdestruct (y <? 0); try lia.
      autorewrite with C_db; reflexivity.
    - bdestruct (y mod S n <? S n). 
      2: specialize (Nat.mod_upper_bound y (S n)); intros; lia. 
      rewrite Cmult_1_r.
      destruct (y / S n <? m) eqn:L1, (y <? m * S n) eqn:L2; trivial.
      * apply Nat.ltb_lt in L1. 
        apply Nat.ltb_nlt in L2. 
        contradict L2. 
        clear H.
        (* Why doesn't this lemma exist??? *)
        destruct m.
        lia.
        apply Nat.div_small_iff. 
        simpl. apply Nat.neq_succ_0. (* `lia` will solve in 8.11+ *)
        apply Nat.div_small in L1.
        rewrite Nat.Div0.div_div in L1.
        rewrite Nat.mul_comm.
        assumption.
      * apply Nat.ltb_nlt in L1. 
        apply Nat.ltb_lt in L2. 
        contradict L1. 
        apply Nat.Div0.div_lt_upper_bound.
        rewrite Nat.mul_comm.
        assumption.
  + simpl.
    bdestruct (x / n =? y / n); simpl; try lca.
    bdestruct (x mod n =? y mod n); simpl; try lca.
    destruct n; try lca.    
    contradict Eq.
    rewrite (Nat.div_mod x (S n)) by lia.
    rewrite (Nat.div_mod y (S n)) by lia.
    rewrite H, H0; reflexivity.
Qed.


Local Open Scope nat_scope.

Lemma kron_assoc_mat_equiv : forall {m n p q r s : nat}
  (A : Matrix m n) (B : Matrix p q) (C : Matrix r s),
  (A ⊗ B ⊗ C) == A ⊗ (B ⊗ C).                                
Proof.
  intros. intros i j Hi Hj.
  unfold kron.
  rewrite 2 mod_product.
  rewrite (Nat.mul_comm p r).
  rewrite (Nat.mul_comm q s).
  rewrite <- 2 Nat.Div0.div_div.
  rewrite <- 2 div_mod.
  rewrite Cmult_assoc.
  reflexivity.
Qed.  

Lemma kron_assoc : forall {m n p q r s : nat}
  (A : Matrix m n) (B : Matrix p q) (C : Matrix r s),
  WF_Matrix A -> WF_Matrix B -> WF_Matrix C ->
  (A ⊗ B ⊗ C) = A ⊗ (B ⊗ C).                                
Proof.
  intros.
  apply mat_equiv_eq; auto with wf_db zarith.
  apply kron_assoc_mat_equiv.
Qed.  

Lemma kron_mixed_product : forall {m n o p q r : nat} (A : Matrix m n) (B : Matrix p q ) 
  (C : Matrix n o) (D : Matrix q r), (A ⊗ B) × (C ⊗ D) = (A × C) ⊗ (B × D).
Proof.
  intros m n o p q r A B C D.
  unfold kron, Mmult.
  prep_matrix_equality.
  destruct q.
  + rewrite Nat.mul_0_r.
    rewrite Cmult_0_r.
    reflexivity. 
  + rewrite (@big_sum_product Complex.C _ _ _ C_is_ring) by easy.
    apply big_sum_eq.
    apply functional_extensionality.
    intros; lca.
Qed.

(* Arguments kron_mixed_product [m n o p q r]. *)

(* A more explicit version, for when typechecking fails *)
Lemma kron_mixed_product' : forall (m n n' o p q q' r mp nq or: nat)
    (A : Matrix m n) (B : Matrix p q) (C : Matrix n' o) (D : Matrix q' r),
    n = n' -> q = q' ->    
    mp = m * p -> nq = n * q -> or = o * r ->
  (@Mmult mp nq or (@kron m n p q A B) (@kron n' o q' r C D)) =
  (@kron m o p r (@Mmult m n o A C) (@Mmult p q r B D)).
Proof. intros. subst. apply kron_mixed_product. Qed.

Lemma kron_id_dist_r : forall {n m o} p (A : Matrix n m) (B : Matrix m o),
  WF_Matrix A -> WF_Matrix B -> (A × B) ⊗ (I p) = (A ⊗ (I p)) × (B ⊗ (I p)).
Proof.
	intros.
  now rewrite kron_mixed_product, Mmult_1_r by auto with wf_db.
Qed.

Lemma kron_id_dist_l : forall {n m o} p (A : Matrix n m) (B : Matrix m o),
  WF_Matrix A -> WF_Matrix B -> (I p) ⊗ (A × B) = ((I p) ⊗ A) × ((I p) ⊗ B).
Proof.
	intros.
  now rewrite kron_mixed_product, Mmult_1_r by auto with wf_db.
Qed.
  
Lemma kron_split_diag {n m p q} (A : Matrix n m) (B : Matrix p q) 
  (HA : WF_Matrix A) (HB : WF_Matrix B) : 
  A ⊗ B = (A ⊗ I p) × (I m ⊗ B).
Proof.
  now rewrite kron_mixed_product, Mmult_1_l, Mmult_1_r.
Qed.

Lemma kron_split_antidiag {n m p q} (A : Matrix n m) (B : Matrix p q) 
  (HA : WF_Matrix A) (HB : WF_Matrix B) : 
  A ⊗ B = (I n ⊗ B) × (A ⊗ I q).
Proof.
  now rewrite kron_mixed_product, Mmult_1_l, Mmult_1_r.
Qed.

Lemma direct_sum_assoc : forall {m n p q r s : nat}
  (A : Matrix m n) (B : Matrix p q) (C : Matrix r s),
  (A .⊕ B .⊕ C) = A .⊕ (B .⊕ C).
Proof. intros. 
       unfold direct_sum. 
       prep_matrix_equality.
       bdestruct_all; simpl; auto.
       repeat (apply f_equal_gen; try lia); easy. 
Qed.
       
Lemma outer_product_eq : forall m (φ ψ : Matrix m 1),
 φ = ψ -> outer_product φ φ = outer_product ψ ψ.
Proof. congruence. Qed.

Lemma outer_product_kron : forall m n (φ : Matrix m 1) (ψ : Matrix n 1), 
    outer_product φ φ ⊗ outer_product ψ ψ = outer_product (φ ⊗ ψ) (φ ⊗ ψ).
Proof. 
  intros. unfold outer_product. 
  specialize (kron_adjoint φ ψ) as KT. 
  simpl in *. rewrite KT.
  specialize (kron_mixed_product φ ψ (φ†) (ψ†)) as KM. 
  simpl in *. rewrite KM.
  reflexivity.
Qed.

Lemma big_kron_app : forall {n m} (l1 l2 : list (Matrix n m)),
  (forall i, WF_Matrix (nth i l1 (@Zero n m))) ->
  (forall i, WF_Matrix (nth i l2 (@Zero n m))) ->
  ⨂ (l1 ++ l2) = (⨂ l1) ⊗ (⨂ l2).
Proof. induction l1.
       - intros. simpl. rewrite (kron_1_l _ _ (⨂ l2)); try easy.
         apply (WF_big_kron _ _ _ (@Zero n m)); easy.
       - intros. simpl. rewrite IHl1. 
         rewrite kron_assoc.
         do 2 (rewrite <- Nat.pow_add_r).
         rewrite app_length.
         reflexivity.
         assert (H' := H 0); simpl in H'; easy.
         all : try apply (WF_big_kron _ _ _ (@Zero n m)); try easy. 
         all : intros. 
         all : assert (H' := H (S i)); simpl in H'; easy.
Qed.

Lemma kron_n_1 {n m} (A : Matrix n m) (HA : WF_Matrix A) : 
  1 ⨂ A = A.
Proof.
  now apply kron_1_l.
Qed.

Lemma kron_n_S {n m} (A : Matrix n m) k : 
  (S k) ⨂ A = (k ⨂ A) ⊗ A.
Proof.
  easy.
Qed.

Lemma kron_n_assoc :
  forall n {m1 m2} (A : Matrix m1 m2), WF_Matrix A -> (S n) ⨂ A = A ⊗ (n ⨂ A).
Proof.
  intros. induction n.
  - simpl. 
    rewrite kron_1_r. 
    rewrite kron_1_l; try assumption.
    reflexivity.
  - simpl.
    replace (m1 * (m1 ^ n)) with ((m1 ^ n) * m1) by apply Nat.mul_comm.
    replace (m2 * (m2 ^ n)) with ((m2 ^ n) * m2) by apply Nat.mul_comm.
    rewrite <- kron_assoc; auto with wf_db.
    rewrite <- IHn.
    reflexivity.
Qed.

Lemma kron_n_adjoint : forall n {m1 m2} (A : Matrix m1 m2),
  WF_Matrix A -> (n ⨂ A)† = n ⨂ A†.
Proof.
  intros. induction n.
  - simpl. apply id_adjoint_eq.
  - simpl.
    replace (m1 * (m1 ^ n)) with ((m1 ^ n) * m1) by apply Nat.mul_comm.
    replace (m2 * (m2 ^ n)) with ((m2 ^ n) * m2) by apply Nat.mul_comm.
    rewrite kron_adjoint, IHn.
    reflexivity.
Qed.

Lemma kron_n_transpose : forall (m n o : nat) (A : Matrix m n),
  (o ⨂ A)⊤ = o ⨂ (A⊤). 
Proof. 
  induction o; intros.
  - apply id_transpose_eq.
  - simpl; rewrite <- IHo; rewrite <- kron_transpose; reflexivity. 
Qed.

Lemma Mscale_kron_n_distr_r : forall {m1 m2} n α (A : Matrix m1 m2),
  n ⨂ (α .* A) = (α ^ n) .* (n ⨂ A).
Proof.
  intros.
  induction n; simpl.
  rewrite Mscale_1_l. reflexivity.
  rewrite IHn. 
  rewrite Mscale_kron_dist_r, Mscale_kron_dist_l. 
  rewrite Mscale_assoc.
  reflexivity.
Qed.

Lemma kron_n_mult : forall {m1 m2 m3} n (A : Matrix m1 m2) (B : Matrix m2 m3),
  n ⨂ A × n ⨂ B = n ⨂ (A × B).
Proof.
  intros.
  induction n; simpl.
  - apply Mmult_1_l, WF_I.
  - rewrite <- IHn. 
    rewrite <- kron_mixed_product.
    f_equal; apply Nat.mul_comm.
Qed.

Lemma kron_n_I : forall n, n ⨂ I 2 = I (2 ^ n).
Proof.
  intros.
  induction n; simpl.
  reflexivity.
  rewrite IHn. 
  rewrite id_kron.
  apply f_equal.
  lia.
Qed.

Lemma kron_n_I_gen : forall n m, n ⨂ I m = I (m ^ n).
Proof.
  intros.
  induction n; simpl.
  reflexivity.
  rewrite IHn. 
  rewrite id_kron.
  apply f_equal.
  lia.
Qed.

Lemma Mmult_n_kron_distr_l : forall {m n} i (A : Square m) (B : Square n),
  i ⨉ (A ⊗ B) = (i ⨉ A) ⊗ (i ⨉ B).
Proof.
  intros m n i A B.
  induction i; simpl.
  rewrite id_kron; reflexivity.
  rewrite IHi.
  rewrite kron_mixed_product.
  reflexivity.
Qed.

Lemma Mmult_n_1_l : forall {n} (A : Square n),
  WF_Matrix A ->
  1 ⨉ A = A.
Proof. intros n A WF. simpl. rewrite Mmult_1_r; auto. Qed.

Lemma Mmult_n_1_r : forall n i,
  i ⨉ (I n) = I n.
Proof.
  intros n i.
  induction i; simpl.
  reflexivity.
  rewrite IHi.  
  rewrite Mmult_1_l; auto with wf_db.
Qed.

Lemma Mmult_n_eigenvector : forall {n} (A : Square n) (ψ : Vector n) λ i,
  WF_Matrix ψ -> A × ψ = λ .* ψ ->
  i ⨉ A × ψ = (λ ^ i) .* ψ.
Proof.
  intros n A ψ λ i WF H.
  induction i; simpl.
  rewrite Mmult_1_l; auto.
  rewrite Mscale_1_l; auto.
  rewrite Mmult_assoc.
  rewrite IHi.
  rewrite Mscale_mult_dist_r.
  rewrite H.
  rewrite Mscale_assoc.
  rewrite Cmult_comm.
  reflexivity.
Qed.




(** * Summation lemmas specific to matrices **)

(* due to dimension problems, we did not prove that Matrix m n is a ring with respect to either
   multiplication or kron. Thus all of these need to be proven *)
Lemma kron_Msum_distr_l : 
  forall {d1 d2 d3 d4} n (f : nat -> Matrix d1 d2) (A : Matrix d3 d4),
  A ⊗ big_sum f n = big_sum (fun i => A ⊗ f i) n.
Proof.
  intros.
  induction n; simpl. lma.
  rewrite kron_plus_distr_l, IHn. reflexivity.
Qed.

Lemma kron_Msum_distr_r : 
  forall {d1 d2 d3 d4} n (f : nat -> Matrix d1 d2) (A : Matrix d3 d4),
  big_sum f n ⊗ A = big_sum (fun i => f i ⊗ A) n.
Proof.
  intros.
  induction n; simpl. lma.
  rewrite kron_plus_distr_r, IHn. reflexivity.
Qed.

Lemma Mmult_Msum_distr_l : forall {d1 d2 m} n (f : nat -> Matrix d1 d2) (A : Matrix m d1),
  A × big_sum f n = big_sum (fun i => A × f i) n.
Proof.
  intros.
  induction n; simpl. 
  rewrite Mmult_0_r. reflexivity.
  rewrite Mmult_plus_distr_l, IHn. reflexivity.
Qed.

Lemma Mmult_Msum_distr_r : forall {d1 d2 m} n (f : nat -> Matrix d1 d2) (A : Matrix d2 m),
  big_sum f n × A = big_sum (fun i => f i × A) n.
Proof.
  intros.
  induction n; simpl. 
  rewrite Mmult_0_l. reflexivity.
  rewrite Mmult_plus_distr_r, IHn. reflexivity.
Qed.

Lemma Mscale_Msum_distr_r : forall {d1 d2} n (c : C) (f : nat -> Matrix d1 d2),
  big_sum (fun i => c .* (f i)) n = c .* big_sum f n.
Proof.
  intros d1 d2 n c f.
  induction n; simpl. lma.
  rewrite Mscale_plus_distr_r, IHn. reflexivity.
Qed.

Lemma Mscale_Msum_distr_l : forall {d1 d2} n (f : nat -> C) (A : Matrix d1 d2),
  big_sum (fun i => (f i) .* A) n = big_sum f n .* A.
Proof.
  intros d1 d2 n f A.
  induction n; simpl. lma.
  rewrite Mscale_plus_distr_l, IHn. reflexivity.
Qed.

Lemma Msum_constant : forall {d1 d2} n (A : Matrix d1 d2),  big_sum (fun _ => A) n = INR n .* A.
Proof.
  intros. 
  induction n.
  simpl. lma.
  simpl big_sum.
  rewrite IHn.
  replace (S n) with (n + 1)%nat by lia. 
  rewrite plus_INR; simpl. 
  rewrite RtoC_plus. 
  rewrite Mscale_plus_distr_l.
  lma.
Qed.

Lemma Msum_transpose : forall n m p f,
  (big_sum (G:=Matrix n m) f p) ⊤ = 
  big_sum (G:=Matrix n m) (fun i => (f i) ⊤) p.
Proof.
  intros.
  rewrite (big_sum_func_distr f transpose); easy.
Qed.

Lemma Msum_adjoint : forall {d1 d2} n (f : nat -> Matrix d1 d2),
  (big_sum f n)† = big_sum (fun i => (f i)†) n.
Proof.
  intros.
  rewrite (big_sum_func_distr f adjoint) by apply Mplus_adjoint.
  reflexivity.
Qed.

Lemma Msum_Csum : forall {d1 d2} n (f : nat -> Matrix d1 d2) i j,
  (big_sum f n) i j = big_sum (fun x => (f x) i j) n.
Proof.
  intros. 
  rewrite (big_sum_func_distr f (fun g => g i j)) by easy.
  reflexivity.
Qed.

Lemma Msum_plus : forall n {d1 d2} (f g : nat -> Matrix d1 d2), 
    big_sum (fun x => f x .+ g x) n = big_sum f n .+ big_sum g n.
Proof.
  intros.
  induction n; simpl.
  lma.
  rewrite IHn. lma.
Qed.

Lemma Mmult_vec_comm {n} (v u : Vector n) : WF_Matrix u -> WF_Matrix v ->
  v ⊤%M × u = u ⊤%M × v.
Proof.
  intros Hu Hv.
  prep_matrix_equivalence.
  by_cell.
  apply big_sum_eq_bounded.
  intros k Hk.
  unfold transpose.
  lca.
Qed.


(** * Tactics **)

(* Note on "using [tactics]": Most generated subgoals will be of the form
   WF_Matrix M, where auto with wf_db will work.
   Occasionally WF_Matrix M will rely on rewriting to match an assumption in the
   context, here we recursively autorewrite (which adds time).
   kron_1_l requires proofs of (n > 0)%nat, here we use lia. *)

(* *)

(* Convert a list to a vector *)
Fixpoint vec_to_list' {nmax : nat} (n : nat) (v : Vector nmax) :=
  match n with
  | O    => nil
  | S n' => v (nmax - n)%nat O :: vec_to_list' n' v
  end.
Definition vec_to_list {n : nat} (v : Vector n) := vec_to_list' n v.

Lemma vec_to_list'_length : forall m n (v : Vector n), length (vec_to_list' m v) = m.
Proof.
  intros.
  induction m; auto.
  simpl. rewrite IHm.
  reflexivity.
Qed.

Lemma vec_to_list_length : forall n (v : Vector n), length (vec_to_list v) = n.
Proof. intros. apply vec_to_list'_length. Qed.

Lemma nth_vec_to_list' : forall {m n} (v : Vector n) x,
  (m <= n)%nat -> (x < m)%nat -> nth x (vec_to_list' m v) C0 = v (n - m + x)%nat O.
Proof.
  intros m n v x Hm.
  gen x.
  induction m; intros x Hx.
  lia.
  simpl.
  destruct x.
  rewrite Nat.add_0_r.
  reflexivity.
  rewrite IHm by lia.
  replace (n - S m + S x)%nat with (n - m + x)%nat by lia.
  reflexivity.
Qed.

Lemma nth_vec_to_list : forall n (v : Vector n) x,
  (x < n)%nat -> nth x (vec_to_list v) C0 = v x O.
Proof.
  intros.
  unfold vec_to_list.
  rewrite nth_vec_to_list' by lia.
  replace (n - n + x)%nat with x by lia.
  reflexivity.
Qed.

Lemma vec_to_list2D_eq {n} (v : Vector n) : WF_Matrix v ->
  v = (list2D_to_matrix [vec_to_list v]) ⊤.
Proof.
  intros HWF.
  pose proof (vec_to_list_length n v) as Hlen.
  apply mat_equiv_eq.
  - auto_wf.
  - cbn. rewrite Hlen. 
    apply WF_transpose.
    apply show_WF_list2D_to_matrix; cbn; rewrite ?Hlen; try easy.
    now rewrite Nat.eqb_refl.
  - intros i j Hi Hj.
    replace j with 0 by lia.
    cbn.
    now rewrite nth_vec_to_list.
Qed.

Lemma matrix_eq_list2D_to_matrix {m n} (A : Matrix m n) (HA : WF_Matrix A) :
  A = @make_WF m n (list2D_to_matrix (
    map vec_to_list (map (B:=Vector n) 
      (fun k => fun i j => if j =? 0 then A k i else C0) (seq 0 m)))).
Proof.
  prep_matrix_equivalence.
  rewrite make_WF_equiv.
  intros i j Hi Hj.
  unfold list2D_to_matrix.
  rewrite (map_nth_small Zero) by now rewrite map_length, seq_length.
  rewrite (map_nth_small 0) by now rewrite seq_length.
  rewrite nth_vec_to_list by easy.
  now rewrite seq_nth by easy.
Qed.

Lemma list2D_to_matrix_cons l li : 
  list2D_to_matrix (l :: li) = 
  list2D_to_matrix [l] .+ 
  (fun x y => if x =? 0 then C0 else list2D_to_matrix li (x - 1) y).
Proof.
  prep_matrix_equality.
  autounfold with U_db.
  cbn.
  destruct x; [lca|].
  replace (S x - 1)%nat with x by lia.
  destruct x, y; cbn; now Csimpl.
Qed.

Lemma Mscale_list2D_to_matrix {n m} c li : 
  @eq (Matrix n m) (@scale n m c (list2D_to_matrix li)) 
  (list2D_to_matrix (map (map (Cmult c)) li)).
Proof.
  prep_matrix_equality.
  autounfold with U_db.
  unfold list2D_to_matrix.
  change [] with (map (Cmult c) []).
  rewrite map_nth.
  replace C0 with (c * C0)%C by lca.
  rewrite map_nth.
  now Csimpl.
Qed.



(** Restoring Matrix Dimensions *)


(** Restoring Matrix dimensions *)
Ltac is_nat n := match type of n with nat => idtac end.

Ltac is_nat_equality :=
  match goal with 
  | |- ?A = ?B => is_nat A
  end.

Ltac unify_matrix_dims tac := 
  try reflexivity; 
  repeat (apply f_equal_gen; 
    try reflexivity; try (is_nat_equality; tac)).

Ltac restore_dims_rec A :=
   match A with
(* special cases *)
  | ?A × I _          => let A' := restore_dims_rec A in 
                        match type of A' with 
                        | Matrix ?m' ?n' => constr:(@Mmult m' n' n' A' (I n'))
                        end
  | I _ × ?B          => let B' := restore_dims_rec B in 
                        match type of B' with 
                        | Matrix ?n' ?o' => constr:(@Mmult n' n' o' (I n')  B')
                        end
  | ?A × @Zero ?n ?n  => let A' := restore_dims_rec A in 
                        match type of A' with 
                        | Matrix ?m' ?n' => constr:(@Mmult m' n' n' A' (@Zero n' n'))
                        end
  | @Zero ?n ?n × ?B  => let B' := restore_dims_rec B in 
                        match type of B' with 
                        | Matrix ?n' ?o' => constr:(@Mmult n' n' o' (@Zero n' n') B')
                        end
  | ?A × @Zero ?n ?o  => let A' := restore_dims_rec A in 
                        match type of A' with 
                        | Matrix ?m' ?n' => constr:(@Mmult m' n' o A' (@Zero n' o))
                        end
  | @Zero ?m ?n × ?B  => let B' := restore_dims_rec B in 
                        match type of B' with 
                        | Matrix ?n' ?o' => constr:(@Mmult n' n' o' (@Zero m n') B')
                        end
  | ?A .+ @Zero ?m ?n => let A' := restore_dims_rec A in 
                        match type of A' with 
                        | Matrix ?m' ?n' => constr:(@Mplus m' n' A' (@Zero m' n'))
                        end
  | @Zero ?m ?n .+ ?B => let B' := restore_dims_rec B in 
                        match type of B' with 
                        | Matrix ?m' ?n' => constr:(@Mplus m' n' (@Zero m' n') B')
                        end
(* general cases *)
  | ?A = ?B  => let A' := restore_dims_rec A in 
                let B' := restore_dims_rec B in 
                match type of A' with 
                | Matrix ?m' ?n' => constr:(@eq (Matrix m' n') A' B')
                  end
  | mat_equiv ?A ?B => 
                let A' := restore_dims_rec A in 
                let B' := restore_dims_rec B in 
                match type of A' with 
                | Matrix ?m' ?n' => constr:(@mat_equiv m' n' A' B')
                  end
  | ?A × ?B   => let A' := restore_dims_rec A in 
                let B' := restore_dims_rec B in 
                match type of A' with 
                | Matrix ?m' ?n' =>
                  match type of B' with 
                  | Matrix ?n'' ?o' => constr:(@Mmult m' n' o' A' B')
                  end
                end 
  | ?A ⊗ ?B   => let A' := restore_dims_rec A in 
                let B' := restore_dims_rec B in 
                match type of A' with 
                | Matrix ?m' ?n' =>
                  match type of B' with 
                  | Matrix ?o' ?p' => constr:(@kron m' n' o' p' A' B')
                  end
                end
  | ?A †      => let A' := restore_dims_rec A in 
                match type of A' with
                | Matrix ?m' ?n' => constr:(@adjoint m' n' A')
                end
  | ?A .+ ?B => let A' := restore_dims_rec A in 
               let B' := restore_dims_rec B in 
               match type of A' with 
               | Matrix ?m' ?n' =>
                 match type of B' with 
                 | Matrix ?m'' ?n'' => constr:(@Mplus m' n' A' B')
                 end
               end
  | ?c .* ?A => let A' := restore_dims_rec A in 
               match type of A' with
               | Matrix ?m' ?n' => constr:(@scale m' n' c A')
               end
  | ?n ⨂ ?A => let A' := restore_dims_rec A in
               match type of A' with
               | Matrix ?m' ?n' => constr:(@kron_n n m' n' A')
               end
  (* For predicates (eg. WF_Matrix, Mixed_State) on Matrices *)
  | ?P ?m ?n ?A => match type of P with
                  | nat -> nat -> Matrix _ _ -> Prop =>
                    let A' := restore_dims_rec A in 
                    match type of A' with
                    | Matrix ?m' ?n' => constr:(P m' n' A')
                    end
                  end
  | ?P ?n ?A => match type of P with
               | nat -> Matrix _ _ -> Prop =>
                 let A' := restore_dims_rec A in 
                 match type of A' with
                 | Matrix ?m' ?n' => constr:(P m' A')
                 end
               end
  (* Handle functions applied to matrices *)
  | ?f ?A    => let f' := restore_dims_rec f in 
               let A' := restore_dims_rec A in 
               constr:(f' A')
  (* default *)
  | ?A       => A
   end.

Ltac restore_dims_using tac := 
  match goal with
  | |- ?A      => let A' := restore_dims_rec A in 
                replace A with A' by unify_matrix_dims tac
  end.

Ltac restore_dims_by_exact tac := 
  match goal with
  | |- ?A      => let A' := restore_dims_rec A in 
                replace A with A' by tac
  end.

Ltac restore_dims_tac :=
  (* Can redefine with:
  Ltac restore_dims_tac ::= (tactic). 
  to extend functionality. *)
  (repeat rewrite Nat.pow_1_l; try ring; 
  unify_pows_two; simpl; lia).

Ltac restore_dims :=
  restore_dims_using restore_dims_tac.

Tactic Notation "restore_dims" "by" tactic(tac) := 
  restore_dims_using tac.

Tactic Notation "restore_dims" "in" hyp(H) "by" tactic3(tac) :=
  match type of H with 
  | ?A => let A' := restore_dims_rec A in 
      replace A with A' in H by unify_matrix_dims tac
  end.

Tactic Notation "restore_dims" "in" hyp(H) :=
  restore_dims in H by restore_dims_tac.

Tactic Notation "restore_dims" "in" "*" "|-" "by" tactic3(tac) :=
  multimatch goal with
  | H : _ |- _ => try restore_dims in H by tac
  end.

Tactic Notation "restore_dims" "in" "*" "|-" :=
  restore_dims in * |- by restore_dims_tac.

Tactic Notation "restore_dims" "in" "*" "by" tactic3(tac) :=
  restore_dims in * |- by tac; restore_dims by tac.

Tactic Notation "restore_dims" "in" "*" :=
  restore_dims in * by restore_dims_tac.

(* Proofs depending on restore_dims *)

Lemma kron_n_assoc_mat_equiv :
  forall n {m1 m2} (A : Matrix m1 m2), (S n) ⨂ A ≡ A ⊗ (n ⨂ A).
Proof.
  intros. induction n.
  - simpl. 
    rewrite kron_1_r.
    restore_dims. 
    now rewrite kron_1_l_mat_equiv.
  - cbn [kron_n] in *.
    restore_dims in *.
    rewrite IHn at 1.
    restore_dims.
    now rewrite kron_assoc_mat_equiv.
Qed.

Lemma kron_n_m_split_mat_equiv {o p} : forall n m (A : Matrix o p), 
  (n + m) ⨂ A ≡ n ⨂ A ⊗ m ⨂ A.
Proof.
  induction n.
  - simpl. 
    intros.
    symmetry. 
    restore_dims.
    now rewrite kron_1_l_mat_equiv.
  - intros.
    simpl.
    restore_dims.
    rewrite IHn.
    restore_dims by (rewrite ?Nat.pow_add_r; lia).
    rewrite kron_assoc_mat_equiv.
    symmetry.
    restore_dims.
    rewrite kron_assoc_mat_equiv.
    pose proof (kron_n_assoc_mat_equiv m A) as H.
    symmetry in H.
    restore_dims in *.
    rewrite H.
    simpl.
    now restore_dims.
Qed.

Lemma kron_n_m_split {o p} : forall n m (A : Matrix o p), 
  WF_Matrix A -> (n + m) ⨂ A = n ⨂ A ⊗ m ⨂ A.
Proof.
  induction n.
  - simpl. 
    intros. 
    rewrite kron_1_l; try auto with wf_db.
  - intros.
    simpl.
    rewrite IHn; try auto.
    restore_dims.
    rewrite 2 kron_assoc; try auto with wf_db.
    rewrite <- kron_n_assoc; try auto.
    simpl.
    restore_dims.
    reflexivity.
Qed.


(** Matrix Simplification *)


(* Old: 
#[global] Hint Rewrite kron_1_l kron_1_r Mmult_1_l Mmult_1_r id_kron id_adjoint_eq
     @Mmult_adjoint Mplus_adjoint @kron_adjoint @kron_mixed_product
     id_adjoint_eq adjoint_involutive using 
     (auto 100 with wf_db; autorewrite with M_db; auto 100 with wf_db; lia) : M_db.
*)

(* eauto will cause major choking... *)
#[global] Hint Rewrite  @kron_1_l @kron_1_r @Mmult_1_l @Mmult_1_r @Mscale_1_l 
     @id_adjoint_eq @id_transpose_eq using (auto 100 with wf_db) : M_db_light.
#[global] Hint Rewrite @kron_0_l @kron_0_r @Mmult_0_l @Mmult_0_r @Mplus_0_l @Mplus_0_r
     @Mscale_0_l @Mscale_0_r @zero_adjoint_eq @zero_transpose_eq using (auto 100 with wf_db) : M_db_light.

(* I don't like always doing restore_dims first, but otherwise sometimes leaves 
   unsolvable WF_Matrix goals. *)
Ltac Msimpl_light := try restore_dims; autorewrite with M_db_light.

#[global] Hint Rewrite @Mmult_adjoint @Mplus_adjoint @kron_adjoint @kron_mixed_product
     @adjoint_involutive using (auto 100 with wf_db) : M_db.

Ltac Msimpl := try restore_dims; autorewrite with M_db_light M_db.

(** Distribute addition to the outside of matrix expressions. *)

Ltac distribute_plus :=
  repeat match goal with 
  | |- context [?a × (?b .+ ?c)] => rewrite (Mmult_plus_distr_l _ _ _ a b c)
  | |- context [(?a .+ ?b) × ?c] => rewrite (Mmult_plus_distr_r _ _ _ a b c)
  | |- context [?a ⊗ (?b .+ ?c)] => rewrite (kron_plus_distr_l _ _ _ _ a b c)
  | |- context [(?a .+ ?b) ⊗ ?c] => rewrite (kron_plus_distr_r _ _ _ _ a b c)
  end.

(** Distribute scaling to the outside of matrix expressions *)

Ltac distribute_scale := 
  repeat
   match goal with
   | |- context [ (?c .* ?A) × ?B   ] => rewrite (Mscale_mult_dist_l _ _ _ c A B)
   | |- context [ ?A × (?c .* ?B)   ] => rewrite (Mscale_mult_dist_r _ _ _ c A B)
   | |- context [ (?c .* ?A) ⊗ ?B   ] => rewrite (Mscale_kron_dist_l _ _ _ _ c A B)
   | |- context [ ?A ⊗ (?c .* ?B)   ] => rewrite (Mscale_kron_dist_r _ _ _ _ c A B)
   | |- context [ ?c .* (?c' .* ?A) ] => rewrite (Mscale_assoc _ _ c c' A)
   end.

Ltac distribute_adjoint :=
  repeat match goal with
  | |- context [(?c .* ?A)†] => rewrite (Mscale_adj _ _ c A)
  | |- context [(?A .+ ?B)†] => rewrite (Mplus_adjoint _ _ A B)
  | |- context [(?A × ?B)†] => rewrite (Mmult_adjoint A B)
  | |- context [(?A ⊗ ?B)†] => rewrite (kron_adjoint A B)
  end.


(** Tactics for solving computational matrix equalities **)

(* Construct matrices full of evars *)
Ltac mk_evar t T := match goal with _ => evar (t : T) end.

Ltac evar_list n := 
  match n with 
  | O => constr:(@nil C)
  | S ?n' => let e := fresh "e" in
            let none := mk_evar e C in 
            let ls := evar_list n' in 
            constr:(e :: ls)
            
  end.

Ltac evar_list_2d m n := 
  match m with 
  | O => constr:(@nil (list C))
  | S ?m' => let ls := evar_list n in 
            let ls2d := evar_list_2d m' n in  
            constr:(ls :: ls2d)
  end.

Ltac evar_matrix m n := let ls2d := (evar_list_2d m n) 
                        in constr:(list2D_to_matrix ls2d).   

(* Tactic version of Nat.lt *)
Ltac tac_lt m n := 
  match n with 
  | S ?n' => match m with 
            | O => idtac
            | S ?m' => tac_lt m' n'
            end
  end.

(* Possible TODO: We could have the tactic below use restore_dims instead of 
   simplifying before rewriting. *)
(* Reassociate matrices so that smallest dimensions are multiplied first:
For (m x n) × (n x o) × (o x p):
If m or o is the smallest, associate left
If n or p is the smallest, associate right
(The actual time for left is (m * o * n) + (m * p * o) = mo(n+p) 
                      versus (n * p * o) + (m * p * n) = np(m+o) for right. 
We find our heuristic to be pretty accurate, though.)
*)
Ltac assoc_least := 
  repeat (simpl; match goal with
  | [|- context[@Mmult ?m ?o ?p (@Mmult ?m ?n ?o ?A ?B) ?C]] => tac_lt p o; tac_lt p m; 
       let H := fresh "H" in 
       specialize (Mmult_assoc A B C) as H; simpl in H; rewrite H; clear H
  | [|- context[@Mmult ?m ?o ?p (@Mmult ?m ?n ?o ?A ?B) ?C]] => tac_lt n o; tac_lt n m; 
       let H := fresh "H" in 
       specialize (Mmult_assoc  A B C) as H; simpl in H; rewrite H; clear H
  | [|- context[@Mmult ?m ?n ?p ?A (@Mmult ?n ?o ?p ?B ?C)]] => tac_lt m n; tac_lt m p; 
       let H := fresh "H" in 
       specialize (Mmult_assoc A B C) as H; simpl in H; rewrite <- H; clear H
  | [|- context[@Mmult ?m ?n ?p ?A (@Mmult ?n ?o ?p ?B ?C)]] => tac_lt o n; tac_lt o p; 
       let H := fresh "H" in 
       specialize (Mmult_assoc A B C) as H; simpl in H; rewrite <- H; clear H
  end).


(* Helper function for crunch_matrix *)
Ltac solve_out_of_bounds := 
  repeat match goal with 
  | [H : WF_Matrix ?M |- context[?M ?a ?b] ] => 
      rewrite (H a b) by (left; simpl; lia) 
  | [H : WF_Matrix ?M |- context[?M ?a ?b] ] => 
      rewrite (H a b) by (right; simpl; lia) 
  end;
  autorewrite with C_db; auto.


Lemma divmod_eq : forall x y n z, 
  fst (Nat.divmod x y n z) = (n + fst (Nat.divmod x y 0 z))%nat.
Proof.
  induction x.
  + intros. simpl. lia.
  + intros. simpl. 
    destruct z.
    rewrite IHx.
    rewrite IHx with (n:=1%nat).
    lia.
    rewrite IHx.
    reflexivity.
Qed.

Lemma divmod_S : forall x y n z, 
  fst (Nat.divmod x y (S n) z) = (S n + fst (Nat.divmod x y 0 z))%nat.
Proof. intros. apply divmod_eq. Qed.

Ltac destruct_m_1' :=
  match goal with
  | [ |- context[match ?x with 
                 | 0   => _
                 | S _ => _
                 end] ] => is_var x; destruct x
  | [ |- context[match fst (Nat.divmod ?x _ _ _) with 
                 | 0   => _
                 | S _ => _
                 end] ] => is_var x; destruct x
  end.

Lemma divmod_0q0 : forall x q, fst (Nat.divmod x 0 q 0) = (x + q)%nat. 
Proof.
  induction x.
  - intros. simpl. reflexivity.
  - intros. simpl. rewrite IHx. lia.
Qed.

Lemma divmod_0 : forall x, fst (Nat.divmod x 0 0 0) = x. 
Proof. intros. rewrite divmod_0q0. lia. Qed.

Ltac destruct_m_eq' := repeat 
  (progress (try destruct_m_1'; try rewrite divmod_0; try rewrite divmod_S; simpl)).

(* Unify A × B with list (list (evars)) *)
(* We convert the matrices back to functional representation for 
   unification. Simply comparing the matrices may be more efficient,
   however. *)

Ltac crunch_matrix := 
                    match goal with 
                      | [|- ?G ] => idtac "Crunching:" G
                      end;
                      repeat match goal with
                             | [ c : C |- _ ] => cbv [c]; clear c (* 'unfold' hangs *)
                             end; 
                      simpl;
                      unfold list2D_to_matrix;    
                      autounfold with U_db;
                      prep_matrix_equality;
                      simpl;
                      destruct_m_eq';
                      simpl;
                      Csimpl; (* basic rewrites only *) 
                      try reflexivity;
                      try solve_out_of_bounds. 

Ltac compound M := 
  match M with
  | ?A × ?B   => idtac
  | ?A .+ ?B  => idtac 
  | ?A .⊕ ?B => idtac
  | ?A †      => compound A
  | ?A ⊤      => compound A
  | _ .* ?A   => compound A
  end.

(* Reduce inner matrices first *)
Ltac reduce_aux M := 
  match M with 
  | ?A .+ ?B     => compound A; reduce_aux A
  | ?A .+ ?B     => compound B; reduce_aux B
  | ?A × ?B      => compound A; reduce_aux A
  | ?A × ?B      => compound B; reduce_aux B
  | @Mmult ?m ?n ?o ?A ?B      => let M' := evar_matrix m o in
                                 replace M with M';
                                 [| crunch_matrix ] 
  | @Mplus ?m ?n ?A ?B         => let M' := evar_matrix m n in
                                 replace M with M';
                                 [| crunch_matrix ] 
  end.

Ltac reduce_matrix := match goal with 
                       | [ |- ?M = _] => reduce_aux M
                       | [ |- _ = ?M] => reduce_aux M
                       end;
                       repeat match goal with 
                              | [ |- context[?c :: _ ]] => cbv [c]; clear c
                              end.

(* Reduces matrices anywhere they appear *)
Ltac reduce_matrices := assoc_least;
                        match goal with 
                        | [ |- context[?M]] => reduce_aux M
                        end;
                        repeat match goal with 
                               | [ |- context[?c :: _ ]] => cbv [c]; clear c
                               end.


Ltac solve_matrix := assoc_least;
                     repeat reduce_matrix; try crunch_matrix;
                     (* handle out-of-bounds *)
                     unfold Nat.ltb; simpl; try rewrite andb_false_r; 
                     (* try to solve complex equalities *)
                     autorewrite with C_db; try lca.

Ltac compute_matrix_getval M := 
  let lem := constr:(matrix_eq_list2D_to_matrix M
  ltac:(auto 100 using WF_Matrix_dim_change with wf_db)) in 
  lazymatch type of lem with
  | _ = @make_WF ?n ?m (list2D_to_matrix ?l) =>
    let l' := fresh "l'" in let Hl' := fresh "Hl'" in 
    let _ := match goal with |- _ =>
      set (l' := l);
      autounfold with U_db in l';
      cbn in l'; unfold Cdiv in l';
      let lval := eval unfold l' in l' in
      pose proof (lem : _ = @make_WF n m (list2D_to_matrix lval)) as Hl';
      Csimpl_in Hl';
      rewrite Hl'
    end in
    lazymatch type of Hl' with
    | _ = ?B =>
      let _ := match goal with |- _ => clear l' Hl' end in 
      constr:(B)
    end 
  end.

Ltac compute_matrix M :=
  let rec comp_mat_val M :=
  match M with
  | @Mplus ?n ?m ?A .+ ?B => 
    let A' := match goal with 
      | |- _ => let _ := match goal with |- _ => compound A end in
        let r := comp_mat_val A in constr:(r)
      | |- _ => constr:(A)
      end in 
    let B' := match goal with 
      | |- _ => let _ := match goal with |- _ => compound B end in
        let r := comp_mat_val B in constr:(r)
      | |- _ => constr:(B)
      end in 
    let r := compute_matrix_getval (@Mplus n m A' B') in 
    constr:(r)
  | @kron ?a ?b ?c ?d ?A ?B => 
    let A' := match goal with 
      | |- _ => let _ := match goal with |- _ => compound A end in
        let r := comp_mat_val A in constr:(r)
      | |- _ => constr:(A)
      end in 
    let B' := match goal with 
      | |- _ => let _ := match goal with |- _ => compound B end in
        let r := comp_mat_val B in constr:(r)
      | |- _ => constr:(B)
      end in  
    let r := compute_matrix_getval (@kron a b c d A' B') in
    constr:(r)
  | @Mmult ?a ?b ?c ?A ?B => 
    let A' := match goal with 
      | |- _ => let _ := match goal with |- _ => compound A end in
        let r := comp_mat_val A in constr:(r)
      | |- _ => constr:(A)
      end in 
    let B' := match goal with 
      | |- _ => let _ := match goal with |- _ => compound B end in
        let r := comp_mat_val B in constr:(r)
      | |- _ => constr:(B)
      end in 
    let r := compute_matrix_getval (@Mmult a b c A' B') in 
    constr:(r)
  | @scale ?a ?b ?A => 
    let _ := match goal with |- _ => compound A end in
    let A' := comp_mat_val A in 
    let r := compute_matrix_getval (@scale a b A') in 
    constr:(r)
  | ?A => 
    let r := compute_matrix_getval A in 
    constr:(r)
  end
  in let _ := comp_mat_val M in idtac.

Ltac solve_matrix_fast_with_tacs pretac posttac :=
  prep_matrix_equivalence; pretac; by_cell_no_intros; posttac.

Tactic Notation "solve_matrix_fast_with" tactic0(pretac) tactic(posttac) :=
  solve_matrix_fast_with_tacs pretac posttac.

Ltac solve_matrix_fast :=
  solve_matrix_fast_with idtac lca.


Create HintDb scalar_move_db.

#[export] Hint Rewrite 
  Mscale_kron_dist_l 
  Mscale_kron_dist_r 
  Mscale_mult_dist_l 
  Mscale_mult_dist_r 
  Mscale_assoc : scalar_move_db.

#[export] Hint Rewrite <- Mscale_plus_distr_l : scalar_move_db.
#[export] Hint Rewrite <- Mscale_plus_distr_r : scalar_move_db.

(** Gridify **)


(** Gridify: Turns an matrix expression into a normal form with 
    plus on the outside, then tensor, then matrix multiplication.
    Eg: ((..×..×..)⊗(..×..×..)⊗(..×..×..)) .+ ((..×..)⊗(..×..))
*)

Lemma repad_lemma1_l : forall (a b d : nat),
  a < b -> d = (b - a - 1) -> b = a + 1 + d.
Proof. intros. subst. lia. Qed. 

Lemma repad_lemma1_r : forall (a b d : nat),
  a < b -> d = (b - a - 1) -> b = d + 1 + a.
Proof. intros. subst. lia. Qed.

Lemma repad_lemma2 : forall (a b d : nat),
  a <= b -> d = (b - a) -> b = a + d.
Proof. intros. subst. lia. Qed.

Lemma le_ex_diff_l : forall a b, a <= b -> exists d, b = d + a. 
Proof. intros. exists (b - a). lia. Qed.

Lemma le_ex_diff_r : forall a b, a <= b -> exists d, b = a + d. 
Proof. intros. exists (b - a). lia. Qed.  

Lemma lt_ex_diff_l : forall a b, a < b -> exists d, b = d + 1 + a. 
Proof. intros. exists (b - a - 1). lia. Qed.

Lemma lt_ex_diff_r : forall a b, a < b -> exists d, b = a + 1 + d. 
Proof. intros. exists (b - a - 1). lia. Qed.

(* Remove _ < _ from hyps, remove _ - _  from goal *)
Ltac remember_differences :=
  repeat match goal with
  | H : ?a < ?b |- context[?b - ?a - 1] => 
    let d := fresh "d" in
    let R := fresh "R" in
    remember (b - a - 1) as d eqn:R ;
    apply (repad_lemma1_l a b d) in H; trivial;
    clear R;
    try rewrite H in *;
    try clear b H
  | H:?a <= ?b  |- context [ ?b - ?a ] =>
    let d := fresh "d" in
    let R := fresh "R" in
    remember (b - a) as d eqn:R ;
    apply (repad_lemma2 a b d) in H; trivial;
    clear R;
    try rewrite H in *;
    try clear b H
  end.

(* gets the exponents of the dimensions of the given matrix expression *)
(* assumes all matrices are square *)
Ltac get_dimensions M :=
  match M with
  | ?A ⊗ ?B  => let a := get_dimensions A in
               let b := get_dimensions B in
               constr:(a + b)
  | ?A .+ ?B => get_dimensions A
  | _        => match type of M with
               | Matrix 2 2 => constr:(1)
               | Matrix 4 4 => constr:(2)
               | Matrix (2^?a) (2^?a) => constr:(a)
(*             | Matrix ?a ?b => idtac "bad dims";
                                idtac M;
                                constr:(a) *)
               end
  end.

(* not necessary in this instance - produced hypothesis is H1 *)
(* This is probably fragile and should be rewritten *)
(*
Ltac hypothesize_dims :=
  match goal with
  | |- ?A × ?B = _ => let a := get_dimensions A in
                    let b := get_dimensions B in
                    assert(a = b) by lia
  | |- _ = ?A × ?B => let a := get_dimensions A in
                    let b := get_dimensions B in
                    assert(a = b) by lia
  end.
*)

(* Hopefully always grabs the outermost product. *)
Ltac hypothesize_dims :=
  match goal with
  | |- context[?A × ?B] => let a := get_dimensions A in
                         let b := get_dimensions B in
                         assert(a = b) by lia
  end.

(* Unifies an equation of the form `a + 1 + b + 1 + c = a' + 1 + b' + 1 + c'`
   (exact symmetry isn't required) by filling in the holes *) 
Ltac fill_differences :=
  repeat match goal with 
  | R : _ < _ |- _           => let d := fresh "d" in
                              destruct (lt_ex_diff_r _ _ R);
                              clear R; subst
  | H : _ = _ |- _           => rewrite <- Nat.add_assoc in H
  | H : ?a + _ = ?a + _ |- _ => apply Nat.add_cancel_l in H; subst
  | H : ?a + _ = ?b + _ |- _ => destruct (lt_eq_lt_dec a b) as [[?|?]|?]; subst
  end; try lia.

Ltac repad := 
  (* remove boolean comparisons *)
  bdestruct_all; Msimpl_light; try reflexivity;
  (* remove minus signs *) 
  remember_differences;
  (* put dimensions in hypothesis [will sometimes exist] *)
  try hypothesize_dims; clear_dups;
  (* where a < b, replace b with a + 1 + fresh *)
  fill_differences.

Ltac gridify :=
  (* remove boolean comparisons *)
  bdestruct_all; Msimpl_light; try reflexivity;
  (* remove minus signs *) 
  remember_differences;
  (* put dimensions in hypothesis [will sometimes exist] *)
  try hypothesize_dims; clear_dups;
  (* where a < b, replace b with a + 1 + fresh *)
  fill_differences;
  (* distribute *)  
  restore_dims; distribute_plus;
  repeat rewrite Nat.pow_add_r;
  repeat rewrite <- id_kron; simpl;
  repeat rewrite Nat.mul_assoc;
  restore_dims; repeat rewrite <- kron_assoc by auto_wf;
  restore_dims; repeat rewrite kron_mixed_product;
  (* simplify *)
  Msimpl_light.


(** Tactics to show implicit arguments *)


Definition kron' := @kron.      
Lemma kron_shadow : @kron = kron'. Proof. reflexivity. Qed.

Definition Mmult' := @Mmult.
Lemma Mmult_shadow : @Mmult = Mmult'. Proof. reflexivity. Qed.

Ltac show_dimensions := try rewrite kron_shadow in *; 
                        try rewrite Mmult_shadow in *.
Ltac hide_dimensions := try rewrite <- kron_shadow in *; 
                        try rewrite <- Mmult_shadow in *.
