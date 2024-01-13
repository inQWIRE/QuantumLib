
(** In this file, we define matrices and prove many basic facts from linear algebra *)

Require Import Psatz. 
Require Import String.
Require Import Program.
Require Export Complex. 
Require Import List.



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
#[export] Program Instance M_is_monoid : forall n m, Monoid (Matrix n m) := 
  { Gzero := @Zero n m
  ; Gplus := Mplus
  }.
Solve All Obligations with program_simpl; prep_matrix_equality; lca. 

#[export] Program Instance M_is_group : forall n m, Group (Matrix n m) :=
  { Gopp := Mopp }.
Solve All Obligations with program_simpl; prep_matrix_equality; lca. 

#[export] Program Instance M_is_comm_group : forall n m, Comm_Group (Matrix n m).
Solve All Obligations with program_simpl; prep_matrix_equality; lca. 


#[export] Program Instance M_is_module_space : forall n m, Module_Space (Matrix n m) C :=
  { Vscale := scale }.
Solve All Obligations with program_simpl; prep_matrix_equality; lca. 

#[export] Program Instance M_is_vector_space : forall n m, Vector_Space (Matrix n m) C.


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
#[export] Hint Unfold Zero I trace dot Mplus scale Mmult kron mat_equiv transpose
            adjoint : U_db.
  
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
                
Ltac by_cell := 
  intros;
  let i := fresh "i" in 
  let j := fresh "j" in 
  let Hi := fresh "Hi" in 
  let Hj := fresh "Hj" in 
  intros i j Hi Hj; try solve_end;
  repeat (destruct i as [|i]; simpl; [|apply <- Nat.succ_lt_mono in Hi]; try solve_end); clear Hi;
  repeat (destruct j as [|j]; simpl; [|apply <- Nat.succ_lt_mono in Hj]; try solve_end); clear Hj.

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



(** * Proofs about well-formedness **)



Lemma WF_Matrix_dim_change : forall (m n m' n' : nat) (A : Matrix m n),
  m = m' ->
  n = n' ->
  @WF_Matrix m n A ->
  @WF_Matrix m' n' A.
Proof. intros. subst. easy. Qed.

Lemma WF_Zero : forall m n : nat, WF_Matrix (@Zero m n).
Proof. intros m n. unfold WF_Matrix. reflexivity. Qed.

Lemma WF_I : forall n : nat, WF_Matrix (I n). 
Proof. 
  unfold WF_Matrix, I. intros n x y H. simpl.
  destruct H; bdestruct (x =? y); bdestruct (x <? n); trivial; lia.
Qed.

Lemma WF_I1 : WF_Matrix (I 1). Proof. apply WF_I. Qed.

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
  apply Nat.sub_add in H;
  rewrite Nat.add_comm in H;
  rewrite <- H;
  cbv;
  destruct_m_eq;
  try lca.                                        

(* Create HintDb wf_db. *)
#[export] Hint Resolve WF_Zero WF_I WF_I1 WF_mult WF_plus WF_scale WF_transpose
     WF_adjoint WF_outer_product WF_big_kron WF_kron_n WF_kron 
     WF_Mmult_n WF_Msum : wf_db.
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

(* This side is more limited *)
Lemma kron_1_l : forall (m n : nat) (A : Matrix m n), 
  WF_Matrix A -> I 1 ⊗ A = A.
Proof.
  intros m n A WF.
  prep_matrix_equality.
  unfold kron.
  unfold I, kron.
  bdestruct (m =? 0). rewrite 2 WF by lia. lca. 
  bdestruct (n =? 0). rewrite 2 WF by lia. lca.
  bdestruct (x / m <? 1); rename H1 into Eq1.
  bdestruct (x / m =? y / n); rename H1 into Eq2; simpl.
  + assert (x / m = 0)%nat by lia. clear Eq1. rename H1 into Eq1.
    rewrite Eq1 in Eq2.     
    symmetry in Eq2.
    rewrite Nat.div_small_iff in Eq2 by lia.
    rewrite Nat.div_small_iff in Eq1 by lia.
    rewrite 2 Nat.mod_small; trivial.
    lca.
  + assert (x / m = 0)%nat by lia. clear Eq1.
    rewrite H1 in Eq2. clear H1.
    assert (y / n <> 0)%nat by lia. clear Eq2.
    rewrite Nat.div_small_iff in H1 by lia.
    rewrite Cmult_0_l.
    destruct WF with (x := x) (y := y). lia.
    reflexivity.
  + rewrite andb_false_r.
    assert (x / m <> 0)%nat by lia. clear Eq1.
    rewrite Nat.div_small_iff in H1 by lia.
    rewrite Cmult_0_l.
    destruct WF with (x := x) (y := y). lia.
    reflexivity.
Qed.

Theorem transpose_involutive : forall (m n : nat) (A : Matrix m n), (A⊤)⊤ = A.
Proof. reflexivity. Qed.

Theorem adjoint_involutive : forall (m n : nat) (A : Matrix m n), A†† = A.
Proof. intros. lma. Qed.  

Lemma id_transpose_eq : forall n, (I n)⊤ = (I n).
Proof.
  intros n. unfold transpose, I.
  prep_matrix_equality.
  bdestruct (y =? x); bdestruct (x =? y); bdestruct (y <? n); bdestruct (x <? n);
    trivial; lia.
Qed.

Lemma zero_transpose_eq : forall m n, (@Zero m n)⊤ = @Zero m n.
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
  + repeat rewrite <- beq_nat_refl; simpl.
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
        rewrite Nat.div_div in L1; try lia.
        rewrite Nat.mul_comm.
        assumption.
      * apply Nat.ltb_nlt in L1. 
        apply Nat.ltb_lt in L2. 
        contradict L1. 
        apply Nat.div_lt_upper_bound. lia.
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

Lemma div_mod : forall (x y z : nat), (x / y) mod z = (x mod (y * z)) / y.
Proof.
  intros. bdestruct (y =? 0). subst. simpl.
  bdestruct (z =? 0). subst. easy.
  apply Nat.mod_0_l. easy.
  bdestruct (z =? 0). subst. rewrite Nat.mul_0_r. simpl.
  try rewrite Nat.div_0_l; easy.
  pattern x at 1. rewrite (Nat.div_mod x (y * z)) by nia.
  replace (y * z * (x / (y * z))) with ((z * (x / (y * z))) * y) by lia.
  rewrite Nat.div_add_l with (b := y) by easy.
  replace (z * (x / (y * z)) + x mod (y * z) / y) with
      (x mod (y * z) / y + (x / (y * z)) * z) by lia.
  rewrite Nat.mod_add by easy.
  apply Nat.mod_small.
  apply Nat.div_lt_upper_bound. easy. apply Nat.mod_upper_bound. nia.
Qed.

Lemma sub_mul_mod :
  forall x y z,
    y * z <= x ->
    (x - y * z) mod z = x mod z.
Proof.
  intros. bdestruct (z =? 0). subst. simpl. lia.
  specialize (Nat.sub_add (y * z) x H) as G.
  rewrite Nat.add_comm in G.
  remember (x - (y * z)) as r.
  rewrite <- G. rewrite <- Nat.add_mod_idemp_l by easy. rewrite Nat.mod_mul by easy.
  easy.
Qed.

Lemma mod_product : forall x y z, y <> 0 -> x mod (y * z) mod z = x mod z.
Proof.
  intros x y z H. bdestruct (z =? 0). subst.
  simpl. try rewrite Nat.mul_0_r. reflexivity.
  pattern x at 2. rewrite Nat.mod_eq with (b := y * z) by nia.
  replace (y * z * (x / (y * z))) with (y * (x / (y * z)) * z) by lia.
  rewrite sub_mul_mod. easy.
  replace (y * (x / (y * z)) * z) with (y * z * (x / (y * z))) by lia.
  apply Nat.mul_div_le. nia.
Qed.

Lemma kron_assoc_mat_equiv : forall {m n p q r s : nat}
  (A : Matrix m n) (B : Matrix p q) (C : Matrix r s),
  (A ⊗ B ⊗ C) == A ⊗ (B ⊗ C).                                
Proof.
  intros. intros i j Hi Hj.
  remember (A ⊗ B ⊗ C) as LHS.
  unfold kron.  
  rewrite (Nat.mul_comm p r) at 1 2.
  rewrite (Nat.mul_comm q s) at 1 2.
  assert (m * p * r <> 0) by lia.
  assert (n * q * s <> 0) by lia.
  apply Nat.neq_mul_0 in H as [Hmp Hr].
  apply Nat.neq_mul_0 in Hmp as [Hm Hp].
  apply Nat.neq_mul_0 in H0 as [Hnq Hs].
  apply Nat.neq_mul_0 in Hnq as [Hn Hq].
  rewrite <- 2 Nat.div_div by assumption.
  rewrite <- 2 div_mod.
  rewrite 2 mod_product by assumption.
  rewrite Cmult_assoc.
  subst.
  reflexivity.
Qed.  

Lemma kron_assoc : forall {m n p q r s : nat}
  (A : Matrix m n) (B : Matrix p q) (C : Matrix r s),
  WF_Matrix A -> WF_Matrix B -> WF_Matrix C ->
  (A ⊗ B ⊗ C) = A ⊗ (B ⊗ C).                                
Proof.
  intros.
  apply mat_equiv_eq; auto with wf_db.
  apply WF_kron; auto with wf_db; lia.
  apply kron_assoc_mat_equiv.
Qed.  

Lemma kron_mixed_product : forall {m n o p q r : nat} (A : Matrix m n) (B : Matrix p q ) 
  (C : Matrix n o) (D : Matrix q r), (A ⊗ B) × (C ⊗ D) = (A × C) ⊗ (B × D).
Proof.
  intros m n o p q r A B C D.
  unfold kron, Mmult.
  prep_matrix_equality.
  destruct q.
  + simpl.
    rewrite Nat.mul_0_r.
    simpl.
    rewrite Cmult_0_r.
    reflexivity. 
  + rewrite (@big_sum_product Complex.C _ _ _ C_is_ring).
    apply big_sum_eq.
    apply functional_extensionality.
    intros; lca.
    lia.
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
  rewrite Mmult_1_l. reflexivity.
  apply WF_I.
  replace (m1 * m1 ^ n) with (m1 ^ n * m1) by apply Nat.mul_comm.
  replace (m2 * m2 ^ n) with (m2 ^ n * m2) by apply Nat.mul_comm.
  replace (m3 * m3 ^ n) with (m3 ^ n * m3) by apply Nat.mul_comm.
  rewrite kron_mixed_product.
  rewrite IHn.
  reflexivity.
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

Lemma Msum_adjoint : forall {d1 d2} n (f : nat -> Matrix d1 d2),
  (big_sum f n)† = big_sum (fun i => (f i)†) n.
Proof.
  intros.
  induction n; simpl.
  lma.
  rewrite Mplus_adjoint, IHn.  
  reflexivity.
Qed.

Lemma Msum_Csum : forall {d1 d2} n (f : nat -> Matrix d1 d2) i j,
  (big_sum f n) i j = big_sum (fun x => (f x) i j) n.
Proof.
  intros. 
  induction n; simpl.
  reflexivity.
  unfold Mplus.
  rewrite IHn.
  reflexivity.
Qed.

Lemma Msum_plus : forall n {d1 d2} (f g : nat -> Matrix d1 d2), 
    big_sum (fun x => f x .+ g x) n = big_sum f n .+ big_sum g n.
Proof.
  clear.
  intros.
  induction n; simpl.
  lma.
  rewrite IHn. lma.
Qed.



(** * Defining matrix altering/col operations *)


Definition get_vec {n m} (i : nat) (S : Matrix n m) : Vector n :=
  fun x y => (if (y =? 0) then S x i else C0).   

Definition get_row {n m} (i : nat) (S : Matrix n m) : Matrix 1 m :=
  fun x y => (if (x =? 0) then S i y else C0).  

Definition reduce_row {n m} (A : Matrix (S n) m) (row : nat) : Matrix n m :=
  fun x y => if x <? row
             then A x y
             else A (1 + x) y.

Definition reduce_col {n m} (A : Matrix n (S m)) (col : nat) : Matrix n m :=
  fun x y => if y <? col
             then A x y
             else A x (1 + y).

(* more specific form for vectors *)
Definition reduce_vecn {n} (v : Vector (S n)) : Vector n :=
  fun x y => if x <? n
             then v x y
             else v (1 + x) y.

(* More specific form for squares *)
Definition reduce {n} (A : Square (S n)) (row col : nat) : Square n :=
  fun x y => (if x <? row 
              then (if y <? col 
                    then A x y
                    else A x (1+y))
              else (if y <? col 
                    then A (1+x) y
                    else A (1+x) (1+y))).

Definition col_append {n m} (T : Matrix n m) (v : Vector n) : Matrix n (S m) :=
  fun i j => if (j =? m) then v i 0 else T i j.

Definition row_append {n m} (T : Matrix n m) (v : Matrix 1 m) : Matrix (S n) m :=
  fun i j => if (i =? n) then v 0 j else T i j.

(* more general than col_append *)
Definition smash {n m1 m2} (T1 : Matrix n m1) (T2 : Matrix n m2) : Matrix n (m1 + m2) :=
  fun i j => if j <? m1 then T1 i j else T2 i (j - m1).

Definition col_wedge {n m} (T : Matrix n m) (v : Vector n) (spot : nat) : Matrix n (S m) :=
  fun i j => if j <? spot 
             then T i j
             else if j =? spot
                  then v i 0
                  else T i (j-1).

Definition row_wedge {n m} (T : Matrix n m) (v : Matrix 1 m) (spot : nat) : Matrix (S n) m :=
  fun i j => if i <? spot 
             then T i j
             else if i =? spot
                  then v 0 j
                  else T (i-1) j.

Definition col_swap {n m : nat} (S : Matrix n m) (x y : nat) : Matrix n m := 
  fun i j => if (j =? x) 
             then S i y
             else if (j =? y) 
                  then S i x
                  else S i j.

Definition row_swap {n m : nat} (S : Matrix n m) (x y : nat) : Matrix n m := 
  fun i j => if (i =? x) 
             then S y j
             else if (i =? y) 
                  then S x j
                  else S i j.

Definition col_scale {n m : nat} (S : Matrix n m) (col : nat) (a : C) : Matrix n m := 
  fun i j => if (j =? col) 
             then (a * S i j)%C
             else S i j.

Definition row_scale {n m : nat} (S : Matrix n m) (row : nat) (a : C) : Matrix n m := 
  fun i j => if (i =? row) 
             then (a * S i j)%C
             else S i j.

(* adding one column to another *)
Definition col_add {n m : nat} (S : Matrix n m) (col to_add : nat) (a : C) : Matrix n m := 
  fun i j => if (j =? col) 
             then (S i j + a * S i to_add)%C
             else S i j.

(* adding one row to another *)
Definition row_add {n m : nat} (S : Matrix n m) (row to_add : nat) (a : C) : Matrix n m := 
  fun i j => if (i =? row) 
             then (S i j + a * S to_add j)%C
             else S i j.

(* generalizing col_add *)
Definition gen_new_vec (n m : nat) (S : Matrix n m) (as' : Vector m) : Vector n :=
  big_sum (fun i => (as' i 0) .* (get_vec i S)) m.

Definition gen_new_row (n m : nat) (S : Matrix n m) (as' : Matrix 1 n) : Matrix 1 m :=
  big_sum (fun i => (as' 0 i) .* (get_row i S)) n.

(* adds all columns to single column *)
Definition col_add_many {n m} (col : nat) (as' : Vector m) (S : Matrix n m) : Matrix n m :=
  fun i j => if (j =? col) 
             then (S i j + (gen_new_vec n m S as') i 0)%C
             else S i j.

Definition row_add_many {n m} (row : nat) (as' : Matrix 1 n) (S : Matrix n m) : Matrix n m :=
  fun i j => if (i =? row) 
             then (S i j + (gen_new_row n m S as') 0 j)%C
             else S i j.

(* adds single column to each other column *)
Definition col_add_each {n m} (col : nat) (as' : Matrix 1 m) (S : Matrix n m) : Matrix n m := 
  S .+ ((get_vec col S) × as').

Definition row_add_each {n m} (row : nat) (as' : Vector n) (S : Matrix n m) : Matrix n m := 
  S .+ (as' × get_row row S).

Definition make_col_zero {n m} (col : nat) (S : Matrix n m) : Matrix n m :=
  fun i j => if (j =? col) 
             then C0
             else S i j.

Definition make_row_zero {n m} (row : nat) (S : Matrix n m) : Matrix n m :=
  fun i j => if (i =? row) 
             then C0
             else S i j.

Definition make_WF {n m} (S : Matrix n m) : Matrix n m :=
  fun i j => if (i <? n) && (j <? m) then S i j else C0.

(** proving lemmas about these new functions *)

Lemma WF_get_vec : forall {n m} (i : nat) (S : Matrix n m),
  WF_Matrix S -> WF_Matrix (get_vec i S). 
Proof. unfold WF_Matrix, get_vec in *.
       intros.
       bdestruct (y =? 0); try lia; try easy.
       apply H.
       destruct H0. 
       left; easy.
       lia. 
Qed.

Lemma WF_get_row : forall {n m} (i : nat) (S : Matrix n m),
  WF_Matrix S -> WF_Matrix (get_row i S). 
Proof. unfold WF_Matrix, get_row in *.
       intros.
       bdestruct (x =? 0); try lia; try easy.
       apply H.
       destruct H0. 
       lia. 
       right; easy.
Qed.

Lemma WF_reduce_row : forall {n m} (row : nat) (A : Matrix (S n) m),
  row < (S n) -> WF_Matrix A -> WF_Matrix (reduce_row A row).
Proof. unfold WF_Matrix, reduce_row. intros. 
       bdestruct (x <? row). 
       - destruct H1 as [H1 | H1].
         + assert (nibzo : forall (a b c : nat), a < b -> b < c -> 1 + a < c).
           { lia. }
           apply (nibzo x row (S n)) in H2.
           simpl in H2. lia. apply H.
         + apply H0; auto.
       - apply H0. destruct H1. 
         + left. simpl. lia.
         + right. apply H1. 
Qed.

Lemma WF_reduce_col : forall {n m} (col : nat) (A : Matrix n (S m)),
  col < (S m) -> WF_Matrix A -> WF_Matrix (reduce_col A col).
Proof. unfold WF_Matrix, reduce_col. intros. 
       bdestruct (y <? col). 
       - destruct H1 as [H1 | H1].   
         + apply H0; auto. 
         + assert (nibzo : forall (a b c : nat), a < b -> b < c -> 1 + a < c).
           { lia. }
           apply (nibzo y col (S m)) in H2.
           simpl in H2. lia. apply H.
       - apply H0. destruct H1.
         + left. apply H1. 
         + right. simpl. lia. 
Qed.

Lemma rvn_is_rr_n : forall {n : nat} (v : Vector (S n)),
  reduce_vecn v = reduce_row v n.
Proof. intros.
       prep_matrix_equality.
       unfold reduce_row, reduce_vecn.
       easy.
Qed.

Lemma WF_reduce_vecn : forall {n} (v : Vector (S n)),
  n <> 0 -> WF_Matrix v -> WF_Matrix (reduce_vecn v).
Proof. intros.
       rewrite rvn_is_rr_n.
       apply WF_reduce_row; try lia; try easy. 
Qed.

Lemma reduce_is_redrow_redcol : forall {n} (A : Square (S n)) (row col : nat),
  reduce A row col = reduce_col (reduce_row A row) col.
Proof. intros. 
       prep_matrix_equality.
       unfold reduce, reduce_col, reduce_row.
       bdestruct (x <? row); bdestruct (y <? col); try easy.
Qed. 

Lemma reduce_is_redcol_redrow : forall {n} (A : Square (S n)) (row col : nat),
  reduce A row col = reduce_row (reduce_col A col) row.
Proof. intros. 
       prep_matrix_equality.
       unfold reduce, reduce_col, reduce_row.
       bdestruct (x <? row); bdestruct (y <? col); try easy.
Qed. 

Lemma WF_reduce : forall {n} (A : Square (S n)) (row col : nat),
  row < S n -> col < S n -> WF_Matrix A -> WF_Matrix (reduce A row col).
Proof. intros.
       rewrite reduce_is_redrow_redcol.
       apply WF_reduce_col; try easy.
       apply WF_reduce_row; try easy.
Qed.

Lemma WF_col_swap : forall {n m : nat} (S : Matrix n m) (x y : nat),
  x < m -> y < m -> WF_Matrix S -> WF_Matrix (col_swap S x y).
Proof. unfold WF_Matrix, col_swap in *.
       intros. 
       bdestruct (y0 =? x); bdestruct (y0 =? y); destruct H2; try lia. 
       all : apply H1; try (left; apply H2).
       auto.
Qed.

Lemma WF_row_swap : forall {n m : nat} (S : Matrix n m) (x y : nat),
  x < n -> y < n -> WF_Matrix S -> WF_Matrix (row_swap S x y).
Proof. unfold WF_Matrix, row_swap in *.
       intros. 
       bdestruct (x0 =? x); bdestruct (x0 =? y); destruct H2; try lia. 
       all : apply H1; try (right; apply H2).
       auto.
Qed.

Lemma WF_col_scale : forall {n m : nat} (S : Matrix n m) (x : nat) (a : C),
  WF_Matrix S -> WF_Matrix (col_scale S x a).
Proof. unfold WF_Matrix, col_scale in *.
       intros. 
       apply H in H0.
       rewrite H0.
       rewrite Cmult_0_r.
       bdestruct (y =? x); easy.
Qed.

Lemma WF_row_scale : forall {n m : nat} (S : Matrix n m) (x : nat) (a : C),
  WF_Matrix S -> WF_Matrix (row_scale S x a).
Proof. unfold WF_Matrix, row_scale in *.
       intros. 
       apply H in H0.
       rewrite H0.
       rewrite Cmult_0_r.
       bdestruct (x0 =? x); easy.
Qed.

Lemma WF_col_add : forall {n m : nat} (S : Matrix n m) (x y : nat) (a : C),
  x < m -> WF_Matrix S -> WF_Matrix (col_add S x y a).
Proof. unfold WF_Matrix, col_add in *.
       intros.
       bdestruct (y0 =? x); destruct H1; try lia. 
       do 2 (rewrite H0; auto). lca. 
       all : apply H0; auto.
Qed.

Lemma WF_row_add : forall {n m : nat} (S : Matrix n m) (x y : nat) (a : C),
  x < n -> WF_Matrix S -> WF_Matrix (row_add S x y a).
Proof. unfold WF_Matrix, row_add in *.
       intros.
       bdestruct (x0 =? x); destruct H1; try lia. 
       do 2 (rewrite H0; auto). lca. 
       all : apply H0; auto.
Qed.

Lemma WF_gen_new_vec : forall {n m} (S : Matrix n m) (as' : Vector m),
  WF_Matrix S -> WF_Matrix (gen_new_vec n m S as').
Proof. intros.
       unfold gen_new_vec.
       apply WF_Msum; intros. 
       apply WF_scale. 
       apply WF_get_vec.
       easy.
Qed.

Lemma WF_gen_new_row : forall {n m} (S : Matrix n m) (as' : Matrix 1 n),
  WF_Matrix S -> WF_Matrix (gen_new_row n m S as').
Proof. intros.
       unfold gen_new_row.
       apply WF_Msum; intros. 
       apply WF_scale. 
       apply WF_get_row.
       easy.
Qed.

Lemma WF_col_add_many : forall {n m} (col : nat) (as' : Vector m) (S : Matrix n m),
  col < m -> WF_Matrix S -> WF_Matrix (col_add_many col as' S).
Proof. unfold WF_Matrix, col_add_many.
       intros. 
       bdestruct (y =? col).
       assert (H4 := (WF_gen_new_vec S as')).
       rewrite H4, H0; try easy.
       lca. destruct H2; lia. 
       rewrite H0; easy.
Qed.

Lemma WF_row_add_many : forall {n m} (row : nat) (as' : Matrix 1 n) (S : Matrix n m),
  row < n -> WF_Matrix S -> WF_Matrix (row_add_many row as' S).
Proof. unfold WF_Matrix, row_add_many.
       intros. 
       bdestruct (x =? row).
       assert (H4 := (WF_gen_new_row S as')).
       rewrite H4, H0; try easy.
       lca. destruct H2; lia. 
       rewrite H0; easy.
Qed.

Lemma WF_col_append : forall {n m} (T : Matrix n m) (v : Vector n),
  WF_Matrix T -> WF_Matrix v -> WF_Matrix (col_append T v).
Proof. unfold WF_Matrix in *.
       intros; destruct H1 as [H1 | H1]. 
       - unfold col_append.
         rewrite H, H0; try lia. 
         bdestruct (y =? m); easy. 
       - unfold col_append.
         bdestruct (y =? m); try lia. 
         apply H; lia. 
Qed.

Lemma WF_row_append : forall {n m} (T : Matrix n m) (v : Matrix 1 m),
  WF_Matrix T -> WF_Matrix v -> WF_Matrix (row_append T v).
Proof. unfold WF_Matrix in *.
       intros; destruct H1 as [H1 | H1]. 
       - unfold row_append.
         bdestruct (x =? n); try lia. 
         apply H; lia. 
       - unfold row_append.
         rewrite H, H0; try lia. 
         bdestruct (x =? n); easy. 
Qed.

Lemma WF_col_wedge : forall {n m} (T : Matrix n m) (v : Vector n) (spot : nat),
  spot <= m -> WF_Matrix T -> WF_Matrix v -> WF_Matrix (col_wedge T v spot).
Proof. unfold WF_Matrix in *.
       intros; destruct H2 as [H2 | H2]. 
       - unfold col_wedge.
         rewrite H0, H1; try lia. 
         rewrite H0; try lia. 
         bdestruct (y <? spot); bdestruct (y =? spot); easy. 
       - unfold col_wedge.
         bdestruct (y <? spot); bdestruct (y =? spot); try lia. 
         rewrite H0; try lia. 
         easy.  
Qed.

Lemma WF_row_wedge : forall {n m} (T : Matrix n m) (v : Matrix 1 m) (spot : nat),
  spot <= n -> WF_Matrix T -> WF_Matrix v -> WF_Matrix (row_wedge T v spot).
Proof. unfold WF_Matrix in *.
       intros; destruct H2 as [H2 | H2]. 
       - unfold row_wedge.
         bdestruct (x <? spot); bdestruct (x =? spot); try lia. 
         rewrite H0; try lia. 
         easy.  
       - unfold row_wedge.
         rewrite H0, H1; try lia. 
         rewrite H0; try lia. 
         bdestruct (x <? spot); bdestruct (x =? spot); easy. 
Qed.

Lemma WF_smash : forall {n m1 m2} (T1 : Matrix n m1) (T2 : Matrix n m2),
  WF_Matrix T1 -> WF_Matrix T2 -> WF_Matrix (smash T1 T2).
Proof. unfold WF_Matrix, smash in *.
       intros. 
       bdestruct (y <? m1).
       - apply H; lia. 
       - apply H0; lia.
Qed.

Lemma WF_col_add_each : forall {n m} (col : nat) (as' : Matrix 1 m) (S : Matrix n m),
  WF_Matrix S -> WF_Matrix as' -> WF_Matrix (col_add_each col as' S).
Proof. intros.
       unfold col_add_each.
       apply WF_plus; try easy;
       apply WF_mult; try easy;
       apply WF_get_vec; easy.
Qed.

Lemma WF_row_add_each : forall {n m} (row : nat) (as' : Vector n) (S : Matrix n m),
  WF_Matrix S -> WF_Matrix as' -> WF_Matrix (row_add_each row as' S).
Proof. intros.
       unfold row_add_each.
       apply WF_plus; try easy;
       apply WF_mult; try easy;
       apply WF_get_row; easy.
Qed.

Lemma WF_make_col_zero : forall {n m} (col : nat) (S : Matrix n m),
  WF_Matrix S -> WF_Matrix (make_col_zero col S).
Proof. unfold make_col_zero, WF_Matrix.
       intros. 
       rewrite H; try easy.
       bdestruct (y =? col); easy.
Qed.

Lemma WF_make_row_zero : forall {n m} (row : nat) (S : Matrix n m),
  WF_Matrix S -> WF_Matrix (make_row_zero row S).
Proof. unfold make_row_zero, WF_Matrix.
       intros. 
       rewrite H; try easy.
       bdestruct (x =? row); easy.
Qed.

Lemma WF_make_WF : forall {n m} (S : Matrix n m), WF_Matrix (make_WF S).
Proof. intros. 
       unfold WF_Matrix, make_WF; intros. 
       destruct H as [H | H].
       bdestruct (x <? n); try lia; easy. 
       bdestruct (y <? m); bdestruct (x <? n); try lia; easy.
Qed.

#[export] Hint Resolve WF_get_vec WF_get_row WF_reduce_row WF_reduce_col WF_reduce_vecn WF_reduce : wf_db.
#[export] Hint Resolve WF_col_swap WF_row_swap WF_col_scale WF_row_scale WF_col_add WF_row_add  : wf_db.
#[export] Hint Resolve WF_gen_new_vec WF_gen_new_row WF_col_add_many WF_row_add_many : wf_db.
#[export] Hint Resolve WF_col_append WF_row_append WF_row_wedge WF_col_wedge WF_smash : wf_db.
#[export] Hint Resolve WF_col_add_each WF_row_add_each WF_make_col_zero WF_make_row_zero WF_make_WF : wf_db.
#[export] Hint Extern 1 (Nat.lt _ _) => lia : wf_db.

Lemma get_vec_reduce_col : forall {n m} (i col : nat) (A : Matrix n (S m)),
  i < col -> get_vec i (reduce_col A col) = get_vec i A.
Proof. intros. 
       prep_matrix_equality. 
       unfold get_vec, reduce_col.
       bdestruct (i <? col); try lia; easy.
Qed.

Lemma get_vec_conv : forall {n m} (x y : nat) (S : Matrix n m),
  (get_vec y S) x 0 = S x y.
Proof. intros. unfold get_vec.
       easy.
Qed.

Lemma get_vec_mult : forall {n} (i : nat) (A B : Square n),
  A × (get_vec i B) = get_vec i (A × B).
Proof. intros. unfold get_vec, Mmult.
       prep_matrix_equality.
       bdestruct (y =? 0).
       - reflexivity.
       - apply (@big_sum_0 C C_is_monoid). intros.
         apply Cmult_0_r.
Qed.

Lemma det_by_get_vec : forall {n} (A B : Square n),
  (forall i, get_vec i A = get_vec i B) -> A = B.
Proof. intros. prep_matrix_equality.
       rewrite <- get_vec_conv.
       rewrite <- (get_vec_conv _ _ B).
       rewrite H.
       reflexivity.
Qed.

Lemma col_scale_reduce_col_same : forall {n m} (T : Matrix n (S m)) (y col : nat) (a : C),
  y = col -> reduce_col (col_scale T col a) y = reduce_col T y.
Proof. intros.
       prep_matrix_equality. 
       unfold reduce_col, col_scale. 
       bdestruct (y0 <? y); bdestruct (y0 =? col); bdestruct (1 + y0 =? col); try lia; easy. 
Qed.

Lemma col_swap_reduce_before : forall {n : nat} (T : Square (S n)) (row col c1 c2 : nat),
  col < (S c1) -> col < (S c2) ->
  reduce (col_swap T (S c1) (S c2)) row col = col_swap (reduce T row col) c1 c2.
Proof. intros. 
       prep_matrix_equality. 
       unfold reduce, col_swap.
       bdestruct (c1 <? col); bdestruct (c2 <? col); try lia. 
       simpl. 
       bdestruct (x <? row); bdestruct (y <? col); bdestruct (y =? c1);
         bdestruct (y =? S c1); bdestruct (y =? c2); bdestruct (y =? S c2); try lia; try easy. 
Qed.

Lemma col_scale_reduce_before : forall {n : nat} (T : Square (S n)) (x y col : nat) (a : C),
  y < col -> reduce (col_scale T col a) x y = col_scale (reduce T x y) (col - 1) a.
Proof. intros. 
       prep_matrix_equality. 
       destruct col; try lia. 
       rewrite Sn_minus_1. 
       unfold reduce, col_scale. 
       bdestruct (x0 <? x); bdestruct (y0 <? y); bdestruct (y0 =? S col);
         bdestruct (y0 =? col); bdestruct (1 + y0 =? S col); try lia; easy. 
Qed.

Lemma col_scale_reduce_same : forall {n : nat} (T : Square (S n)) (x y col : nat) (a : C),
  y = col -> reduce (col_scale T col a) x y = reduce T x y.
Proof. intros. 
       prep_matrix_equality. 
       unfold reduce, col_scale. 
       bdestruct (x0 <? x); bdestruct (y0 <? y);
         bdestruct (y0 =? col); bdestruct (1 + y0 =? col); try lia; easy. 
Qed.

Lemma col_scale_reduce_after : forall {n : nat} (T : Square (S n)) (x y col : nat) (a : C),
  y > col -> reduce (col_scale T col a) x y = col_scale (reduce T x y) col a.
Proof. intros. 
       prep_matrix_equality. 
       unfold reduce, col_scale. 
       bdestruct (x0 <? x); bdestruct (y0 <? y);
         bdestruct (y0 =? col); bdestruct (1 + y0 =? col); try lia; easy. 
Qed.

Lemma mcz_reduce_col_same : forall {n m} (T : Matrix n (S m)) (col : nat),
  reduce_col (make_col_zero col T) col = reduce_col T col.
Proof. intros. 
       prep_matrix_equality. 
       unfold reduce_col, make_col_zero. 
       bdestruct (y <? col); bdestruct (1 + y <? col); 
         bdestruct (y =? col); bdestruct (1 + y =? col); try lia; easy. 
Qed.

Lemma mrz_reduce_row_same : forall {n m} (T : Matrix (S n) m) (row : nat),
  reduce_row (make_row_zero row T) row = reduce_row T row.
Proof. intros. 
       prep_matrix_equality. 
       unfold reduce_row, make_row_zero. 
       bdestruct (x <? row); bdestruct (1 + x <? row); 
         bdestruct (x =? row); bdestruct (1 + x =? row); try lia; easy. 
Qed.

Lemma col_add_many_reduce_col_same : forall {n m} (T : Matrix n (S m)) (v : Vector (S m))
                                            (col : nat),
  reduce_col (col_add_many col v T) col = reduce_col T col.
Proof. intros. 
       unfold reduce_col, col_add_many.
       prep_matrix_equality. 
       bdestruct (y <? col); bdestruct (1 + y <? col); 
         bdestruct (y =? col); bdestruct (1 + y =? col); try lia; easy. 
Qed.

Lemma row_add_many_reduce_row_same : forall {n m} (T : Matrix (S n) m) (v : Matrix 1 (S n))
                                            (row : nat),
  reduce_row (row_add_many row v T) row = reduce_row T row.
Proof. intros. 
       unfold reduce_row, row_add_many.
       prep_matrix_equality. 
       bdestruct (x <? row); bdestruct (1 + x <? row); 
         bdestruct (x =? row); bdestruct (1 + x =? row); try lia; easy. 
Qed.

Lemma col_wedge_reduce_col_same : forall {n m} (T : Matrix n m) (v : Vector m)
                                         (col : nat),
  reduce_col (col_wedge T v col) col = T.
Proof. intros.
       prep_matrix_equality.
       unfold reduce_col, col_wedge.
       assert (p : (1 + y - 1) = y). lia.
       bdestruct (y <? col); bdestruct (1 + y <? col); 
         bdestruct (y =? col); bdestruct (1 + y =? col); try lia; try easy. 
       all : rewrite p; easy.
Qed.

Lemma row_wedge_reduce_row_same : forall {n m} (T : Matrix n m) (v : Matrix 1 n)
                                         (row : nat),
  reduce_row (row_wedge T v row) row = T.
Proof. intros.
       prep_matrix_equality.
       unfold reduce_row, row_wedge.
       assert (p : (1 + x - 1) = x). lia.
       bdestruct (x <? row); bdestruct (1 + x <? row); 
         bdestruct (x =? row); bdestruct (1 + x =? row); try lia; try easy. 
       all : rewrite p; easy.
Qed.

Lemma col_add_many_reduce_row : forall {n m} (T : Matrix (S n) m) (v : Vector m) (col row : nat),
  col_add_many col v (reduce_row T row) = reduce_row (col_add_many col v T) row.
Proof. intros. 
       prep_matrix_equality. 
       unfold col_add_many, reduce_row, gen_new_vec, scale, get_vec. 
       bdestruct (y =? col); try lia; try easy. 
       bdestruct (x <? row); try lia. 
       apply Cplus_simplify; try easy. 
       do 2 rewrite Msum_Csum.
       apply big_sum_eq_bounded; intros. 
       bdestruct (x <? row); try lia; easy.
       apply Cplus_simplify; try easy. 
       do 2 rewrite Msum_Csum.
       apply big_sum_eq_bounded; intros. 
       bdestruct (x <? row); try lia; easy.
Qed.

Lemma col_swap_same : forall {n m : nat} (S : Matrix n m) (x : nat),
  col_swap S x x = S.
Proof. intros. 
       unfold col_swap. 
       prep_matrix_equality. 
       bdestruct (y =? x); try easy.
       rewrite H; easy.
Qed. 

Lemma row_swap_same : forall {n m : nat} (S : Matrix n m) (x : nat),
  row_swap S x x = S.
Proof. intros. 
       unfold row_swap. 
       prep_matrix_equality. 
       bdestruct (x0 =? x); try easy.
       rewrite H; easy.
Qed. 

Lemma col_swap_diff_order : forall {n m : nat} (S : Matrix n m) (x y : nat),
  col_swap S x y = col_swap S y x.
Proof. intros. 
       prep_matrix_equality. 
       unfold col_swap.
       bdestruct (y0 =? x); bdestruct (y0 =? y); try easy.
       rewrite <- H, <- H0; easy.
Qed.

Lemma row_swap_diff_order : forall {n m : nat} (S : Matrix n m) (x y : nat),
  row_swap S x y = row_swap S y x.
Proof. intros. 
       prep_matrix_equality. 
       unfold row_swap.
       bdestruct (x0 =? x); bdestruct (x0 =? y); try easy.
       rewrite <- H, <- H0; easy.
Qed.

Lemma col_swap_inv : forall {n m : nat} (S : Matrix n m) (x y : nat),
  S = col_swap (col_swap S x y) x y.
Proof. intros. 
       prep_matrix_equality. 
       unfold col_swap.
       bdestruct (y0 =? x); bdestruct (y0 =? y); 
         bdestruct (y =? x); bdestruct (x =? x); bdestruct (y =? y); 
         try easy. 
       all : (try rewrite H; try rewrite H0; try rewrite H1; easy).
Qed.

Lemma row_swap_inv : forall {n m : nat} (S : Matrix n m) (x y : nat),
  S = row_swap (row_swap S x y) x y.
Proof. intros. 
       prep_matrix_equality. 
       unfold row_swap.
       bdestruct (x0 =? x); bdestruct (x0 =? y); 
         bdestruct (y =? x); bdestruct (x =? x); bdestruct (y =? y); 
         try easy. 
       all : (try rewrite H; try rewrite H0; try rewrite H1; easy).
Qed.

Lemma col_swap_get_vec : forall {n m : nat} (S : Matrix n m) (x y : nat),
  get_vec y S = get_vec x (col_swap S x y).
Proof. intros. 
       prep_matrix_equality. 
       unfold get_vec, col_swap. 
       bdestruct (x =? x); bdestruct (x =? y); try lia; try easy.
Qed.

Lemma col_swap_three : forall {n m} (T : Matrix n m) (x y z : nat),
  x <> z -> y <> z -> col_swap T x z = col_swap (col_swap (col_swap T x y) y z) x y.
Proof. intros.
       bdestruct (x =? y).
       rewrite H1, col_swap_same, col_swap_same.
       easy. 
       prep_matrix_equality. 
       unfold col_swap.
       bdestruct (y =? y); bdestruct (y =? x); bdestruct (y =? z); try lia. 
       bdestruct (x =? y); bdestruct (x =? x); bdestruct (x =? z); try lia. 
       bdestruct (z =? y); bdestruct (z =? x); try lia. 
       bdestruct (y0 =? y); bdestruct (y0 =? x); bdestruct (y0 =? z); 
         try lia; try easy.
       rewrite H10.
       easy.
Qed.

Lemma reduce_row_reduce_col : forall {n m} (A : Matrix (S n) (S m)) (i j : nat),
  reduce_col (reduce_row A i) j = reduce_row (reduce_col A j) i.
Proof. intros. 
       prep_matrix_equality. 
       unfold reduce_col, reduce_row.
       bdestruct (y <? j); bdestruct (x <? i); try lia; try easy. 
Qed.
Lemma reduce_col_swap_01 : forall {n} (A : Square (S (S n))),
  reduce_col (reduce_col (col_swap A 0 1) 0) 0 = reduce_col (reduce_col A 0) 0.
Proof. intros. 
       prep_matrix_equality. 
       unfold reduce_col, col_swap.
       bdestruct (y <? 0); bdestruct (1 + y <? 0); try lia. 
       bdestruct (1 + (1 + y) =? 0); bdestruct (1 + (1 + y) =? 1); try lia. 
       easy. 
Qed.

Lemma reduce_reduce_0 : forall {n} (A : Square (S (S n))) (x y : nat),
  x <= y ->
  (reduce (reduce A x 0) y 0) = (reduce (reduce A (S y) 0) x 0).
Proof. intros.
       prep_matrix_equality.
       unfold reduce. 
       bdestruct (y0 <? 0); bdestruct (1 + y0 <? 0); try lia. 
       bdestruct (x0 <? y); bdestruct (x0 <? S y); bdestruct (x0 <? x); 
         bdestruct (1 + x0 <? S y); bdestruct (1 + x0 <? x); 
         try lia; try easy.
Qed.     

Lemma col_add_split : forall {n} (A : Square (S n)) (i : nat) (c : C),
  col_add A 0 i c = col_wedge (reduce_col A 0) (get_vec 0 A .+ c.* get_vec i A) 0.
Proof. intros. 
       prep_matrix_equality. 
       unfold col_add, col_wedge, reduce_col, get_vec, Mplus, scale.
       bdestruct (y =? 0); try lia; simpl. 
       rewrite H; easy.
       replace (S (y - 1)) with y by lia. 
       easy.
Qed.

Lemma col_swap_col_add_Si : forall {n} (A : Square n) (i j : nat) (c : C),
  i <> 0 -> i <> j -> col_swap (col_add (col_swap A j 0) 0 i c) j 0 = col_add A j i c.
Proof. intros. 
       bdestruct (j =? 0).
       - rewrite H1.
         do 2 rewrite col_swap_same; easy.
       - prep_matrix_equality. 
         unfold col_swap, col_add.
         bdestruct (y =? j); bdestruct (j =? j); try lia; simpl. 
         destruct j; try lia. 
         bdestruct (i =? S j); bdestruct (i =? 0); try lia.  
         rewrite H2; easy.
         bdestruct (y =? 0); bdestruct (j =? 0); try easy. 
         rewrite H4; easy. 
Qed.

Lemma col_swap_col_add_0 : forall {n} (A : Square n) (j : nat) (c : C),
  j <> 0 -> col_swap (col_add (col_swap A j 0) 0 j c) j 0 = col_add A j 0 c.
Proof. intros. 
       prep_matrix_equality. 
       unfold col_swap, col_add.
       bdestruct (y =? j); bdestruct (j =? j); bdestruct (0 =? j); try lia; simpl. 
       rewrite H0; easy.
       bdestruct (y =? 0); bdestruct (j =? 0); try easy. 
       rewrite H3; easy.
Qed.

Lemma col_swap_end_reduce_col_hit : forall {n m : nat} (T : Matrix n (S (S m))) (i : nat),
  i <= m -> col_swap (reduce_col T i) m i = reduce_col (col_swap T (S m) (S i)) i.
Proof. intros.
       prep_matrix_equality. 
       unfold reduce_col, col_swap. 
       bdestruct (i <? i); bdestruct (m <? i); bdestruct (y =? m); bdestruct (y =? i); 
         bdestruct (y <? i); bdestruct (1 + y =? S m); try lia; try easy. 
       bdestruct (1 + y =? S i); try lia; easy.
       bdestruct (y =? S m); bdestruct (y =? S i); try lia; easy. 
       bdestruct (1 + y =? S i); try lia; easy.
Qed.

Lemma col_swap_reduce_row : forall {n m : nat} (S : Matrix (S n) m) (x y row : nat),
  col_swap (reduce_row S row) x y = reduce_row (col_swap S x y) row.
Proof. intros. 
       prep_matrix_equality. 
       unfold col_swap, reduce_row. 
       bdestruct (y0 =? x); bdestruct (x0 <? row); bdestruct (y0 =? y); try lia; easy. 
Qed.

Lemma col_scale_inv : forall {n m : nat} (S : Matrix n m) (x : nat) (a : C),
  a <> C0 -> S = col_scale (col_scale S x a) x (/ a).
Proof. intros. 
       prep_matrix_equality. 
       unfold col_scale.
       bdestruct (y =? x); try easy.
       rewrite Cmult_assoc.
       rewrite Cinv_l; try lca; easy. 
Qed.

Lemma row_scale_inv : forall {n m : nat} (S : Matrix n m) (x : nat) (a : C),
  a <> C0 -> S = row_scale (row_scale S x a) x (/ a).
Proof. intros. 
       prep_matrix_equality. 
       unfold row_scale.
       bdestruct (x0 =? x); try easy.
       rewrite Cmult_assoc.
       rewrite Cinv_l; try lca; easy. 
Qed.

Lemma col_add_double : forall {n m : nat} (S : Matrix n m) (x : nat) (a : C),
  col_add S x x a = col_scale S x (C1 + a).
Proof. intros. 
       prep_matrix_equality. 
       unfold col_add, col_scale. 
       bdestruct (y =? x).
       - rewrite H; lca. 
       - easy.
Qed.

Lemma row_add_double : forall {n m : nat} (S : Matrix n m) (x : nat) (a : C),
  row_add S x x a = row_scale S x (C1 + a).
Proof. intros. 
       prep_matrix_equality. 
       unfold row_add, row_scale. 
       bdestruct (x0 =? x).
       - rewrite H; lca. 
       - easy.
Qed.

Lemma col_add_swap : forall {n m : nat} (S : Matrix n m) (x y : nat) (a : C),
  col_swap (col_add S x y a) x y = col_add (col_swap S x y) y x a. 
Proof. intros. 
       prep_matrix_equality. 
       unfold col_swap, col_add.
       bdestruct (y0 =? x); bdestruct (y =? x);
         bdestruct (y0 =? y); bdestruct (x =? x); try lia; easy. 
Qed.
       
Lemma row_add_swap : forall {n m : nat} (S : Matrix n m) (x y : nat) (a : C),
  row_swap (row_add S x y a) x y = row_add (row_swap S x y) y x a. 
Proof. intros. 
       prep_matrix_equality. 
       unfold row_swap, row_add.
       bdestruct_all; easy.
Qed.

Lemma col_add_inv : forall {n m : nat} (S : Matrix n m) (x y : nat) (a : C),
  x <> y -> S = col_add (col_add S x y a) x y (-a).
Proof. intros. 
       prep_matrix_equality.
       unfold col_add.
       bdestruct (y0 =? x); bdestruct (y =? x); try lia. 
       lca. easy. 
Qed.

Lemma row_add_inv : forall {n m : nat} (S : Matrix n m) (x y : nat) (a : C),
  x <> y -> S = row_add (row_add S x y a) x y (-a).
Proof. intros. 
       prep_matrix_equality.
       unfold row_add.
       bdestruct (x0 =? x); bdestruct (y =? x); try lia. 
       lca. easy. 
Qed.

Lemma mat_equiv_make_WF : forall {n m} (T : Matrix n m),
  T == make_WF T.
Proof. unfold make_WF, mat_equiv; intros. 
       bdestruct (i <? n); bdestruct (j <? m); try lia; easy.
Qed.

Lemma eq_make_WF : forall {n m} (T : Matrix n m),
  WF_Matrix T -> T = make_WF T.
Proof. intros. 
       apply mat_equiv_eq; auto with wf_db.
       apply mat_equiv_make_WF.
Qed.

Lemma col_swap_make_WF : forall {n m} (T : Matrix n m) (x y : nat),
  x < m -> y < m -> col_swap (make_WF T) x y = make_WF (col_swap T x y).
Proof. intros.
       unfold make_WF, col_swap. 
       prep_matrix_equality.
       bdestruct_all; try easy. 
Qed.

Lemma col_scale_make_WF : forall {n m} (T : Matrix n m) (x : nat) (c : C),
  col_scale (make_WF T) x c = make_WF (col_scale T x c).
Proof. intros.
       unfold make_WF, col_scale. 
       prep_matrix_equality.
       bdestruct_all; try easy; lca. 
Qed.

Lemma col_add_make_WF : forall {n m} (T : Matrix n m) (x y : nat) (c : C),
  x < m -> y < m -> col_add (make_WF T) x y c = make_WF (col_add T x y c).
Proof. intros.
       unfold make_WF, col_add. 
       prep_matrix_equality.
       bdestruct_all; try easy; lca. 
Qed.

Lemma Mmult_make_WF : forall {n m o} (A : Matrix n m) (B : Matrix m o),
  make_WF A × make_WF B = make_WF (A × B).
Proof. intros. 
       apply mat_equiv_eq; auto with wf_db.
       unfold mat_equiv; intros. 
       unfold make_WF, Mmult.
       bdestruct (i <? n); bdestruct (j <? o); try lia; simpl. 
       apply big_sum_eq_bounded; intros. 
       bdestruct (x <? m); try lia; easy. 
Qed.

Lemma gen_new_vec_0 : forall {n m} (T : Matrix n m) (as' : Vector m),
  as' == Zero -> gen_new_vec n m T as' = Zero.
Proof. intros.
       unfold mat_equiv, gen_new_vec in *.
       prep_matrix_equality.
       rewrite Msum_Csum.
       unfold Zero in *.
       apply (@big_sum_0_bounded C C_is_monoid); intros. 
       rewrite H; try lia. 
       rewrite Mscale_0_l.
       easy.
Qed.

Lemma gen_new_row_0 : forall {n m} (T : Matrix n m) (as' : Matrix 1 n),
  as' == Zero -> gen_new_row n m T as' = Zero.
Proof. intros.
       unfold mat_equiv, gen_new_row in *.
       prep_matrix_equality.
       rewrite Msum_Csum.
       unfold Zero in *.
       apply (@big_sum_0_bounded C C_is_monoid); intros. 
       rewrite H; try lia. 
       rewrite Mscale_0_l.
       easy.
Qed.

Lemma col_add_many_0 : forall {n m} (col : nat) (T : Matrix n m) (as' : Vector m),
  as' == Zero -> T = col_add_many col as' T.
Proof. intros. 
       unfold col_add_many in *.
       prep_matrix_equality.
       bdestruct (y =? col); try easy.
       rewrite gen_new_vec_0; try easy.
       unfold Zero; lca. 
Qed.

Lemma row_add_many_0 : forall {n m} (row : nat) (T : Matrix n m) (as' : Matrix 1 n),
  as' == Zero -> T = row_add_many row as' T.
Proof. intros. 
       unfold row_add_many in *.
       prep_matrix_equality. 
       bdestruct (x =? row); try easy.
       rewrite gen_new_row_0; try easy.
       unfold Zero; lca. 
Qed.

Lemma gen_new_vec_mat_equiv : forall {n m} (T : Matrix n m) (as' bs : Vector m),
  as' == bs -> gen_new_vec n m T as' = gen_new_vec n m T bs.
Proof. unfold mat_equiv, gen_new_vec; intros.
       prep_matrix_equality.
       do 2 rewrite Msum_Csum.
       apply big_sum_eq_bounded; intros. 
       rewrite H; try lia. 
       easy.
Qed.

Lemma gen_new_row_mat_equiv : forall {n m} (T : Matrix n m) (as' bs : Matrix 1 n),
  as' == bs -> gen_new_row n m T as' = gen_new_row n m T bs.
Proof. unfold mat_equiv, gen_new_row; intros.
       prep_matrix_equality.
       do 2 rewrite Msum_Csum.
       apply big_sum_eq_bounded; intros. 
       rewrite H; try lia. 
       easy.
Qed.

Lemma col_add_many_mat_equiv : forall {n m} (col : nat) (T : Matrix n m) (as' bs : Vector m),
  as' == bs -> col_add_many col as' T = col_add_many col bs T.
Proof. intros. 
       unfold col_add_many.
       rewrite (gen_new_vec_mat_equiv _ as' bs); easy.
Qed.

Lemma row_add_many_mat_equiv : forall {n m} (row : nat) (T : Matrix n m) (as' bs : Matrix 1 n),
  as' == bs -> row_add_many row as' T = row_add_many row bs T.
Proof. intros. 
       unfold row_add_many.
       rewrite (gen_new_row_mat_equiv _ as' bs); easy.
Qed.

Lemma col_add_each_0 : forall {n m} (col : nat) (T : Matrix n m) (v : Matrix 1 m),
  v = Zero -> T = col_add_each col v T.
Proof. intros. 
       rewrite H.
       unfold col_add_each.
       rewrite Mmult_0_r.
       rewrite Mplus_0_r.
       easy. 
Qed.

Lemma row_add_each_0 : forall {n m} (row : nat) (T : Matrix n m) (v : Vector n),
  v = Zero -> T = row_add_each row v T.
Proof. intros. 
       rewrite H.
       unfold row_add_each.
       rewrite Mmult_0_l.
       rewrite Mplus_0_r.
       easy. 
Qed.

(* allows for induction on col_add_many *)
Lemma col_add_many_col_add : forall {n m} (col e : nat) (T : Matrix n m) (as' : Vector m),
  col <> e -> e < m -> as' col 0 = C0 ->
  col_add_many col as' T = 
  col_add (col_add_many col (make_row_zero e as') T) col e (as' e 0).
Proof. intros. 
       unfold col_add_many, col_add, gen_new_vec.
       prep_matrix_equality.
       bdestruct (y =? col); try easy.
       bdestruct (e =? col); try lia.
       rewrite <- Cplus_assoc.
       apply Cplus_simplify; try easy.
       assert (H' : m = e + (m - e)). lia. 
       rewrite H'.
       do 2 rewrite Msum_Csum. 
       rewrite big_sum_sum.
       rewrite big_sum_sum.
       rewrite <- Cplus_assoc.
       apply Cplus_simplify.
       apply big_sum_eq_bounded; intros.
       unfold make_row_zero.
       bdestruct (x0 =? e); try lia; easy. 
       destruct (m - e); try lia. 
       do 2 rewrite <- big_sum_extend_l.
       unfold make_row_zero.
       bdestruct (e + 0 =? e); try lia. 
       unfold scale.
       rewrite Cmult_0_l, Cplus_0_l.
       rewrite Cplus_comm.
       apply Cplus_simplify.
       apply big_sum_eq_bounded; intros.
       bdestruct (e + S x0 =? e); try lia; easy.
       unfold get_vec. simpl. 
       rewrite Nat.add_0_r; easy.
Qed.

(* shows that we can eliminate a column in a matrix using col_add_many *)
Lemma col_add_many_cancel : forall {n m} (T : Matrix n (S m)) (as' : Vector (S m)) (col : nat),
  col < (S m) -> as' col 0 = C0 ->
  (reduce_col T col) × (reduce_row as' col) = -C1 .* (get_vec col T) -> 
  (forall i : nat, (col_add_many col as' T) i col = C0).
Proof. intros. 
       unfold col_add_many, gen_new_vec.
       bdestruct (col =? col); try lia. 
       rewrite Msum_Csum. 
       assert (H' : (big_sum (fun x : nat => (as' x 0 .* get_vec x T) i 0) (S m) = 
                     (@Mmult n m 1 (reduce_col T col) (reduce_row as' col)) i 0)%C).
       { unfold Mmult.
         replace (S m) with (col + (S (m - col))) by lia; rewrite big_sum_sum.
         rewrite <- (Nat.sub_add col m);
           try rewrite (Nat.add_comm (m - col) col);
           try lia; rewrite big_sum_sum.
         apply Cplus_simplify. 
         apply big_sum_eq_bounded; intros. 
         unfold get_vec, scale, reduce_col, reduce_row. 
         bdestruct (x <? col); simpl; try lia; lca.
         rewrite (Nat.add_comm col (m - col)).
         rewrite (Nat.sub_add col m), <- big_sum_extend_l, Nat.add_0_r, H0; try lia. 
         unfold scale; rewrite Cmult_0_l, Cplus_0_l.
         apply big_sum_eq_bounded; intros. 
         unfold get_vec, scale, reduce_col, reduce_row. 
         bdestruct (col + x <? col); simpl; try lia.
         assert (p3 : (col + S x) = (S (col + x))). lia.
         rewrite p3. lca. }
       rewrite H', H1.
       unfold scale, get_vec. 
       bdestruct (0 =? 0); try lia. 
       lca.
Qed.

Lemma col_add_many_inv : forall {n m} (S : Matrix n m) (col : nat) (as' : Vector m),
  as' col 0 = C0 -> S = col_add_many col (-C1 .* as') (col_add_many col as' S).
Proof. intros. 
       unfold col_add_many, gen_new_vec.
       prep_matrix_equality. 
       bdestruct (y =? col); try easy.
       rewrite <- (Cplus_0_r (S x y)).
       rewrite <- Cplus_assoc.
       apply Cplus_simplify; try lca.
       do 2 rewrite Msum_Csum.
       rewrite <- (@big_sum_plus Complex.C _ _ C_is_comm_group).
       rewrite (@big_sum_0_bounded C C_is_monoid); try lca.
       intros. 
       unfold get_vec, scale.
       bdestruct (0 =? 0); bdestruct (x0 =? col); try lia; try lca.
       rewrite Msum_Csum.
       bdestruct (0 =? 0); try lia. 
       rewrite H3, H. lca.
Qed.

(* like above, allows for induction on col_add_each *)
Lemma col_add_each_col_add : forall {n m} (col e : nat) (S : Matrix n m) (as' : Matrix 1 m),
  col <> e -> (forall x, as' x col = C0) ->
              col_add_each col as' S = 
              col_add (col_add_each col (make_col_zero e as') S) e col (as' 0 e).
Proof. intros.
       prep_matrix_equality.
       unfold col_add_each, col_add, make_col_zero, Mmult, Mplus, get_vec, big_sum.
       bdestruct (y =? col); bdestruct (y =? e); bdestruct (col =? e); 
         bdestruct (e =? e); bdestruct (0 =? 0); try lia; try lca. 
       rewrite H0. 
       rewrite H2. lca.
Qed.

Lemma row_add_each_row_add : forall {n m} (row e : nat) (S : Matrix n m) (as' : Vector n),
  row <> e -> (forall y, as' row y = C0) ->
              row_add_each row as' S = 
              row_add (row_add_each row (make_row_zero e as') S) e row (as' e 0).
Proof. intros.
       prep_matrix_equality.
       unfold row_add_each, row_add, make_row_zero, Mmult, Mplus, get_row, big_sum.
       bdestruct (x =? row); bdestruct (x =? e); bdestruct (row =? e); 
         bdestruct (e =? e); bdestruct (0 =? 0); try lia; try lca. 
       rewrite H0. 
       rewrite H2. lca.
Qed.

(* must use make_col_zero here instead of just as' col 0 = C0, since def requires stronger hyp *)
Lemma col_add_each_inv : forall {n m} (col : nat) (as' : Matrix 1 m) (T : Matrix n m),
  T = col_add_each col (make_col_zero col (-C1 .* as')) 
                   (col_add_each col (make_col_zero col as') T).
Proof. intros. 
       prep_matrix_equality. 
       unfold col_add_each, make_col_zero, Mmult, Mplus, get_vec, scale.
       simpl. bdestruct (y =? col); bdestruct (col =? col); try lia; try lca. 
Qed.

Lemma row_add_each_inv : forall {n m} (row : nat) (as' : Vector n) (T : Matrix n m),
  T = row_add_each row (make_row_zero row (-C1 .* as')) 
                   (row_add_each row (make_row_zero row as') T).
Proof. intros. 
       prep_matrix_equality. 
       unfold row_add_each, make_row_zero, Mmult, Mplus, get_row, scale.
       simpl. bdestruct (x =? row); bdestruct (row =? row); try lia; try lca. 
Qed.


(* we can show that we get from col_XXX to row_XXX via transposing *)
(* helpful, since we can bootstrap many lemmas on cols for rows *)
Lemma get_vec_transpose : forall {n m} (A : Matrix n m) (i : nat),
  (get_vec i A)⊤ = get_row i (A⊤).
Proof. intros. 
       prep_matrix_equality. 
       unfold get_vec, get_row, transpose. 
       easy.
Qed.

Lemma get_row_transpose : forall {n m} (A : Matrix n m) (i : nat),
  (get_row i A)⊤ = get_vec i (A⊤).
Proof. intros. 
       prep_matrix_equality. 
       unfold get_vec, get_row, transpose. 
       easy.
Qed.

Lemma col_swap_transpose : forall {n m} (A : Matrix n m) (x y : nat),
  (col_swap A x y)⊤ = row_swap (A⊤) x y.
Proof. intros. 
       prep_matrix_equality. 
       unfold row_swap, col_swap, transpose. 
       easy. 
Qed.

Lemma row_swap_transpose : forall {n m} (A : Matrix n m) (x y : nat),
  (row_swap A x y)⊤ = col_swap (A⊤) x y.
Proof. intros. 
       prep_matrix_equality. 
       unfold row_swap, col_swap, transpose. 
       easy. 
Qed.

Lemma col_scale_transpose : forall {n m} (A : Matrix n m) (x : nat) (a : C),
  (col_scale A x a)⊤ = row_scale (A⊤) x a.
Proof. intros. 
       prep_matrix_equality. 
       unfold row_scale, col_scale, transpose. 
       easy. 
Qed.

Lemma row_scale_transpose : forall {n m} (A : Matrix n m) (x : nat) (a : C),
  (row_scale A x a)⊤ = col_scale (A⊤) x a.
Proof. intros. 
       prep_matrix_equality. 
       unfold row_scale, col_scale, transpose. 
       easy. 
Qed.

Lemma col_add_transpose : forall {n m} (A : Matrix n m) (col to_add : nat) (a : C),
  (col_add A col to_add a)⊤ = row_add (A⊤) col to_add a.
Proof. intros. 
       prep_matrix_equality. 
       unfold row_add, col_add, transpose. 
       easy. 
Qed.

Lemma row_add_transpose : forall {n m} (A : Matrix n m) (row to_add : nat) (a : C),
  (row_add A row to_add a)⊤ = col_add (A⊤) row to_add a.
Proof. intros. 
       prep_matrix_equality. 
       unfold row_add, col_add, transpose. 
       easy. 
Qed.

Lemma col_add_many_transpose : forall {n m} (A : Matrix n m) (col : nat) (as' : Vector m),
  (col_add_many col as' A)⊤ = row_add_many col (as'⊤) (A⊤).
Proof. intros. 
       prep_matrix_equality. 
       unfold row_add_many, col_add_many, transpose. 
       bdestruct (x =? col); try easy. 
       apply Cplus_simplify; try easy.
       unfold gen_new_vec, gen_new_row, get_vec, get_row, scale.
       do 2 rewrite Msum_Csum.
       apply big_sum_eq_bounded; intros. 
       easy. 
Qed.

Lemma row_add_many_transpose : forall {n m} (A : Matrix n m) (row : nat) (as' : Matrix 1 n),
  (row_add_many row as' A)⊤ = col_add_many row (as'⊤) (A⊤).
Proof. intros. 
       prep_matrix_equality. 
       unfold row_add_many, col_add_many, transpose. 
       bdestruct (y =? row); try easy. 
       apply Cplus_simplify; try easy.
       unfold gen_new_vec, gen_new_row, get_vec, get_row, scale.
       do 2 rewrite Msum_Csum.
       apply big_sum_eq_bounded; intros. 
       easy. 
Qed.

Lemma col_add_each_transpose : forall {n m} (A : Matrix n m) (col : nat) (as' : Matrix 1 m),
  (col_add_each col as' A)⊤ = row_add_each col (as'⊤) (A⊤).
Proof. intros. 
       unfold row_add_each, col_add_each. 
       rewrite Mplus_transpose.
       rewrite Mmult_transpose. 
       rewrite get_vec_transpose. 
       easy.
Qed.

Lemma row_add_each_transpose : forall {n m} (A : Matrix n m) (row : nat) (as' : Vector n),
  (row_add_each row as' A)⊤ = col_add_each row (as'⊤) (A⊤).
Proof. intros. 
       unfold row_add_each, col_add_each. 
       rewrite Mplus_transpose.
       rewrite Mmult_transpose. 
       rewrite get_row_transpose. 
       easy.
Qed.




(** the idea is to show that col operations correspond to multiplication by special matrices. *)
(** Thus, we show that the col ops all satisfy various multiplication rules *)
Lemma swap_preserves_mul_lt : forall {n m o} (A : Matrix n m) (B : Matrix m o) (x y : nat),
  x < y -> x < m -> y < m -> A × B = (col_swap A x y) × (row_swap B x y).
Proof. intros. 
       prep_matrix_equality. 
       unfold Mmult. 
       bdestruct (x <? m); try lia.
       rewrite <- (Nat.sub_add x m);
         try rewrite (Nat.add_comm (m - x) x); try lia.
       do 2 rewrite big_sum_sum. 
       apply Cplus_simplify. 
       apply big_sum_eq_bounded.
       intros. 
       unfold col_swap, row_swap.
       bdestruct (x1 =? x); bdestruct (x1 =? y); try lia; try easy.   
       destruct (m - x) as [| x'] eqn:E; try lia. 
       do 2 rewrite <- big_sum_extend_l.
       rewrite Cplus_comm.
       rewrite (Cplus_comm (col_swap A x y x0 (x + 0)%nat * row_swap B x y (x + 0)%nat y0)%C _).
       bdestruct ((y - x - 1) <? x'); try lia.  
       rewrite <- (Nat.sub_add (y - x - 1) x');
         try rewrite (Nat.add_comm (x' - (y - x - 1)) (y - x - 1));
         try lia. 
       do 2 rewrite big_sum_sum.
       do 2 rewrite <- Cplus_assoc.
       apply Cplus_simplify. 
       apply big_sum_eq_bounded.
       intros. 
       unfold col_swap, row_swap.
       bdestruct (x + S x1 =? x); bdestruct (x + S x1 =? y); try lia; try easy. 
       destruct (x' - (y - x - 1)) as [| x''] eqn:E1; try lia. 
       do 2 rewrite <- big_sum_extend_l.
       rewrite Cplus_comm.
       rewrite (Cplus_comm _ (col_swap A x y x0 (x + 0)%nat * row_swap B x y (x + 0)%nat y0)%C). 
       do 2 rewrite Cplus_assoc.
       apply Cplus_simplify.
       do 2 rewrite <- plus_n_O. 
       unfold col_swap, row_swap.
       bdestruct (x + S (y - x - 1) =? x); bdestruct (x + S (y - x - 1) =? y); 
         bdestruct (x =? x); try lia.
       rewrite H5. lca. 
       apply big_sum_eq_bounded.
       intros. 
       unfold col_swap, row_swap.
       bdestruct (x + S (y - x - 1 + S x1) =? x); 
         bdestruct (x + S (y - x - 1 + S x1) =? y); try lia; try easy.
Qed.           

Lemma swap_preserves_mul : forall {n m o} (A : Matrix n m) (B : Matrix m o) (x y : nat),
  x < m -> y < m -> A × B = (col_swap A x y) × (row_swap B x y).
Proof. intros. bdestruct (x <? y).
       - apply swap_preserves_mul_lt; easy.
       - destruct H1.
         + rewrite col_swap_same, row_swap_same; easy.
         + rewrite col_swap_diff_order, row_swap_diff_order. 
           apply swap_preserves_mul_lt; lia.
Qed.

Lemma scale_preserves_mul : forall {n m o} (A : Matrix n m) (B : Matrix m o) (x : nat) (a : C),
  A × (row_scale B x a) = (col_scale A x a) × B.
Proof. intros. 
       prep_matrix_equality. 
       unfold Mmult. 
       apply big_sum_eq_bounded.
       intros. 
       unfold col_scale, row_scale.
       bdestruct (x1 =? x).
       - rewrite Cmult_assoc.
         lca. 
       - reflexivity. 
Qed.        

Lemma add_preserves_mul_lt : forall {n m o} (A : Matrix n m) (B : Matrix m o) 
                                                (x y : nat) (a : C),
   x < y -> x < m -> y < m -> A × (row_add B y x a) = (col_add A x y a) × B.
Proof. intros.  
       prep_matrix_equality. 
       unfold Mmult.   
       bdestruct (x <? m); try lia.
       rewrite <- (Nat.sub_add x m);
         try rewrite (Nat.add_comm (m - x) x);
         try lia.
       do 2 rewrite big_sum_sum.
       apply Cplus_simplify. 
       apply big_sum_eq_bounded.
       intros. 
       unfold row_add, col_add.
       bdestruct (x1 =? y); bdestruct (x1 =? x); try lia; easy. 
       destruct (m - x) as [| x'] eqn:E; try lia. 
       do 2 rewrite <- big_sum_extend_l.
       rewrite Cplus_comm. 
       rewrite (Cplus_comm (col_add A x y a x0 (x + 0)%nat * B (x + 0)%nat y0)%C _).
       bdestruct ((y - x - 1) <? x'); try lia.  
       rewrite <- (Nat.sub_add (y - x - 1) x');
         try rewrite (Nat.add_comm (x' - (y - x - 1)) (y - x - 1));
         try lia. 
       do 2 rewrite big_sum_sum.
       do 2 rewrite <- Cplus_assoc.
       apply Cplus_simplify. 
       apply big_sum_eq_bounded.
       intros. 
       unfold row_add, col_add.
       bdestruct (x + S x1 =? y); bdestruct (x + S x1 =? x); try lia; easy. 
       destruct (x' - (y - x - 1)) as [| x''] eqn:E1; try lia. 
       do 2 rewrite <- big_sum_extend_l.
       rewrite Cplus_comm. 
       rewrite (Cplus_comm _ (col_add A x y a x0 (x + 0)%nat * B (x + 0)%nat y0)%C).
       do 2 rewrite Cplus_assoc.
       apply Cplus_simplify. 
       unfold row_add, col_add.
       do 2 rewrite <- plus_n_O.
       bdestruct (x =? y); bdestruct (x =? x); 
         bdestruct (x + S (y - x - 1) =? y); bdestruct (x + S (y - x - 1) =? x); try lia. 
       rewrite H6. lca. 
       apply big_sum_eq_bounded.
       intros. 
       unfold row_add, col_add.
       bdestruct (x + S (y - x - 1 + S x1) =? y); 
         bdestruct (x + S (y - x - 1 + S x1) =? x); try lia; easy. 
Qed.

Lemma add_preserves_mul : forall {n m o} (A : Matrix n m) (B : Matrix m o) 
                                             (x y : nat) (a : C),
   x < m -> y < m -> A × (row_add B y x a) = (col_add A x y a) × B.
Proof. intros. bdestruct (x <? y).
       - apply add_preserves_mul_lt; easy.
       - destruct H1.
         + rewrite col_add_double, row_add_double. 
           apply scale_preserves_mul.
         + rewrite (swap_preserves_mul A _ y (S m0)); try easy.
           rewrite (swap_preserves_mul _ B (S m0) y); try easy.
           rewrite col_add_swap.
           rewrite row_add_swap.
           rewrite row_swap_diff_order.
           rewrite col_swap_diff_order.
           apply add_preserves_mul_lt; lia. 
Qed.


(* used for the below induction where basically we may have to go from n to (n + 2) *)
(* might want to move this somewhere else. cool technique though! Maybe coq already has something like this  *) 
Definition skip_count (skip i : nat) : nat :=
  if (i <? skip) then i else S i.

Lemma skip_count_le : forall (skip i : nat),
  i <= skip_count skip i.
Proof. intros; unfold skip_count. 
       bdestruct (i <? skip); lia.
Qed.

Lemma skip_count_not_skip : forall (skip i : nat),
  skip <> skip_count skip i. 
Proof. intros; unfold skip_count. 
       bdestruct (i <? skip); try lia. 
Qed.

Lemma skip_count_mono : forall (skip i1 i2 : nat),
  i1 < i2 -> skip_count skip i1 < skip_count skip i2.
Proof. intros; unfold skip_count. 
       bdestruct (i1 <? skip); bdestruct (i2 <? skip); try lia. 
Qed.

Lemma cam_ca_switch : forall {n m} (T : Matrix n m) (as' : Vector m) (col to_add : nat) (c : C),
  as' col 0 = C0 -> to_add <> col -> 
  col_add (col_add_many col as' T) col to_add c = 
  col_add_many col as' (col_add T col to_add c).
Proof. intros. 
       prep_matrix_equality. 
       unfold col_add, col_add_many.
       bdestruct (y =? col); try lia; try easy.
       repeat rewrite <- Cplus_assoc.
       apply Cplus_simplify; try easy.
       bdestruct (to_add =? col); try lia.
       rewrite Cplus_comm.
       apply Cplus_simplify; try easy. 
       unfold gen_new_vec.
       do 2 rewrite Msum_Csum.
       apply big_sum_eq_bounded; intros. 
       unfold get_vec, scale; simpl.
       bdestruct (x0 =? col); try lca. 
       rewrite H4, H; lca.
Qed.

Lemma col_add_many_preserves_mul_some : forall (n m o e col : nat) 
                                               (A : Matrix n m) (B : Matrix m o) (v : Vector m),
  WF_Matrix v -> (skip_count col e) < m -> col < m -> 
  (forall i : nat, (skip_count col e) < i -> v i 0 = C0) -> v col 0 = C0 ->
  A × (row_add_each col v B) = (col_add_many col v A) × B.  
Proof. induction e as [| e].
       - intros.
         destruct m; try easy.
         rewrite (col_add_many_col_add col (skip_count col 0) _ _); try easy.
         rewrite <- (col_add_many_0 col A (make_row_zero (skip_count col 0) v)).
         rewrite (row_add_each_row_add col (skip_count col 0) _ _); try easy.
         rewrite <- (row_add_each_0 col B (make_row_zero (skip_count col 0) v)).
         apply add_preserves_mul; try easy.
         apply mat_equiv_eq; auto with wf_db.
         unfold mat_equiv; intros. 
         destruct j; try lia. 
         unfold make_row_zero.
         bdestruct (i =? skip_count col 0); try lia; try easy. 
         destruct col; destruct i; try easy.
         rewrite H2; try easy. unfold skip_count in *. 
         bdestruct (0 <? 0); lia. 
         rewrite H2; try easy.
         unfold skip_count in *. simpl; lia. 
         all : try apply skip_count_not_skip.
         intros. destruct y; try easy.
         apply H; lia. 
         unfold mat_equiv, make_row_zero; intros. 
         destruct j; try lia. 
         bdestruct (i =? skip_count col 0); try lia; try easy. 
         destruct col; try easy.
         destruct i; try easy.
         rewrite H2; try easy. 
         unfold skip_count in *; simpl in *; lia. 
         rewrite H2; try easy.
         unfold skip_count in *; simpl in *; lia. 
       - intros. 
         destruct m; try easy.
         rewrite (col_add_many_col_add col (skip_count col (S e)) _ _); try easy.
         rewrite (row_add_each_row_add col (skip_count col (S e)) _ _); try easy.
         rewrite add_preserves_mul; try easy.
         rewrite cam_ca_switch. 
         rewrite IHe; try easy; auto with wf_db.
         assert (p : e < S e). lia. 
         apply (skip_count_mono col) in p.
         lia. 
         intros.
         unfold make_row_zero.
         bdestruct (i =? skip_count col (S e)); try easy. 
         unfold skip_count in *. 
         bdestruct (e <? col); bdestruct (S e <? col); try lia. 
         all : try (apply H2; lia). 
         bdestruct (i =? col); bdestruct (S e =? col); try lia. 
         rewrite H8; apply H3.
         apply H2. lia. 
         unfold make_row_zero.
         bdestruct (col =? skip_count col (S e)); try easy.
         unfold make_row_zero.
         bdestruct (col =? skip_count col (S e)); try easy.
         assert (H4 := skip_count_not_skip). auto.
         all : try apply skip_count_not_skip.
         intros. 
         destruct y; try easy.
         apply H; lia. 
Qed.

Lemma col_add_many_preserves_mul: forall (n m o col : nat) 
                                               (A : Matrix n m) (B : Matrix m o) (v : Vector m),
  WF_Matrix v -> col < m -> v col 0 = C0 ->
  A × (row_add_each col v B) = (col_add_many col v A) × B.  
Proof. intros. 
       destruct m; try easy.
       destruct m.
       - assert (H' : v = Zero).
         apply mat_equiv_eq; auto with wf_db.
         unfold mat_equiv; intros. 
         destruct i; destruct j; destruct col; try lia; easy.
         rewrite <- col_add_many_0, <- row_add_each_0; try easy.
         rewrite H'; easy.
       - apply (col_add_many_preserves_mul_some _ _ _ m col); try easy.
         unfold skip_count.
         bdestruct (m <? col); lia. 
         intros. 
         unfold skip_count in H2.
         bdestruct (m <? col). 
         bdestruct (col =? (S m)); try lia. 
         bdestruct (i =? (S m)). 
         rewrite H5, <- H4. apply H1.
         apply H; lia. 
         apply H; lia. 
Qed.

(* we can prove col_add_each version much more easily using transpose *)
Lemma col_add_each_preserves_mul: forall (n m o col : nat) (A : Matrix n m) 
                                                         (B : Matrix m o) (v : Matrix 1 m),
  WF_Matrix v -> col < m -> v 0 col = C0 ->
  A × (row_add_many col v B) = (col_add_each col v A) × B.  
Proof. intros. 
       assert (H' : ((B⊤) × (row_add_each col (v⊤) (A⊤)))⊤ = 
                               ((col_add_many col (v⊤) (B⊤)) × (A⊤))⊤).  
       rewrite col_add_many_preserves_mul; auto with wf_db; try easy.
       do 2 rewrite Mmult_transpose in H'. 
       rewrite row_add_each_transpose in H'. 
       rewrite col_add_many_transpose in H'. 
       repeat rewrite transpose_involutive in H'.
       easy. 
Qed.

Lemma col_swap_mult_r : forall {n} (A : Square n) (x y : nat),
  x < n -> y < n -> WF_Matrix A -> 
  col_swap A x y = A × (row_swap (I n) x y).
Proof. intros.
       assert (H2 := (swap_preserves_mul A (row_swap (I n) x y) x y)).
       rewrite <- (Mmult_1_r _ _ (col_swap A x y)); auto with wf_db.
       rewrite H2; try easy.
       rewrite <- (row_swap_inv (I n) x y).
       reflexivity. 
Qed.

Lemma col_scale_mult_r : forall {n} (A : Square n) (x : nat) (a : C),
  WF_Matrix A -> 
  col_scale A x a = A × (row_scale (I n) x a).
Proof. intros. 
       rewrite scale_preserves_mul.
       rewrite Mmult_1_r; auto with wf_db. 
Qed.

Lemma col_add_mult_r : forall {n} (A : Square n) (x y : nat) (a : C),
  x < n -> y < n -> WF_Matrix A -> 
  col_add A x y a = A × (row_add (I n) y x a).
Proof. intros. 
       rewrite add_preserves_mul; auto.
       rewrite Mmult_1_r; auto with wf_db. 
Qed.

Lemma col_add_many_mult_r : forall {n} (A : Square n) (v : Vector n) (col : nat),
  WF_Matrix A -> WF_Matrix v -> col < n -> v col 0 = C0 ->
  col_add_many col v A = A × (row_add_each col v (I n)).
Proof. intros. 
       rewrite col_add_many_preserves_mul; try easy.
       rewrite Mmult_1_r; auto with wf_db.
Qed.

Lemma col_add_each_mult_r : forall {n} (A : Square n) (v : Matrix 1 n) (col : nat),
  WF_Matrix A -> WF_Matrix v -> col < n -> v 0 col = C0 ->
  col_add_each col v A = A × (row_add_many col v (I n)).
Proof. intros. 
       rewrite col_add_each_preserves_mul; try easy.
       rewrite Mmult_1_r; auto with wf_db.
Qed.

(* now we prove facts about the ops on (I n) *)
Lemma col_row_swap_invr_I : forall (n x y : nat), 
  x < n -> y < n -> col_swap (I n) x y = row_swap (I n) x y.
Proof. intros. 
       prep_matrix_equality.
       unfold col_swap, row_swap, I.
       bdestruct_all; try easy.
Qed.

Lemma col_row_scale_invr_I : forall (n x : nat) (c : C), 
  col_scale (I n) x c = row_scale (I n) x c.
Proof. intros. 
       prep_matrix_equality.
       unfold col_scale, row_scale, I.
       bdestruct_all; try easy; lca.
Qed.

Lemma col_row_add_invr_I : forall (n x y : nat) (c : C), 
  x < n -> y < n -> col_add (I n) x y c = row_add (I n) y x c.
Proof. intros. 
       prep_matrix_equality.
       unfold col_add, row_add, I.
       bdestruct_all; try easy; try lca.
Qed.

Lemma row_each_col_many_invr_I : forall (n col : nat) (v : Vector n),
  WF_Matrix v -> col < n -> v col 0 = C0 ->
  row_add_each col v (I n) = col_add_many col v (I n).  
Proof. intros. 
       rewrite <- Mmult_1_r, <- col_add_many_preserves_mul, Mmult_1_l; auto with wf_db. 
Qed.

Lemma row_many_col_each_invr_I : forall (n col : nat) (v : Matrix 1 n),
  WF_Matrix v -> col < n -> v 0 col = C0 ->
  row_add_many col v (I n) = col_add_each col v (I n).  
Proof. intros. 
       rewrite <- Mmult_1_r, <- col_add_each_preserves_mul, Mmult_1_l; auto with wf_db. 
Qed.

Lemma reduce_append_split : forall {n m} (T : Matrix n (S m)), 
  WF_Matrix T -> T = col_append (reduce_col T m) (get_vec m T).
Proof. intros. 
       prep_matrix_equality. 
       unfold col_append, get_vec, reduce_col.
       bdestruct_all; subst; try easy.
       do 2 (rewrite H; try lia); easy. 
Qed.

Lemma smash_zero : forall {n m} (T : Matrix n m) (i : nat),
  WF_Matrix T -> smash T (@Zero n i) = T. 
Proof. intros. 
       prep_matrix_equality.
       unfold smash, Zero. 
       bdestruct (y <? m); try easy.
       rewrite H; try lia; easy.
Qed.

Lemma smash_assoc : forall {n m1 m2 m3}
                           (T1 : Matrix n m1) (T2 : Matrix n m2) (T3 : Matrix n m3),
  smash (smash T1 T2) T3 = smash T1 (smash T2 T3).
Proof. intros. 
       unfold smash.
       prep_matrix_equality.
       bdestruct (y <? m1 + m2); bdestruct (y <? m1); 
         bdestruct (y - m1 <? m2); try lia; try easy.
       assert (H' : y - (m1 + m2) = y - m1 - m2).
       lia. rewrite H'; easy.
Qed.

Lemma smash_append : forall {n m} (T : Matrix n m) (v : Vector n),
  WF_Matrix T -> WF_Matrix v ->
  col_append T v = smash T v.
Proof. intros. 
       unfold smash, col_append, WF_Matrix in *.
       prep_matrix_equality. 
       bdestruct (y =? m); bdestruct (y <? m); try lia; try easy.
       rewrite H1.
       rewrite Nat.sub_diag; easy. 
       rewrite H0, H; try lia; try easy.
Qed.

Lemma smash_reduce : forall {n m1 m2} (T1 : Matrix n m1) (T2 : Matrix n (S m2)),
  reduce_col (smash T1 T2) (m1 + m2) = smash T1 (reduce_col T2 m2).
Proof. intros. 
       prep_matrix_equality. 
       unfold reduce_col, smash. 
       bdestruct (y <? m1 + m2); bdestruct (y <? m1); bdestruct (1 + y <? m1);
         bdestruct (y - m1 <? m2); try lia; try easy.
       assert (H' : 1 + y - m1 = 1 + (y - m1)). lia.  
       rewrite H'; easy.
Qed.

Lemma split_col : forall {n m} (T : Matrix n (S m)), 
  T = smash (get_vec 0 T) (reduce_col T 0).
Proof. intros. 
       prep_matrix_equality. 
       unfold smash, get_vec, reduce_col.
       bdestruct (y <? 1); bdestruct (y =? 0); bdestruct (y - 1 <? 0); try lia; try easy.
       rewrite H0; easy. 
       destruct y; try lia. 
       simpl. assert (H' : y - 0 = y). lia. 
       rewrite H'; easy.
Qed.



(** * Some more lemmas with these new concepts *)

(* We can now show that matrix_equivalence is decidable *)
Lemma vec_equiv_dec : forall {n : nat} (A B : Vector n), 
    { A == B } + { ~ (A == B) }.
Proof. induction n as [| n'].
       - left; easy.
       - intros. destruct (IHn' (reduce_vecn A) (reduce_vecn B)).
         + destruct (Ceq_dec (A n' 0) (B n' 0)).
           * left. 
             unfold mat_equiv in *.
             intros.
             bdestruct (i =? n'); bdestruct (n' <? i); try lia. 
             rewrite H1.
             destruct j.
             apply e. lia.
             apply (m i j) in H0; try lia.
             unfold reduce_vecn in H0.
             bdestruct (i <? n'); try lia; easy.
           * right. unfold not. 
             intros. unfold mat_equiv in H.
             apply n. apply H; lia. 
         + right. 
           unfold not in *. 
           intros. apply n.
           unfold mat_equiv in *.
           intros. unfold reduce_vecn.
           bdestruct (i <? n'); try lia. 
           apply H; lia. 
Qed.

Lemma mat_equiv_dec : forall {n m : nat} (A B : Matrix n m), 
    { A == B } + { ~ (A == B) }.
Proof. induction m as [| m']. intros.  
       - left. easy.
       - intros. destruct (IHm' (reduce_col A m') (reduce_col B m')).
         + destruct (vec_equiv_dec (get_vec m' A) (get_vec m' B)).
           * left. 
             unfold mat_equiv in *.
             intros. 
             bdestruct (j =? m'); bdestruct (m' <? j); try lia.
             ++ apply (m0 i 0) in H.
                do 2 rewrite get_vec_conv in H.
                rewrite H1. easy. lia. 
             ++ apply (m i j) in H.
                unfold reduce_col in H.
                bdestruct (j <? m'); try lia; try easy.
                lia. 
           * right. 
             unfold not, mat_equiv in *.
             intros. apply n0.
             intros. 
             destruct j; try easy.
             do 2 rewrite get_vec_conv.
             apply H; lia.
         + right. 
           unfold not, mat_equiv, reduce_col in *.
           intros. apply n0. 
           intros. 
           bdestruct (j <? m'); try lia.
           apply H; lia.            
Qed.

(* we can also now prove some useful lemmas about nonzero vectors *)
Lemma last_zero_simplification : forall {n : nat} (v : Vector (S n)),
  WF_Matrix v -> v n 0 = C0 -> v = reduce_vecn v.
Proof. intros. unfold reduce_vecn.
       prep_matrix_equality.
       bdestruct (x <? n).
       - easy.
       - unfold WF_Matrix in H.
         destruct H1.
         + destruct y. 
           * rewrite H0, H. reflexivity.
             left. nia. 
           * rewrite H. rewrite H. reflexivity.
             right; nia. right; nia.
         + rewrite H. rewrite H. reflexivity.
           left. nia. left. nia.
Qed.

Lemma zero_reduce : forall {n : nat} (v : Vector (S n)) (x : nat),
  WF_Matrix v -> (v = Zero <-> (reduce_row v x) = Zero /\ v x 0 = C0).
Proof. intros. split.    
       - intros. rewrite H0. split.
         + prep_matrix_equality. unfold reduce_row. 
           bdestruct (x0 <? x); easy. 
         + easy.
       - intros [H0 H1]. 
         prep_matrix_equality.
         unfold Zero.
         bdestruct (x0 =? x).
         + rewrite H2. 
           destruct y; try easy.          
           apply H; lia.
         + bdestruct (x0 <? x). 
           * assert (H' : (reduce_row v x) x0 y = C0). 
             { rewrite H0. easy. }
             unfold reduce_row in H'.
             bdestruct (x0 <? x); try lia; try easy.
           * destruct x0; try lia. 
             assert (H'' : (reduce_row v x) x0 y = C0). 
             { rewrite H0. easy. }
             unfold reduce_row in H''.
             bdestruct (x0 <? x); try lia. 
             rewrite <- H''. easy.
Qed.

Lemma nonzero_vec_nonzero_elem : forall {n} (v : Vector n),
  WF_Matrix v -> v <> Zero -> exists x, v x 0 <> C0.
Proof. induction n as [| n']. 
       - intros. 
         assert (H' : v = Zero).
         { prep_matrix_equality.
           unfold Zero.
           unfold WF_Matrix in H.
           apply H.
           left. lia. }
         easy.
       - intros.   
         destruct (Ceq_dec (v n' 0) C0). 
         + destruct (vec_equiv_dec (reduce_row v n') Zero). 
           * assert (H' := H). 
             apply (zero_reduce _ n') in H'.
             destruct H'.
             assert (H' : v = Zero). 
             { apply H2.
               split. 
               apply mat_equiv_eq; auto with wf_db.
               easy. }
             easy.             
           * assert (H1 : exists x, (reduce_row v n') x 0 <> C0).
             { apply IHn'; auto with wf_db.
               unfold not in *. intros. apply n. 
               rewrite H1. easy. }
             destruct H1. 
             exists x. 
             rewrite (last_zero_simplification v); try easy.    
         + exists n'. 
           apply n.
Qed.

Local Close Scope nat_scope.


(* some inner product lemmas *)
Lemma inner_product_scale_l : forall {n} (u v : Vector n) (c : C),
  ⟨c .* u, v⟩ = c^* * ⟨u,v⟩.
Proof. intros.
       unfold inner_product, scale, adjoint, Mmult.
       rewrite (@big_sum_mult_l C _ _ _ C_is_ring).
       apply big_sum_eq_bounded; intros.
       lca.
Qed.       

Lemma inner_product_scale_r : forall {n} (u v : Vector n) (c : C),
  ⟨u, c .* v⟩ = c * ⟨u,v⟩.
Proof. intros.
       unfold inner_product, scale, adjoint, Mmult.
       rewrite (@big_sum_mult_l C _ _ _ C_is_ring).
       apply big_sum_eq_bounded; intros.
       lca.
Qed.       

Lemma inner_product_plus_l : forall {n} (u v w : Vector n),
  ⟨u .+ v, w⟩ = ⟨u, w⟩ + ⟨v, w⟩.
Proof. intros.
       unfold inner_product, scale, adjoint, Mplus, Mmult.
       rewrite <- (@big_sum_plus C _ _ C_is_comm_group).
       apply big_sum_eq_bounded; intros.
       lca.
Qed.       

Lemma inner_product_plus_r : forall {n} (u v w : Vector n),
  ⟨u, v .+ w⟩ = ⟨u, v⟩ + ⟨u, w⟩.
Proof. intros.
       unfold inner_product, scale, adjoint, Mplus, Mmult.
       rewrite <- (@big_sum_plus C _ _ C_is_comm_group).
       apply big_sum_eq_bounded; intros.
       lca.
Qed.       

Lemma inner_product_big_sum_l : forall {n} (u : Vector n) (f : nat -> Vector n) (k : nat),
  ⟨big_sum f k, u⟩ = big_sum (fun i => ⟨f i, u⟩) k.
Proof. induction k.
       - unfold inner_product; simpl.
         rewrite zero_adjoint_eq, Mmult_0_l; easy.
       - simpl. 
         rewrite inner_product_plus_l, IHk.
         reflexivity.
Qed.       

Lemma inner_product_big_sum_r : forall {n} (u : Vector n) (f : nat -> Vector n) (k : nat),
  ⟨u, big_sum f k⟩ = big_sum (fun i => ⟨u, f i⟩) k.
Proof. induction k.
       - unfold inner_product; simpl.
         rewrite Mmult_0_r; easy.
       - simpl. 
         rewrite inner_product_plus_r, IHk.
         reflexivity.
Qed.       

Lemma inner_product_conj_sym : forall {n} (u v : Vector n),
  ⟨u, v⟩ = ⟨v, u⟩^*.
Proof. intros. 
       unfold inner_product, adjoint, Mmult.
       rewrite (@big_sum_func_distr C C _ C_is_group _ C_is_group).
       apply big_sum_eq_bounded; intros.
       lca.
       intros; lca.
Qed.

Lemma inner_product_mafe_WF_l : forall {n} (u v : Vector n),
  ⟨u, v⟩ = ⟨make_WF u, v⟩.
Proof. intros. 
       unfold inner_product, adjoint, Mmult, make_WF.
       apply big_sum_eq_bounded; intros.
       bdestruct_all; simpl; easy.
Qed.

Lemma inner_product_mafe_WF_r : forall {n} (u v : Vector n),
  ⟨u, v⟩ = ⟨u, make_WF v⟩.
Proof. intros. 
       unfold inner_product, adjoint, Mmult, make_WF.
       apply big_sum_eq_bounded; intros.
       bdestruct_all; simpl; easy.
Qed.

(* Useful to be able to normalize vectors *)
Definition norm {n} (ψ : Vector n) : R :=
  sqrt (fst ⟨ψ,ψ⟩).

Definition normalize {n} (ψ : Vector n) :=
  / (norm ψ) .* ψ.

Lemma norm_scale : forall {n} c (v : Vector n), norm (c .* v) = ((Cmod c) * norm v)%R.
Proof.
  intros n c v.
  unfold norm, inner_product.
  rewrite Mscale_adj.
  rewrite Mscale_mult_dist_l, Mscale_mult_dist_r, Mscale_assoc.
  unfold scale.
  simpl.
  replace (fst c * snd c + - snd c * fst c)%R with 0%R.
  autorewrite with R_db C_db.
  replace (fst c * fst c)%R with (fst c ^ 2)%R by lra.
  replace (snd c * snd c)%R with (snd c ^ 2)%R by lra.
  rewrite sqrt_mult_alt.
  reflexivity.
  apply Rplus_le_le_0_compat; apply pow2_ge_0.
  lra.
Qed.

Lemma normalized_norm_1 : forall {n} (v : Vector n),
  norm v <> 0 -> norm (normalize v) = 1.
Proof. intros. 
       unfold normalize.
       rewrite norm_scale.  
       rewrite Cmod_real. 
       simpl.  
       autorewrite with R_db.
       rewrite Rmult_comm.
       rewrite Rinv_mult_distr; try easy. 
       rewrite <- Rmult_comm.
       rewrite <- Rmult_assoc.
       rewrite Rinv_r; try easy.
       autorewrite with R_db.
       reflexivity. 
       unfold Cinv.
       simpl. 
       autorewrite with R_db.
       rewrite Rinv_mult_distr; try easy. 
       rewrite <- Rmult_assoc.
       rewrite Rinv_r; try easy.
       autorewrite with R_db.
       assert (H' : norm v >= 0).
       { assert (H'' : 0 <= norm v).
         { apply sqrt_pos. }
         lra. }
       destruct H' as [H0 | H0].
       left.
       assert (H1 : 0 < norm v). { lra. }
       apply Rinv_0_lt_compat in H1.
       lra. easy. 
       apply div_real.
       easy. 
Qed. 

Lemma rewrite_norm : forall {d} (ψ : Vector d),
    fst ⟨ψ,ψ⟩ = big_sum (fun i => Cmod (ψ i O) ^ 2)%R d.
Proof.
  intros d ψ. unfold inner_product, Mmult.
  replace (fun y : nat => (ψ† O y * ψ y O)%C) with (fun y : nat => RtoC (Cmod (ψ y O) ^ 2)).
  apply Rsum_big_sum.
  apply functional_extensionality. intros.
  unfold adjoint. rewrite <- Cmod_sqr. symmetry. apply RtoC_pow.
Qed.

Local Open Scope nat_scope.

Lemma norm_real : forall {n} (v : Vector n), snd ⟨v,v⟩ = 0%R. 
Proof. intros. unfold inner_product, Mmult, adjoint.
       rewrite big_sum_snd_0. easy.
       intros. rewrite Cmult_comm.
       rewrite Cmult_conj_real.
       reflexivity.
Qed.

Lemma inner_product_ge_0 : forall {d} (ψ : Vector d),
  (0 <= fst ⟨ψ,ψ⟩)%R.
Proof.
  intros.
  unfold inner_product, Mmult, adjoint.
  apply big_sum_ge_0.
  intro.
  rewrite <- Cmod_sqr.
  simpl.
  autorewrite with R_db.
  apply Rmult_le_pos; apply Cmod_ge_0.
Qed.

(* why does sqrt_pos exist? *)
Lemma norm_ge_0 : forall {d} (ψ : Vector d),
  (0 <= norm ψ)%R.
Proof. intros.
       unfold norm.
       apply sqrt_positivity.
       (* apply sqrt_pos *)
       apply inner_product_ge_0.
Qed.

Lemma norm_squared : forall {d} (ψ : Vector d),
  ((norm ψ) ^2)%R = fst ⟨ ψ, ψ ⟩.
Proof. intros.
       unfold norm.
       rewrite pow2_sqrt; auto.
       apply inner_product_ge_0.
Qed.

(* "Quick" proof of |x| = 0 iff x = 0 *)
Lemma inner_product_zero_iff_zero : forall {n} (v : Vector n),
  WF_Matrix v -> (⟨v,v⟩ = C0 <-> v = Zero). 
Proof. intros. split. 
       - intros. 
         destruct (mat_equiv_dec v Zero).
         apply mat_equiv_eq; try easy.
         assert (H' : v <> Zero). 
         { unfold not; intros. 
           apply n0. rewrite H1.
           easy. }
         apply nonzero_vec_nonzero_elem in H'; try easy.
         destruct H'. 
         unfold WF_Matrix in H.
         bdestruct (x <? n).
         assert (H0' := Rle_0_sqr).  
         unfold Rsqr in H0'. 
         assert (H' : (0 < fst (inner_product v v))%R).
         { unfold inner_product.
           unfold Mmult. 
           apply big_sum_gt_0.
           unfold adjoint. 
           intros.
           rewrite <- Cmod_sqr.
           simpl. autorewrite with R_db.
           apply H0'. 
           exists x. split; try easy.
           unfold adjoint. 
           rewrite <- Cmod_sqr.
           simpl. autorewrite with R_db.
           assert (H' : (0 <= Cmod (v x 0%nat) * Cmod (v x 0%nat))%R). 
           { apply H0'. } 
           destruct H'; try easy. 
           assert (H' := Rsqr_0_uniq).
           unfold Rsqr in H'. 
           assert (H'' : forall a b : R, a = b -> b = a). { easy. }
           apply H'' in H3. 
           apply H' in H3.
           apply Cmod_gt_0 in H1.
           rewrite H3 in H1.
           lra. }
         rewrite H0 in H'. 
         simpl in H'. lra. 
         assert (H' : v x O = C0).
         { apply H. left; easy. }
         rewrite H' in H1; easy. 
       - intros. 
         unfold inner_product.  
         rewrite H0. 
         rewrite Mmult_0_r. 
         easy.
Qed.

Lemma norm_zero_iff_zero : forall {n} (v : Vector n),
  WF_Matrix v -> (norm v = 0%R <-> v = Zero). 
Proof. intros. split. 
       - intros. 
         unfold norm in H0.
         apply inner_product_zero_iff_zero in H.
         unfold inner_product in H. 
         apply sqrt_eq_0 in H0.
         apply H. 
         apply c_proj_eq.
         apply H0.
         apply norm_real.
         apply inner_product_ge_0.
       - intros. 
         rewrite H0. 
         unfold norm, inner_product.
         rewrite Mmult_0_r. 
         simpl. apply sqrt_0. 
Qed.     

Local Close Scope nat_scope.

(* We can now prove Cauchy-Schwartz for vectors with inner_product *)
Lemma CS_key_lemma : forall {n} (u v : Vector n),
  fst ⟨ (⟨v,v⟩ .* u .+ -1 * ⟨v,u⟩ .* v), (⟨v,v⟩ .* u .+ -1 * ⟨v,u⟩ .* v) ⟩ =
    ((fst ⟨v,v⟩) * ((fst ⟨v,v⟩)* (fst ⟨u,u⟩) - (Cmod ⟨u,v⟩)^2 ))%R.
Proof. intros. 
       replace ((fst ⟨v,v⟩) * ((fst ⟨v,v⟩)* (fst ⟨u,u⟩) - (Cmod ⟨u,v⟩)^2 ))%R with
               (fst (⟨v,v⟩ * (⟨v,v⟩ * ⟨u,u⟩ - (Cmod ⟨u,v⟩)^2))).
       - apply f_equal.
         repeat rewrite inner_product_plus_l; repeat rewrite inner_product_plus_r;
           repeat rewrite inner_product_scale_l; repeat rewrite inner_product_scale_r. 
         replace ((-1 * ⟨ v, u ⟩) ^* * (-1 * ⟨ v, u ⟩ * ⟨ v, v ⟩)) with 
           ( ⟨ v, u ⟩^* * ⟨ v, u ⟩ * ⟨ v, v ⟩ ) by lca.       
         replace ((-1 * ⟨ v, u ⟩) ^* * (⟨ v, v ⟩ * ⟨ v, u ⟩) +
                    ⟨ v, u ⟩ ^* * ⟨ v, u ⟩ * ⟨ v, v ⟩) with C0 by lca.
         rewrite (inner_product_conj_sym v u), <- (inner_product_conj_sym v v).
         rewrite <- Cmult_assoc.   
         replace (⟨ u, v ⟩ ^* * ⟨ u, v ⟩) with (Cmod ⟨ u, v ⟩ ^ 2) by apply Cmod_sqr.
         lca.
       - assert (H := norm_real v).
         assert (H0 := norm_real u).
         destruct ⟨ v, v ⟩; destruct ⟨ u, u ⟩.
         rewrite Cmod_sqr.
         replace (⟨ u, v ⟩ ^* * ⟨ u, v ⟩) with (Cmod ⟨ u, v ⟩ ^ 2,0)%R.
         simpl in *; subst; lra.
         apply c_proj_eq.
         unfold Cmod. 
         rewrite pow2_sqrt. 
         simpl; lra.
         apply Rplus_le_le_0_compat; apply pow2_ge_0.
         rewrite Cmult_comm, Cmult_conj_real; easy. 
Qed.

Lemma real_ge_0_aux : forall (a b c : R),
  0 <= a -> 0 < b -> (a = b * c)%R ->
  0 <= c.
Proof. intros. 
       replace c with (a * / b)%R.
       apply Rle_mult_inv_pos; auto.
       subst.
       replace (b * c * / b)%R with (b * /b * c)%R by lra.
       rewrite Rinv_r; try lra. 
Qed.

Lemma Cauchy_Schwartz_ver1 : forall {n} (u v : Vector n),
  (Cmod ⟨u,v⟩)^2 <= (fst ⟨u,u⟩) * (fst ⟨v,v⟩).
Proof. intros. 
       destruct (Req_dec (fst ⟨v,v⟩) 0).
       - rewrite H. 
         rewrite inner_product_mafe_WF_l, inner_product_mafe_WF_r in H.
         rewrite inner_product_mafe_WF_r.
         assert (H' : make_WF v = Zero).
         { apply norm_zero_iff_zero; auto with wf_db.
           unfold norm; rewrite H.
           apply sqrt_0. }
         unfold inner_product.
         rewrite H', Mmult_0_r.
         unfold Zero.
         rewrite Cmod_0.
         lra.
       - assert (H0 := CS_key_lemma u v).
         apply real_ge_0_aux in H0.
         lra.
         apply inner_product_ge_0.
         destruct (inner_product_ge_0 v); lra.
Qed.

Lemma Cauchy_Schwartz_ver2 : forall {n} (u v : Vector n),
  (Cmod ⟨u,v⟩) <= norm u * norm v.
Proof. intros. 
       rewrite <- (sqrt_pow2 (Cmod ⟨ u, v ⟩)), <- (sqrt_pow2 (norm v)), <- (sqrt_pow2 (norm u)).
       rewrite <- sqrt_mult.
       apply sqrt_le_1.
       all : try apply pow2_ge_0.
       apply Rmult_le_pos.
       all : try apply pow2_ge_0.
       unfold norm.
       rewrite pow2_sqrt, pow2_sqrt.
       apply Cauchy_Schwartz_ver1.
       all : try apply inner_product_ge_0; try apply norm_ge_0.
       apply Cmod_ge_0.
Qed.

Lemma Cplx_Cauchy_vector :
  forall n (u v : Vector n),
    ((big_sum (fun i => Cmod (u i O) ^ 2) n) * (big_sum (fun i => Cmod (v i O) ^ 2) n) >=
     Cmod (big_sum (fun i => ((u i O)^* * (v i O))%C) n) ^ 2)%R.
Proof. intros.
       assert (H := Cauchy_Schwartz_ver1 u v).
       replace (big_sum (fun i : nat => (Cmod (u i 0%nat) ^ 2)%R) n) with (fst ⟨ u, u ⟩).
       replace (big_sum (fun i : nat => (Cmod (v i 0%nat) ^ 2)%R) n) with (fst ⟨ v, v ⟩).
       replace (Σ (fun i : nat => (u i 0%nat) ^* * v i 0%nat) n) with (⟨ u, v ⟩).
       lra.
       all : unfold inner_product, adjoint, Mmult; try easy. 
       all : rewrite (@big_sum_func_distr C R _ C_is_group _ R_is_group).
       all : try apply big_sum_eq_bounded; intros.
       all : try rewrite <- Cmod_sqr. 
       all : try (destruct a; destruct b; simpl; easy).
       destruct (v x 0%nat); unfold Cmod, pow, Cmult; simpl; lra. 
       destruct (u x 0%nat); unfold Cmod, pow, Cmult; simpl; lra. 
Qed.


Local Open Scope nat_scope.

Lemma Cplx_Cauchy :
  forall n (u v : nat -> C),
    ((big_sum (fun i => Cmod (u i) ^ 2) n) * (big_sum (fun i => Cmod (v i) ^ 2) n) >= Cmod (big_sum (fun i => ((u i)^* * (v i))%C) n) ^ 2)%R.
Proof. intros. 
       assert (H := Cplx_Cauchy_vector n (fun i j => u i) (fun i j => v i)).
       simpl in *.
       easy. 
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


(** Restoring Matrix Dimensions *)


(** Restoring Matrix dimensions *)
Ltac is_nat n := match type of n with nat => idtac end.

Ltac is_nat_equality :=
  match goal with 
  | |- ?A = ?B => is_nat A
  end.

Ltac unify_matrix_dims tac := 
  try reflexivity; 
  repeat (apply f_equal_gen; try reflexivity; 
          try (is_nat_equality; tac)).

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

Ltac restore_dims tac := 
  match goal with
  | |- ?A      => let A' := restore_dims_rec A in 
                replace A with A' by unify_matrix_dims tac
  end.

Tactic Notation "restore_dims" tactic(tac) := restore_dims tac.

Tactic Notation "restore_dims" := restore_dims (repeat rewrite Nat.pow_1_l; try ring; unify_pows_two; simpl; lia).


(* Proofs depending on restore_dims *)


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
Hint Rewrite kron_1_l kron_1_r Mmult_1_l Mmult_1_r id_kron id_adjoint_eq
     @Mmult_adjoint Mplus_adjoint @kron_adjoint @kron_mixed_product
     id_adjoint_eq adjoint_involutive using 
     (auto 100 with wf_db; autorewrite with M_db; auto 100 with wf_db; lia) : M_db.
*)

(* eauto will cause major choking... *)
#[export] Hint Rewrite  @kron_1_l @kron_1_r @Mmult_1_l @Mmult_1_r @Mscale_1_l 
     @id_adjoint_eq @id_transpose_eq using (auto 100 with wf_db) : M_db_light.
#[export] Hint Rewrite @kron_0_l @kron_0_r @Mmult_0_l @Mmult_0_r @Mplus_0_l @Mplus_0_r
     @Mscale_0_l @Mscale_0_r @zero_adjoint_eq @zero_transpose_eq using (auto 100 with wf_db) : M_db_light.

(* I don't like always doing restore_dims first, but otherwise sometimes leaves 
   unsolvable WF_Matrix goals. *)
Ltac Msimpl_light := try restore_dims; autorewrite with M_db_light.

#[export] Hint Rewrite @Mmult_adjoint @Mplus_adjoint @kron_adjoint @kron_mixed_product
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
  | ?A × ?B  => idtac
  | ?A .+ ?B => idtac 
  | ?A †     => compound A
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
