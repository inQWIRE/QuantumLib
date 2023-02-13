 
(** In this file, we define matrices and prove many basic facts from linear algebra *)
 
Require Import Psatz. 
Require Import String.
Require Import Program. 
Require Import List.
Require Export Summation. 



(* TODO: Use matrix equality everywhere, declare equivalence relation *)
(* TODO: Make all nat arguments to matrix lemmas implicit *)


(** * Matrix definitions and infrastructure **)


Declare Scope genmatrix_scope.
Delimit Scope genmatrix_scope with GM.
Open Scope genmatrix_scope.




(* TODO: make this better (although it already works well despite being naive) *)
Ltac dumb_lRa := repeat (repeat rewrite Gmult_plus_distr_l;
                         repeat rewrite Gmult_plus_distr_r;
                         repeat rewrite Gmult_assoc;
                         repeat rewrite Gmult_1_l;
                         repeat rewrite Gmult_1_r; 
                         repeat rewrite Gmult_0_l;
                         repeat rewrite Gmult_0_r;
                         repeat rewrite Gplus_assoc;
                         repeat rewrite Gplus_0_l;
                         repeat rewrite Gplus_0_r; try easy).


 

Local Open Scope nat_scope.
Local Open Scope group_scope.



Definition GenMatrix (F : Type) (m n : nat) := nat -> nat -> F.

(* Check that a matrix is well formed. Super important for understanding how we view matrices! *)
Definition WF_GenMatrix {F : Type} {R0 : Monoid F} {m n: nat} (A : GenMatrix F m n) : Prop := 
  forall x y, x >= m \/ y >= n -> A x y = 0.


(* makes a matrix well formed *)
Definition make_WF {F : Type} {R0 : Monoid F} {m n} (S : GenMatrix F m n) : GenMatrix F m n :=
  fun i j => if (i <? m) && (j <? n) then S i j else 0%G.  


Notation Vector F n := (GenMatrix F n 1).

Notation Square F n := (GenMatrix F n n).

(** Equality via functional extensionality *)
Ltac prep_genmatrix_equality :=
  let x := fresh "x" in 
  let y := fresh "y" in 
  apply functional_extensionality; intros x;
  apply functional_extensionality; intros y.

(** Matrix equivalence *)

Definition genmat_equiv {F : Type} {m n : nat} (A B : GenMatrix F m n) : Prop := 
  forall i j, i < m -> j < n -> A i j = B i j.

Infix "==" := genmat_equiv (at level 70) : genmatrix_scope.

Lemma genmat_equiv_refl : forall F m n (A : GenMatrix F m n), genmat_equiv A A.
Proof. unfold genmat_equiv; reflexivity. Qed.

Lemma genmat_equiv_eq : forall {F} {R0 : Monoid F} {m n : nat} (A B : GenMatrix F m n),
  WF_GenMatrix A -> 
  WF_GenMatrix B -> 
  A == B ->
  A = B.
Proof.
  intros F R0 m n A' B' WFA WFB Eq.
  prep_genmatrix_equality.
  unfold genmat_equiv in Eq.
  bdestruct (x <? m).
  bdestruct (y <? n).
  + apply Eq; easy.
  + rewrite WFA, WFB; trivial; right; try lia.
  + rewrite WFA, WFB; trivial; left; try lia.
Qed.


(** 2D list representation *)
    
Definition list2D_to_genmatrix {F : Type} {R0 : Monoid F} (l : list (list F)) : 
  GenMatrix F (length l) (length (hd [] l)) :=
  (fun x y => nth y (nth x l []) 0).

Lemma WF_list2D_to_genmatrix : forall {F : Type} {R0 : Monoid F} m n li, 
    length li = m ->
    (forall li', In li' li -> length li' = n)  ->
    @WF_GenMatrix F R0 m n (list2D_to_genmatrix li).
Proof.
  intros F R0 m n li L f x y [l | r].
  - unfold list2D_to_genmatrix. 
    rewrite (nth_overflow _ []).
    destruct y; easy.
    rewrite L. apply l.
  - unfold list2D_to_genmatrix. 
    rewrite (nth_overflow _ 0).
    easy.
    destruct (nth_in_or_default x li []) as [IN | DEF].
    apply f in IN.
    rewrite IN. apply r.
    rewrite DEF.
    simpl; lia.
Qed.

(** Example *)
Definition M23 (F : Type) `{Ring F} : GenMatrix F 2 3 :=
  fun x y => 
  match (x, y) with
  | (0, 0) => 1
  | (0, 1) => 1+1
  | (0, 2) => 1+1+1
  | (1, 0) => 1+1+1+1
  | (1, 1) => 1+1+1+1+1
  | (1, 2) => 1+1+1+1+1+1
  | _ => 0
  end.

Definition M23' (F : Type) `{Ring F} : GenMatrix F 2 3 := 
  list2D_to_genmatrix  
  ([ [1; 1+1; 1+1+1];
    [1+1+1+1; 1+1+1+1+1; 1+1+1+1+1+1] ]).

Lemma M23eq (F : Type) `{Ring F} : M23 F = M23' F.
Proof.
  unfold M23'.
  compute.
  prep_genmatrix_equality.
  do 4 (try destruct x; try destruct y; simpl; trivial).
Qed.


(** * Operands and operations **)

(* TODO: perhaps make m and n explicit? *)
Definition Zero {F : Type} {R0 : Monoid F} {m n : nat} : GenMatrix F m n := fun x y => 0.

Definition I {F : Type} `{R3 : Ring F} (n : nat) : Square F n := 
  (fun x y => if (x =? y) && (x <? n) then 1 else 0).

(* in many cases, n needs to be made explicit, but not always, hence it is made implicit here *)
Definition e_i {F : Type} `{R3 : Ring F} {n : nat} (i : nat) : Vector F n :=
  fun x y => (if (x =? i) && (x <? n) && (y =? 0) then 1 else 0). 


(* Optional coercion to scalar (should be limited to 1 × 1 matrices):
Definition to_scalar (m n : nat) (A: GenMatrix m n) : C := A 0 0.
Coercion to_scalar : GenMatrix >-> C.
*)

(* This isn't used, but is interesting *)
Definition I__inf {F : Type} `{R3 : Ring F} := fun x y => if x =? y then 1 else 0.
Notation "I∞" := I__inf : genmatrix_scope.



(*TODO: the placement of G's is horribly inconsistent... can probably be fixed since
 eventually Matrix n m will be something more specific like CMatrix n m *)
Definition trace {F : Type} {R0 : Monoid F} {n : nat} (A : Square F n) := 
  big_sum (fun x => A x x) n.

Definition scale {F : Type} `{R3 : Ring F} 
           {m n : nat} (r : F) (A : GenMatrix F m n) : GenMatrix F m n := 
  fun x y => (r * A x y).

Definition dot {F : Type} `{R3 : Ring F}  {n : nat} (A : Vector F n) (B : Vector F n) : F :=
  big_sum (fun x => A x 0 * B x 0) n.

Definition GMplus {F : Type} {R0 : Monoid F} 
           {m n : nat} (A B : GenMatrix F m n) : GenMatrix F m n :=
  fun x y => (A x y + B x y).

Definition GMopp {F : Type} `{R1 : Group F} 
           {m n : nat} (A : GenMatrix F m n) : GenMatrix F m n :=
  fun x y => (- A x y).

Definition GMminus {F : Type} `{R1 : Group F} 
           {m n : nat} (A B : GenMatrix F m n) : GenMatrix F m n :=
  GMplus A (GMopp B).

Definition GMmult {F : Type} `{R3 : Ring F}
           {m n o : nat} (A : GenMatrix F m n) (B : GenMatrix F n o) : GenMatrix F m o := 
  fun x z => big_sum (fun y => A x y * B y z) n.


(* Only well-defined when o and p are non-zero *)
Definition Gkron {F : Type} `{R3 : Ring F}
           {m n o p : nat} (A : GenMatrix F m n) (B : GenMatrix F o p) : 
  GenMatrix F (m*o) (n*p) :=
  fun x y => (A (x / o)%nat (y / p)%nat) * (B (x mod o) (y mod p)).

Definition direct_sum {F : Type} {R0 : Monoid F} 
           {m n o p : nat} (A : GenMatrix F m n) (B : GenMatrix F o p) :
  GenMatrix F (m+o) (n+p) :=
  fun x y =>  if (x <? m) || (y <? n) then A x y else B (x - m)%nat (y - n)%nat.

Definition transpose {F : Type} {m n} (A : GenMatrix F m n) : GenMatrix F n m := 
  fun x y => A y x.

(* NB: no adjoint! 
Definition adjoint {m n} (A : GenMatrix m n) : GenMatrix n m := 
  fun x y => (A y x)^*.
*)


(* no adjoint! so these are defined in terms of transpose. good for R, but is this correct? *)
Definition inner_product {F : Type} `{R3 : Ring F}
           {n} (u v : Vector F n) : F := 
  GMmult (transpose u) (v) 0 0.

Definition outer_product {F : Type} `{R3 : Ring F} 
           {n} (u v : Vector F n) : Square F n := 
  GMmult u (transpose v).

(** Kronecker of n copies of A *)
Fixpoint kron_n {F : Type} `{R3 : Ring F} 
         n {m1 m2} (A : GenMatrix F m1 m2) : GenMatrix F (m1^n) (m2^n) :=
  match n with
  | 0    => I 1
  | S n' => Gkron (kron_n n' A) A
  end.

(** Kronecker product of a list *)
Fixpoint big_kron {F : Type} `{R3 : Ring F}  
         {m n} (As : list (GenMatrix F m n)) : 
  GenMatrix F (m^(length As)) (n^(length As)) := 
  match As with
  | [] => I 1
  | A :: As' => Gkron A (big_kron As')
  end.

(** Product of n copies of A, basically GMpow *)
Fixpoint GMmult_n {F : Type} `{R3 : Ring F}   
         {m} (A : Square F m) p : Square F m :=
  match p with
  | 0    => I m
  | S p' => GMmult A (GMmult_n A p')
  end.

(** Direct sum of n copies of A *)
Fixpoint direct_sum_n {F : Type} {R0 : Monoid F} `{R3 : Ring F} 
         n {m1 m2} (A : GenMatrix F m1 m2) : GenMatrix F (n*m1) (n*m2) :=
  match n with
  | 0    => @Zero F R0 0 0
  | S n' => direct_sum A (direct_sum_n n' A)
  end.



(** Notations *) 
Infix "∘" := dot (at level 40, left associativity) : genmatrix_scope.
Infix ".+" := GMplus (at level 50, left associativity) : genmatrix_scope.
Infix ".*" := scale (at level 40, left associativity) : genmatrix_scope.
Infix "×" := GMmult (at level 40, left associativity) : genmatrix_scope.
Infix "⊗" := Gkron (at level 40, left associativity) : genmatrix_scope.
Infix ".⊕" := direct_sum (at level 20) : genmatrix_scope. (* should have different level and assoc *)
Infix "≡" := genmat_equiv (at level 70) : genmatrix_scope.
Notation "A ⊤" := (transpose A) (at level 0) : genmatrix_scope. 
(* Notation "A †" := (adjoint A) (at level 0) : genmatrix_scope. *)
(* Notation Σ := (@big_sum F R0).  (* we intoduce Σ notation here *) *)
Notation "n ⨂ A" := (kron_n n A) (at level 30, no associativity) : genmatrix_scope.
Notation "⨂ A" := (big_kron A) (at level 60): genmatrix_scope.
Notation "p ⨉ A" := (GMmult_n A p) (at level 30, no associativity) : genmatrix_scope.
Notation "⟨ u , v ⟩" := (inner_product u v) (at level 0) : genmatrix_scope. 
 

#[export] Hint Unfold Zero I e_i trace dot GMplus GMopp scale GMmult Gkron genmat_equiv transpose : U_db.


(* tactics for equality and mat_equality *)

Ltac destruct_m_1 :=
  match goal with
  | [ |- context[match ?x with 
                 | 0   => _
                 | S _ => _
                 end] ] => is_var x; destruct x
  end.
Ltac destruct_m_eq := repeat (destruct_m_1; simpl).


Ltac lgma := 
  autounfold with U_db;
  prep_genmatrix_equality;
  destruct_m_eq; 
  (* lca. *)  (* !!! everything is destroyed without lca for rings *)
  ring.

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
  repeat (destruct i as [|i]; simpl; [|apply Nat.succ_lt_mono in Hi]; try solve_end); clear Hi;
  repeat (destruct j as [|j]; simpl; [|apply Nat.succ_lt_mono in Hj]; try solve_end); clear Hj.

Ltac lgma' :=
  apply genmat_equiv_eq;
  repeat match goal with
  | [ |- WF_GenMatrix (?A) ]  => auto with wf_db (* (try show_wf) *)
  | [ |- genmat_equiv (?A) (?B) ] => by_cell; try ring (* try lca  *)             
  end.



(** * Tactics for showing well-formedness *)


(* Much less awful *)
Ltac show_wf := 
  unfold WF_GenMatrix;
  let x := fresh "x" in
  let y := fresh "y" in
  let H := fresh "H" in
  intros x y [H | H];
  apply le_plus_minus' in H; rewrite H;
  cbv;
  destruct_m_eq;
  try ring.




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
      |- WF_GenMatrix _ => auto with wf_db;
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
  | ?A        => has_hyp (WF_GenMatrix A)
  (* recursive case *)
  | ?op ?A ?B => collate_wf' A;
                collate_wf' B;
                assert (WF_GenMatrix (op A B)) by auto with wf_db
  (* base case *)
  | ?A =>        assert (WF_GenMatrix A) by auto with wf_db
  (* not a matrix *)
  | _         => idtac
  end.
  
(* Aggregates well-formedness conditions for context *)
Ltac collate_wf :=
  match goal with
  | |- ?A = ?B      => collate_wf' A; collate_wf' B
  | |- ?A == ?B     => collate_wf' A; collate_wf' B
  | |- WF_GenMatrix ?A => collate_wf' A
  | |- context[?A]  => collate_wf' A 
  end.

Ltac solve_wf := collate_wf; easy. 




(** * Showing that M is a vector space *)

#[export] Program Instance GM_is_monoid : forall {F : Type} {R0 : Monoid F} 
                                                 m n , Monoid (GenMatrix F m n) := 
  { Gzero := @Zero F R0 m n
  ; Gplus := GMplus
  }.
Solve All Obligations with program_simpl; prep_genmatrix_equality; 
  autounfold with U_db; dumb_lRa. 


#[export] Program Instance GM_is_group : forall {F : Type} `{R1 : Group F} 
                                                m n, Group (GenMatrix F m n) :=
  { Gopp := GMopp }.
Solve All Obligations with program_simpl; prep_genmatrix_equality; 
  autounfold with U_db; dumb_lRa; try apply Gopp_l; apply Gopp_r.
                 

#[export] Program Instance M_is_comm_group : forall {F : Type} `{R2 : Comm_Group F} 
                                                    m n, Comm_Group (GenMatrix F m n).
Solve All Obligations with program_simpl; prep_genmatrix_equality; 
  autounfold with U_db; try apply Gplus_comm.

#[export] Program Instance M_is_module_space : forall {F : Type} `{R4 : Comm_Ring F} 
                                                      m n, Module_Space (GenMatrix F m n) F :=
  { Vscale := scale }.
Solve All Obligations with program_simpl; prep_genmatrix_equality; 
  autounfold with U_db; dumb_lRa. 














(********************************************************)
(* HERE, We put everything in a section for convenience *)
(********************************************************)

Section LinAlgOverCommRing.
  Variables (F : Type).   (* F for ring, too bad R is taken :( *)
  Variable (R0 : Monoid F).
  Variable (R1 : Group F).
  Variable (R2 : Comm_Group F).
  Variable (R3 : Ring F).
  Variable (R4 : Comm_Ring F).


(* things that need to be rewritten in order to get the "reopened" section to work *)
(* could maybe use a Module so that this only needs to occur once??? *) 
Lemma F_ring_theory : ring_theory 0%G 1%G Gplus Gmult Gminus Gopp eq.
Proof. apply (@G_ring_theory F _ _ _ _ R4). Qed.

Add Ring F_ring_ring : F_ring_theory.


Notation GenMatrix := (GenMatrix F). 
Notation Square n := (Square F n). 
Notation Vector n := (Vector F n). 

Notation Σ := (@big_sum F R0).  (* we intoduce Σ notation here *) 










(* lemmas which are useful for simplifying proofs involving matrix operations *)
Lemma kron_simplify : forall (m n o p : nat) (a b : GenMatrix m n) (c d : GenMatrix o p), 
    a = b -> c = d -> (a ⊗ c)%GM = (b ⊗ d)%GM.
Proof. intros; subst; easy. 
Qed.

Lemma n_kron_simplify : forall (m n : nat) (a b : GenMatrix m n) (i j : nat), 
    a = b -> i = j -> i ⨂ a = j ⨂ b.
Proof. intros; subst; easy. 
Qed.

Lemma Mtranspose_simplify : forall (m n : nat) (a b : GenMatrix m n), 
    a = b -> a⊤ = b⊤.
Proof. intros; subst; easy. 
Qed.

(*
Lemma Madjoint_simplify : forall (n m : nat) (a b : GenMatrix n m), 
    a = b -> a† = b†.
Proof. intros; subst; easy. 
Qed.
*)

Lemma Mmult_simplify : forall (m n o : nat) (a b : GenMatrix m n) (c d : GenMatrix n o), 
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

Lemma Mplus_simplify : forall (m n : nat) (a b c d : GenMatrix m n), 
    a = b -> c = d -> a .+ c = b .+ d.
Proof. intros; subst; easy. 
Qed.

Lemma Mscale_simplify : forall (m n : nat) (a b : GenMatrix m n) (c d : F), 
    a = b -> c = d -> c .* a = d .* b.
Proof. intros; subst; easy. 
Qed.



(** * Proofs about well-formedness **)



Lemma WF_GenMatrix_dim_change : forall (m n m' n' : nat) (A : GenMatrix m n),
  m = m' ->
  n = n' ->
  @WF_GenMatrix F R0 m n A ->
  @WF_GenMatrix F R0 m' n' A.
Proof. intros. subst. easy. Qed.

Lemma WF_make_WF : forall {m n} (S : GenMatrix m n), WF_GenMatrix (make_WF S).
Proof. intros. 
       unfold WF_GenMatrix, make_WF; intros. 
       destruct H as [H | H].
       bdestruct (x <? m); try lia; easy. 
       bdestruct (y <? n); bdestruct (x <? m); try lia; easy.
Qed.
  
Lemma WF_Zero : forall m n : nat, WF_GenMatrix (@Zero F R0 m n).
Proof. intros m n. unfold WF_GenMatrix. reflexivity. Qed.

Lemma WF_I : forall n : nat, WF_GenMatrix (I n). 
Proof. 
  unfold WF_GenMatrix, I. intros n x y H. simpl.
  destruct H; bdestruct (x =? y); bdestruct (x <? n); trivial; lia.
Qed.

Lemma WF_I1 : WF_GenMatrix (I 1). Proof. apply WF_I. Qed.

Lemma WF_e_i : forall {n : nat} (i : nat),
  WF_GenMatrix (@e_i _ _ _ _ _ n i).
Proof. unfold WF_GenMatrix, e_i.
       intros; destruct H as [H | H].
       bdestruct (x =? i); bdestruct (x <? n); bdestruct (y =? 0); try lia; easy.
       bdestruct (x =? i); bdestruct (x <? n); bdestruct (y =? 0); try lia; easy.
Qed.

Lemma WF_scale : forall {m n : nat} (r : F) (A : GenMatrix m n), 
  WF_GenMatrix A -> WF_GenMatrix (scale r A).
Proof.
  unfold WF_GenMatrix, scale.
  intros m n r A H x y H0. simpl.
  rewrite H; trivial.
  rewrite Gmult_0_r.
  reflexivity.
Qed.

Lemma WF_plus : forall {m n} (A B : GenMatrix m n), 
  WF_GenMatrix A -> WF_GenMatrix B -> WF_GenMatrix (A .+ B).
Proof.
  unfold WF_GenMatrix, GMplus.
  intros m n A B H H0 x y H1. simpl.
  rewrite H, H0; trivial.
  rewrite Gplus_0_l.
  reflexivity.
Qed.

Lemma WF_mult : forall {m n o : nat} (A : GenMatrix m n) (B : GenMatrix n o), 
  WF_GenMatrix A -> WF_GenMatrix B -> WF_GenMatrix (A × B).
Proof. 
  unfold WF_GenMatrix, GMmult.
  intros m n o A B H H0 x y D. 
  apply (@big_sum_0 F R0).
  destruct D; intros z.
  + rewrite H; [rewrite Gmult_0_l; easy | auto].
  + rewrite H0; [rewrite Gmult_0_r; easy | auto].
Qed.

Lemma WF_kron : forall {m n o p q r : nat} (A : GenMatrix m n) (B : GenMatrix o p), 
                  q = (m * o)%nat -> r = (n * p)%nat -> 
                  WF_GenMatrix A -> WF_GenMatrix B -> @WF_GenMatrix F R0 q r (A ⊗ B).
Proof.
  unfold WF_GenMatrix, Gkron.
  intros m n o p q r A B Nn No H H0 x y H1. subst.
  bdestruct (o =? 0). rewrite H0; [rewrite Gmult_0_r; easy|lia]. 
  bdestruct (p =? 0). rewrite H0; [rewrite Gmult_0_r; easy|lia]. 
  rewrite H.
  rewrite Gmult_0_l; reflexivity.
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

Lemma WF_direct_sum : forall {m n o p q r : nat} (A : GenMatrix m n) (B : GenMatrix o p), 
                  q = (m + o)%nat -> r = (n + p)%nat -> 
                  WF_GenMatrix A -> WF_GenMatrix B -> @WF_GenMatrix F R0 q r (A .⊕ B).
Proof. 
  unfold WF_GenMatrix, direct_sum. 
  intros; subst.
  destruct H3; bdestruct_all; simpl; try apply H1; try apply H2. 
  all : try lia.
Qed.

Lemma WF_transpose : forall {m n : nat} (A : GenMatrix m n), 
                     WF_GenMatrix A -> WF_GenMatrix A⊤. 
Proof. unfold WF_GenMatrix, transpose. intros m n A H x y H0. apply H. 
       destruct H0; auto. Qed.

(*
Lemma WF_adjoint : forall {m n : nat} (A : GenMatrix m n), 
      WF_GenMatrix A -> WF_GenMatrix A†. 
Proof. unfold WF_GenMatrix, adjoint, Cconj. intros m n A H x y H0. simpl. 
rewrite H. lca. lia. Qed.
*)

Lemma WF_outer_product : forall {n} (u v : Vector n),
    WF_GenMatrix u ->
    WF_GenMatrix v ->
    WF_GenMatrix (outer_product u v).
Proof. intros. apply WF_mult; [|apply WF_transpose]; assumption. Qed.

Lemma WF_kron_n : forall n {m1 m2} (A : GenMatrix m1 m2),
   WF_GenMatrix A ->  WF_GenMatrix (kron_n n A).
Proof.
  intros.
  induction n; simpl.
  - apply WF_I.
  - apply WF_kron; try lia; assumption. 
Qed.

Lemma WF_big_kron : forall n m (l : list (GenMatrix m n)) (A : GenMatrix m n), 
                        (forall i, WF_GenMatrix (nth i l A)) ->
                         WF_GenMatrix (⨂ l). 
Proof.                         
  intros n m l A H.
  induction l.
  - simpl. apply WF_I.
  - simpl. apply WF_kron; trivial. apply (H O).
    apply IHl. intros i. apply (H (S i)).
Qed.

(* alternate version that uses In instead of nth *)
Lemma WF_big_kron' : forall n m (l : list (GenMatrix m n)), 
                        (forall A, In A l -> WF_GenMatrix A) ->
                         WF_GenMatrix (⨂ l). 
Proof.                         
  intros n m l H. 
  induction l.
  - simpl. apply WF_I.
  - simpl. apply WF_kron; trivial. apply H; left; easy. 
    apply IHl. intros A' H0. apply H; right; easy.
Qed.

Lemma WF_GMmult_n : forall n {m} (A : Square m),
   WF_GenMatrix A -> WF_GenMatrix (GMmult_n A n).
Proof.
  intros.
  induction n; simpl.
  - apply WF_I.
  - apply WF_mult; assumption. 
Qed.

Lemma WF_direct_sum_n : forall n {m1 m2} (A : GenMatrix m1 m2),
   WF_GenMatrix A -> WF_GenMatrix (direct_sum_n n A).
Proof.
  intros.
  induction n; simpl.
  - apply WF_Zero.
  - apply WF_direct_sum; try lia; assumption. 
Qed.


Lemma WF_Msum : forall d1 d2 n (f : nat -> GenMatrix d1 d2), 
  (forall i, (i < n)%nat -> WF_GenMatrix (f i)) -> 
  WF_GenMatrix (big_sum f n).
Proof.
  intros. 
  apply big_sum_prop_distr; intros. 
  apply WF_plus; auto.
  apply WF_Zero.
  auto. 
Qed.





(* Create HintDb wf_db. *)
Hint Resolve WF_Zero WF_I WF_I1 WF_mult WF_plus WF_scale WF_transpose
     WF_outer_product WF_big_kron WF_kron_n WF_kron 
     WF_GMmult_n WF_make_WF (* WF_Msum *) : wf_db.
Hint Extern 2 (_ = _) => unify_pows_two : wf_db.

  
(** * Basic matrix lemmas *)

Lemma genmat_equiv_make_WF : forall {m n} (T : GenMatrix m n),
  T == make_WF T.
Proof. unfold make_WF, genmat_equiv; intros. 
       bdestruct (i <? m); bdestruct (j <? n); try lia; easy.
Qed.

Lemma eq_make_WF : forall {n m} (T : GenMatrix m n),
  WF_GenMatrix T -> T = make_WF T.
Proof. intros. 
       apply genmat_equiv_eq; auto with wf_db.
       apply genmat_equiv_make_WF.
Qed.

Lemma GMplus_make_WF : forall {n m} (A B : GenMatrix m n),
  make_WF A .+ make_WF B = make_WF (A .+ B).
Proof. intros. 
       apply genmat_equiv_eq; auto with wf_db.
       unfold genmat_equiv; intros. 
       unfold make_WF, GMplus.
       bdestruct (i <? m); bdestruct (j <? n); try lia; simpl. 
       easy.
Qed.
  
Lemma GMmult_make_WF : forall {m n o} (A : GenMatrix m n) (B : GenMatrix n o),
  make_WF A × make_WF B = make_WF (A × B).
Proof. intros. 
       apply genmat_equiv_eq; auto with wf_db.
       unfold genmat_equiv; intros. 
       unfold make_WF, GMmult.
       bdestruct (i <? m); bdestruct (j <? o); try lia; simpl. 
       apply big_sum_eq_bounded; intros. 
       bdestruct (x <? n); try lia; easy. 
Qed.

  
Lemma WF0_Zero_l :forall (n : nat) (A : GenMatrix 0%nat n), WF_GenMatrix A -> A = Zero.
Proof.
  intros n A WFA.
  prep_genmatrix_equality.
  rewrite WFA.
  reflexivity.
  lia.
Qed.

Lemma WF0_Zero_r :forall (n : nat) (A : GenMatrix n 0%nat), WF_GenMatrix A -> A = Zero.
Proof.
  intros n A WFA.
  prep_genmatrix_equality.
  rewrite WFA.
  reflexivity.
  lia.
Qed.

Lemma WF0_Zero :forall (A : GenMatrix 0%nat 0%nat), WF_GenMatrix A -> A = Zero.
Proof.
  apply WF0_Zero_l.
Qed.

Lemma I0_Zero : I 0 = Zero.
Proof.
  apply WF0_Zero.
  apply WF_I.
Qed.

Lemma trace_plus_dist : forall (n : nat) (A B : Square n), 
    trace (A .+ B) = (trace A + trace B). 
Proof. 
  intros.
  unfold trace, GMplus.
  rewrite (@big_sum_plus F _ _ R2). 
  easy.  
Qed.

Lemma trace_mult_dist : forall n p (A : Square n), trace (p .* A) = (p * trace A). 
Proof.
  intros.
  unfold trace, scale.
  rewrite (@big_sum_mult_l F _ _ _ R3). 
  easy.
Qed.

Lemma GMplus_0_l : forall (m n : nat) (A : GenMatrix m n), Zero .+ A = A.
Proof. intros. lgma. Qed.

Lemma GMplus_0_r : forall (m n : nat) (A : GenMatrix m n), A .+ Zero = A.
Proof. intros. lgma. Qed.
    
Lemma GMmult_0_l : forall (m n o : nat) (A : GenMatrix n o), @Zero F R0 m n × A = Zero.
Proof.
  intros m n o A. 
  unfold GMmult, Zero.
  prep_genmatrix_equality.
  apply (@big_sum_0 F R0).  
  intros.
  ring.
Qed.

Lemma GMmult_0_r : forall (m n o : nat) (A : GenMatrix m n), A × @Zero F R0 n o = Zero.
Proof.
  intros m n o A. 
  unfold Zero, GMmult.
  prep_genmatrix_equality.
  apply (@big_sum_0 F R0). 
  intros.
  ring. 
Qed.

(* using <= because our form big_sum is exclusive. *)
Lemma GMmult_1_l_gen: forall (m n : nat) (A : GenMatrix m n) (x z k : nat), 
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
      simpl; dumb_lRa.
      apply IHl.
      lia.
    + intros gtSkx.
      simpl in *.
      unfold I in *.
      bdestruct (x =? k); bdestruct (x <? m); subst; try lia.
      rewrite IHl by lia; simpl; ring.
      rewrite IHr by lia; simpl; ring.
Qed.

Lemma GMmult_1_l_mat_eq : forall (m n : nat) (A : GenMatrix m n), I m × A == A.
Proof.
  intros m n A i j Hi Hj.
  unfold GMmult.
  edestruct (@GMmult_1_l_gen m n) as [Hl Hr].
  apply Nat.le_refl.
  unfold get.
  apply Hr.
  simpl in *.
  lia.
Qed.  

Lemma GMmult_1_l: forall (m n : nat) (A : GenMatrix m n), 
  WF_GenMatrix A -> I m × A = A.
Proof.
  intros m n A H.
  apply genmat_equiv_eq; trivial.
  auto with wf_db.
  apply GMmult_1_l_mat_eq.
Qed.

Lemma GMmult_1_r_gen: forall (m n : nat) (A : GenMatrix m n) (x z k : nat), 
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
    simpl; dumb_lRa.
    apply IHl; lia.
  + intros gtSkz.
    simpl in *.
    unfold I in *.
    bdestruct (k =? z); subst.
    - bdestruct (z <? n); try lia.
      rewrite IHl by lia; simpl; ring.
    - rewrite IHr by lia; simpl; ring.
Qed.

Lemma GMmult_1_r_mat_eq : forall (m n : nat) (A : GenMatrix m n), A × I n ≡ A.
Proof.
  intros m n A i j Hi Hj.
  unfold GMmult.
  edestruct (@GMmult_1_r_gen m n) as [Hl Hr].
  apply Nat.le_refl.
  unfold get; simpl.
  apply Hr.
  lia.
Qed.  

Lemma GMmult_1_r: forall (m n : nat) (A : GenMatrix m n), 
  WF_GenMatrix A -> A × I n = A.
Proof.
  intros m n A H.
  apply genmat_equiv_eq; trivial.
  auto with wf_db.
  apply GMmult_1_r_mat_eq.
Qed.

(* Cool facts about I∞, not used in the development *) 
Lemma GMmult_inf_l : forall(m n : nat) (A : GenMatrix m n),
  WF_GenMatrix A -> I∞ × A = A.
Proof. 
  intros m n A H.
  prep_genmatrix_equality.
  unfold GMmult.
  edestruct (@GMmult_1_l_gen m n) as [Hl Hr].
  apply Nat.le_refl.
  bdestruct (m <=? x).
  rewrite H by auto.
  apply (@big_sum_0_bounded F R0). 
  intros z L. 
  unfold I__inf, I.
  bdestruct (x =? z). lia. ring. 
  unfold I__inf, I in *.
  erewrite big_sum_eq.
  apply Hr.
  assumption.
  bdestruct (x <? m); [|lia]. 
  apply functional_extensionality. intros. rewrite andb_true_r. reflexivity.
Qed.

Lemma GMmult_inf_r : forall(m n : nat) (A : GenMatrix m n),
  WF_GenMatrix A -> A × I∞ = A.
Proof. 
  intros m n A H.
  prep_genmatrix_equality.
  unfold GMmult.
  edestruct (@GMmult_1_r_gen m n) as [Hl Hr].
  apply Nat.le_refl.
  bdestruct (n <=? y).
  rewrite H by auto.
  apply (@big_sum_0_bounded F R0). 
  intros z L. 
  unfold I__inf, I.
  bdestruct (z =? y). lia. ring. 
  unfold I__inf, I in *.
  erewrite big_sum_eq.
  apply Hr.
  assumption.
  apply functional_extensionality. intros z. 
  bdestruct (z =? y); bdestruct (z <? n); simpl; dumb_lRa; lia. 
Qed.

Lemma kron_0_l : forall (m n o p : nat) (A : GenMatrix o p), 
  @Zero F R0 m n ⊗ A = Zero.
Proof.
  intros m n o p A.
  prep_genmatrix_equality.
  unfold Zero, Gkron.
  rewrite Gmult_0_l.
  reflexivity.
Qed.

Lemma kron_0_r : forall (m n o p : nat) (A : GenMatrix m n), 
   A ⊗ @Zero F R0 o p = Zero.
Proof.
  intros m n o p A.
  prep_genmatrix_equality.
  unfold Zero, Gkron.
  rewrite Gmult_0_r.
  reflexivity.
Qed.

Lemma kron_1_r : forall (m n : nat) (A : GenMatrix m n), A ⊗ I 1 = A.
Proof.
  intros m n A.
  prep_genmatrix_equality.
  unfold I, Gkron.
  rewrite 2 Nat.div_1_r.
  rewrite 2 Nat.mod_1_r.
  simpl.
  ring. 
Qed.

(* This side is more limited *)
Lemma kron_1_l : forall (m n : nat) (A : GenMatrix m n), 
  WF_GenMatrix A -> I 1 ⊗ A = A.
Proof.
  intros m n A WF.
  prep_genmatrix_equality.
  unfold I, Gkron.
  bdestruct (m =? 0). rewrite 2 WF by lia. ring. 
  bdestruct (n =? 0). rewrite 2 WF by lia. ring. 
  bdestruct (x / m <? 1); rename H1 into Eq1.
  bdestruct (x / m =? y / n); rename H1 into Eq2; simpl.
  + assert (x / m = 0)%nat by lia. clear Eq1. rename H1 into Eq1.
    rewrite Eq1 in Eq2.     
    symmetry in Eq2.
    rewrite Nat.div_small_iff in Eq2 by lia.
    rewrite Nat.div_small_iff in Eq1 by lia.
    rewrite 2 Nat.mod_small; trivial.
    ring. 
  + assert (x / m = 0)%nat by lia. clear Eq1.
    rewrite H1 in Eq2. clear H1.
    assert (y / n <> 0)%nat by lia. clear Eq2.
    rewrite Nat.div_small_iff in H1 by lia.
    rewrite Gmult_0_l.
    destruct WF with (x := x) (y := y). lia.
    reflexivity.
  + rewrite andb_false_r.
    assert (x / m <> 0)%nat by lia. clear Eq1.
    rewrite Nat.div_small_iff in H1 by lia.
    rewrite Gmult_0_l.
    destruct WF with (x := x) (y := y). lia.
    reflexivity.
Qed.

Theorem transpose_involutive : forall (m n : nat) (A : GenMatrix m n), (A⊤)⊤ = A.
Proof. reflexivity. Qed.

(*
Theorem adjoint_involutive : forall (m n : nat) (A : GenMatrix m n), A†† = A.
Proof. intros. lma. Qed.  
*)

Lemma id_transpose_eq : forall n, (I n)⊤ = (I n).
Proof.
  intros n. unfold transpose, I.
  prep_genmatrix_equality.
  bdestruct (y =? x); bdestruct (x =? y); bdestruct (y <? n); bdestruct (x <? n);
    trivial; lia.
Qed.

Lemma zero_transpose_eq : forall m n, (@Zero F R0 m n)⊤ = @Zero F R0 m n.
Proof. reflexivity. Qed.


(*
Lemma id_adjoint_eq : forall n, (I n)† = (I n).
Proof.
  intros n.
  unfold adjoint, I.
  prep_genmatrix_equality.
  bdestruct (y =? x); bdestruct (x =? y); bdestruct (y <? n); bdestruct (x <? n);
    try lia; lca.
Qed.
*)
(*
Lemma zero_adjoint_eq : forall m n, (@Zero m n)† = @Zero n m.
Proof. unfold adjoint, Zero. rewrite Cconj_0. reflexivity. Qed.
*)

Theorem GMplus_comm : forall (m n : nat) (A B : GenMatrix m n), A .+ B = B .+ A.
Proof.
  unfold GMplus. 
  intros m n A B.
  prep_genmatrix_equality.
  apply Gplus_comm.
Qed.

Theorem GMplus_assoc : forall (m n : nat) (A B C : GenMatrix m n), A .+ B .+ C = A .+ (B .+ C).
Proof.
  unfold GMplus. 
  intros m n A B C.
  prep_genmatrix_equality.
  rewrite Gplus_assoc.
  reflexivity.
Qed.


Theorem GMmult_assoc : forall {m n o p : nat} (A : GenMatrix m n) (B : GenMatrix n o) 
  (C: GenMatrix o p), A × B × C = A × (B × C).
Proof.
  intros m n o p A B C.
  unfold GMmult.
  prep_genmatrix_equality.
  replace (fun y0 : nat => Σ (fun y1 : nat => A x y1 * B y1 y0) n * C y0 y) with 
    (fun y0 : nat => Σ (fun y1 : nat => A x y1 * B y1 y0 * C y0 y) n).
  replace (fun y0 : nat => A x y0 * Σ (fun y1 : nat => B y0 y1 * C y1 y) o) with
    (fun y0 : nat => Σ (fun y1 : nat => A x y0 * (B y0 y1 * C y1 y)) o).
  rewrite big_sum_swap_order.
  do 2 (apply big_sum_eq_bounded; intros; dumb_lRa).  
  all : apply functional_extensionality; intros.  
  rewrite big_sum_mult_l; easy.
  rewrite big_sum_mult_r; easy.
Qed.


Lemma GMmult_plus_distr_l : forall (m n o : nat) (A : GenMatrix m n) (B C : GenMatrix n o), 
                           A × (B .+ C) = A × B .+ A × C.
Proof. 
  intros m n o A B C.
  unfold GMplus, GMmult.
  prep_genmatrix_equality.
  rewrite <- (@big_sum_plus F _ _ R2).
  apply big_sum_eq.
  apply functional_extensionality. intros z.
  rewrite Gmult_plus_distr_l. 
  reflexivity.
Qed.

Lemma GMmult_plus_distr_r : forall (m n o : nat) (A B : GenMatrix m n) (C : GenMatrix n o), 
                           (A .+ B) × C = A × C .+ B × C.
Proof. 
  intros m n o A B C.
  unfold GMplus, GMmult.
  prep_genmatrix_equality.
  rewrite <- (@big_sum_plus F _ _ R2).
  apply big_sum_eq.
  apply functional_extensionality. intros z.
  rewrite Gmult_plus_distr_r. 
  reflexivity.
Qed.

Lemma kron_plus_distr_l : forall (m n o p : nat) (A : GenMatrix m n) (B C : GenMatrix o p), 
                           A ⊗ (B .+ C) = A ⊗ B .+ A ⊗ C.
Proof. 
  intros m n o p A B C.
  unfold GMplus, Gkron.
  prep_genmatrix_equality.
  rewrite Gmult_plus_distr_l.
  easy.
Qed.

Lemma kron_plus_distr_r : forall (m n o p : nat) (A B : GenMatrix m n) (C : GenMatrix o p), 
                           (A .+ B) ⊗ C = A ⊗ C .+ B ⊗ C.
Proof. 
  intros m n o p A B C.
  unfold GMplus, Gkron.
  prep_genmatrix_equality.
  rewrite Gmult_plus_distr_r. 
  reflexivity.
Qed.

Lemma Mscale_0_l : forall (m n : nat) (A : GenMatrix m n), 0 .* A = Zero.
Proof.
  intros m n A.
  prep_genmatrix_equality.
  unfold Zero, scale.
  rewrite Gmult_0_l.
  reflexivity.
Qed.

Lemma Mscale_0_r : forall (m n : nat) (c : F), c .* @Zero F R0 m n = Zero.
Proof.
  intros m n c.
  prep_genmatrix_equality.
  unfold Zero, scale.
  rewrite Gmult_0_r.
  reflexivity.
Qed.

Lemma Mscale_1_l : forall (m n : nat) (A : GenMatrix m n), 1 .* A = A.
Proof.
  intros m n A.
  prep_genmatrix_equality.
  unfold scale.
  rewrite Gmult_1_l.
  reflexivity.
Qed.

Lemma Mscale_1_r : forall (n : nat) (c : F),
    c .* I n = fun x y => if (x =? y) && (x <? n) then c else 0.
Proof.
  intros n c.
  prep_genmatrix_equality.
  unfold scale, I.
  destruct ((x =? y) && (x <? n)).
  rewrite Gmult_1_r; reflexivity.
  rewrite Gmult_0_r; reflexivity.
Qed.

Lemma Mscale_assoc : forall (m n : nat) (x y : F) (A : GenMatrix m n),
  x .* (y .* A) = (x * y) .* A.
Proof.
  intros. unfold scale. prep_genmatrix_equality.
  rewrite Gmult_assoc; reflexivity.
Qed.

(* TODO: make this work when c is not a zero divisor 
Lemma Mscale_div : forall {n m} (c : F) (A B : GenMatrix n m),
  c <> C0 -> c .* A = c .* B -> A = B.
Proof. intros. 
       rewrite <- Mscale_1_l. rewrite <- (Mscale_1_l n m A).
       rewrite <- (Ginv_l c).
       rewrite <- Mscale_assoc.
       rewrite H0. 
       lma.
       apply H.
Qed.
*)


Lemma Mscale_plus_distr_l : forall (m n : nat) (x y : F) (A : GenMatrix m n),
  (x + y) .* A = x .* A .+ y .* A.
Proof.
  intros. unfold GMplus, scale. prep_genmatrix_equality. apply Gmult_plus_distr_r.
Qed.

Lemma Mscale_plus_distr_r : forall (m n : nat) (x : F) (A B : GenMatrix m n),
  x .* (A .+ B) = x .* A .+ x .* B.
Proof.
  intros. unfold GMplus, scale. prep_genmatrix_equality. apply Gmult_plus_distr_l.
Qed.

Lemma Mscale_mult_dist_l : forall (m n o : nat) (x : F) (A : GenMatrix m n) (B : GenMatrix n o), 
    ((x .* A) × B) = x .* (A × B).
Proof.
  intros m n o x A B.
  unfold scale, GMmult.
  prep_genmatrix_equality.
  rewrite (@big_sum_mult_l F _ _ _ R3). 
  apply big_sum_eq.
  apply functional_extensionality. intros z.
  rewrite Gmult_assoc.
  reflexivity.
Qed.

Lemma Mscale_mult_dist_r : forall (m n o : nat) (x : F) (A : GenMatrix m n) (B : GenMatrix n o),
    (A × (x .* B)) = x .* (A × B).
Proof.
  intros m n o x A B.
  unfold scale, GMmult.
  prep_genmatrix_equality.
  rewrite (@big_sum_mult_l F _ _ _ R3). 
  apply big_sum_eq.
  apply functional_extensionality. intros z.
  repeat rewrite Gmult_assoc.
  rewrite (Gmult_comm _ x).
  reflexivity.
Qed.

Lemma Mscale_kron_dist_l : forall (m n o p : nat) (x : F) (A : GenMatrix m n) (B : GenMatrix o p), 
    ((x .* A) ⊗ B) = x .* (A ⊗ B).
Proof.
  intros m n o p x A B.
  unfold scale, Gkron.
  prep_genmatrix_equality.
  rewrite Gmult_assoc.
  reflexivity.
Qed.

Lemma Mscale_kron_dist_r : forall (m n o p : nat) (x : F) (A : GenMatrix m n) (B : GenMatrix o p), 
    (A ⊗ (x .* B)) = x .* (A ⊗ B).
Proof.
  intros m n o p x A B.
  unfold scale, Gkron.
  prep_genmatrix_equality.
  rewrite Gmult_assoc.  
  rewrite (Gmult_comm (A _ _) x).
  rewrite Gmult_assoc.  
  reflexivity.
Qed.

Lemma Mscale_trans : forall (m n : nat) (x : F) (A : GenMatrix m n),
    (x .* A)⊤ = x .* A⊤.
Proof. reflexivity. Qed.

(*
Lemma Mscale_adj : forall (m n : nat) (x : F) (A : GenMatrix m n),
    (x .* A)† = x^* .* A†.
Proof.
  intros m n x A.
  unfold scale, adjoint.
  prep_genmatrix_equality.
  rewrite Cconj_mult_distr.          
  reflexivity.
Qed.
*)

Lemma GMplus_transpose : forall (m n : nat) (A : GenMatrix m n) (B : GenMatrix m n),
  (A .+ B)⊤ = A⊤ .+ B⊤.
Proof. reflexivity. Qed.

Lemma GMmult_transpose : forall (m n o : nat) (A : GenMatrix m n) (B : GenMatrix n o),
      (A × B)⊤ = B⊤ × A⊤.
Proof.
  intros m n o A B.
  unfold GMmult, transpose.
  prep_genmatrix_equality.
  apply big_sum_eq.  
  apply functional_extensionality. intros z.
  rewrite Gmult_comm.
  reflexivity.
Qed.

Lemma kron_transpose : forall {m n o p : nat} (A : GenMatrix m n) (B : GenMatrix o p ),
  (A ⊗ B)⊤ = A⊤ ⊗ B⊤.
Proof. reflexivity. Qed.

(*
Lemma GMplus_adjoint : forall (m n : nat) (A : GenMatrix m n) (B : GenMatrix m n),
  (A .+ B)† = A† .+ B†.
Proof.  
  intros m n A B.
  unfold GMplus, adjoint.
  prep_genmatrix_equality.
  rewrite Cconj_plus_distr.
  reflexivity.
Qed.
Lemma GMmult_adjoint : forall {m n o : nat} (A : GenMatrix m n) (B : GenMatrix n o),
      (A × B)† = B† × A†.
Proof.
  intros m n o A B.
  unfold GMmult, adjoint.
  prep_genmatrix_equality.
  rewrite (@big_sum_func_distr C C _ C_is_group _ C_is_group). (* not great *) 
  apply big_sum_eq.  
  apply functional_extensionality. intros z.
  rewrite Cconj_mult_distr.
  rewrite Cmult_comm.
  reflexivity.
  intros; lca. 
Qed.
Lemma kron_adjoint : forall {m n o p : nat} (A : GenMatrix m n) (B : GenMatrix o p),
  (A ⊗ B)† = A† ⊗ B†.
Proof. 
  intros. unfold adjoint, kron. 
  prep_genmatrix_equality.
  rewrite Cconj_mult_distr.
  reflexivity.
Qed.
*)


Lemma id_kron : forall (m n : nat),  I m ⊗ I n = I (m * n).
Proof.
  intros.
  unfold I, Gkron.
  prep_genmatrix_equality.
  bdestruct (x =? y); rename H into Eq; subst.
  + repeat rewrite Nat.eqb_refl; simpl.
    destruct n.
    - simpl.
      rewrite Nat.mul_0_r.
      bdestruct (y <? 0); try lia.
      ring. 
    - bdestruct (y mod S n <? S n). 
      2: specialize (Nat.mod_upper_bound y (S n)); intros; lia. 
      rewrite Gmult_1_r.
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
    bdestruct (x / n =? y / n); simpl; dumb_lRa.
    bdestruct (x mod n =? y mod n); simpl; dumb_lRa.
    destruct n; simpl; dumb_lRa.   
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
  (A : GenMatrix m n) (B : GenMatrix p q) (C : GenMatrix r s),
  (A ⊗ B ⊗ C) == A ⊗ (B ⊗ C).                                
Proof.
  intros. intros i j Hi Hj.
  remember (A ⊗ B ⊗ C) as LHS.
  unfold Gkron.  
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
  rewrite Gmult_assoc.
  subst.
  reflexivity.
Qed.  

Lemma kron_assoc : forall {m n p q r s : nat}
  (A : GenMatrix m n) (B : GenMatrix p q) (C : GenMatrix r s),
  WF_GenMatrix A -> WF_GenMatrix B -> WF_GenMatrix C ->
  (A ⊗ B ⊗ C) = A ⊗ (B ⊗ C).                                
Proof.
  intros.
  apply genmat_equiv_eq; auto with wf_db.
  apply WF_kron; auto with wf_db; lia.
  apply kron_assoc_mat_equiv.
Qed.  

Lemma kron_mixed_product : forall {m n o p q r : nat} (A : GenMatrix m n) (B : GenMatrix p q ) 
  (C : GenMatrix n o) (D : GenMatrix q r), (A ⊗ B) × (C ⊗ D) = (A × C) ⊗ (B × D).
Proof.
  intros m n o p q r A B C D.
  unfold Gkron, GMmult.
  prep_genmatrix_equality.
  destruct q.
  + simpl.
    rewrite Nat.mul_0_r.
    simpl.
    rewrite Gmult_0_r.
    reflexivity. 
  + rewrite (@big_sum_product F _ _ _ R3).
    apply big_sum_eq.
    apply functional_extensionality.
    intros; ring. 
    lia.
Qed.

(* Arguments kron_mixed_product [m n o p q r]. *)

(* A more explicit version, for when typechecking fails *)
Lemma kron_mixed_product' : forall (m n n' o p q q' r mp nq or: nat)
    (A : GenMatrix m n) (B : GenMatrix p q) (C : GenMatrix n' o) (D : GenMatrix q' r),
    n = n' -> q = q' ->    
    mp = m * p -> nq = n * q -> or = o * r ->
  (@GMmult F R0 R1 R2 R3 mp nq or 
           (@Gkron F R0 R1 R2 R3 m n p q A B) (@Gkron F R0 R1 R2 R3 n' o q' r C D)) =
  (@Gkron F R0 R1 R2 R3 m o p r 
          (@GMmult F R0 R1 R2 R3 m n o A C) (@GMmult F R0 R1 R2 R3 p q r B D)).
Proof. intros. subst. apply kron_mixed_product. Qed.


Lemma direct_sum_assoc : forall {m n p q r s : nat}
  (A : GenMatrix m n) (B : GenMatrix p q) (C : GenMatrix r s),
  (A .⊕ B .⊕ C) = A .⊕ (B .⊕ C).
Proof. intros. 
       unfold direct_sum. 
       prep_genmatrix_equality.
       bdestruct_all; simpl; auto.
       repeat (apply f_equal_gen; try lia); easy. 
Qed.
       
Lemma outer_product_eq : forall m (φ ψ : GenMatrix m 1),
 φ = ψ -> outer_product φ φ = outer_product ψ ψ.
Proof. congruence. Qed.

Lemma outer_product_kron : forall m n (φ : GenMatrix m 1) (ψ : GenMatrix n 1), 
    outer_product φ φ ⊗ outer_product ψ ψ = outer_product (φ ⊗ ψ) (φ ⊗ ψ).
Proof. 
  intros. unfold outer_product. 
  specialize (kron_transpose φ ψ) as KT. 
  simpl in *. rewrite KT.
  specialize (kron_mixed_product φ ψ (φ⊤) (ψ⊤)) as KM. 
  simpl in *. rewrite KM.
  reflexivity.
Qed.



Lemma big_kron_app : forall {n m} (l1 l2 : list (GenMatrix n m)),
  (forall i, WF_GenMatrix (nth i l1 (@Zero F R0 n m))) ->
  (forall i, WF_GenMatrix (nth i l2 (@Zero F R0 n m))) ->
  ⨂ (l1 ++ l2) = (⨂ l1) ⊗ (⨂ l2).
Proof. induction l1.
       - intros. simpl. rewrite (kron_1_l _ _ (⨂ l2)); try easy.
         apply (WF_big_kron _ _ _ (@Zero F R0 n m)); easy.
       - intros. simpl. rewrite IHl1. 
         rewrite kron_assoc.
         do 2 (rewrite <- Nat.pow_add_r).
         rewrite app_length.
         reflexivity.
         assert (H' := H 0); simpl in H'; easy.
         all : try apply (WF_big_kron _ _ _ (@Zero F R0 n m)); try easy. 
         all : intros. 
         all : assert (H' := H (S i)); simpl in H'; easy.
Qed.

Lemma kron_n_assoc :
  forall n {m1 m2} (A : GenMatrix m1 m2), WF_GenMatrix A -> (S n) ⨂ A = A ⊗ (n ⨂ A).
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

(*
Lemma kron_n_adjoint : forall n {m1 m2} (A : GenMatrix m1 m2),
  WF_GenMatrix A -> (n ⨂ A)† = n ⨂ A†.
Proof.
  intros. induction n.
  - simpl. apply id_adjoint_eq.
  - simpl.
    replace (m1 * (m1 ^ n)) with ((m1 ^ n) * m1) by apply Nat.mul_comm.
    replace (m2 * (m2 ^ n)) with ((m2 ^ n) * m2) by apply Nat.mul_comm.
    rewrite kron_adjoint, IHn.
    reflexivity.
Qed. *)

Lemma kron_n_transpose : forall (m n o : nat) (A : GenMatrix m n),
  (o ⨂ A)⊤ = o ⨂ (A⊤). 
Proof. 
  induction o; intros.
  - apply id_transpose_eq.
  - simpl; rewrite <- IHo; rewrite <- kron_transpose; reflexivity. 
Qed.

(* TODO: make Gpow *) (*
Lemma Mscale_kron_n_distr_r : forall {m1 m2} n α (A : GenMatrix m1 m2),
  n ⨂ (α .* A) = (α ^ n)%G .* (n ⨂ A).
Proof.
  intros.
  induction n; simpl.
  rewrite Mscale_1_l. reflexivity.
  rewrite IHn. 
  rewrite Mscale_kron_dist_r, Mscale_kron_dist_l. 
  rewrite Mscale_assoc.
  reflexivity.
Qed.
 *)


Lemma kron_n_mult : forall {m1 m2 m3} n (A : GenMatrix m1 m2) (B : GenMatrix m2 m3),
  n ⨂ A × n ⨂ B = n ⨂ (A × B).
Proof.
  intros.
  induction n; simpl.
  rewrite GMmult_1_l. reflexivity.
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

Lemma GMmult_n_kron_distr_l : forall {m n} i (A : Square m) (B : Square n),
  i ⨉ (A ⊗ B) = (i ⨉ A) ⊗ (i ⨉ B).
Proof.
  intros m n i A B.
  induction i; simpl.
  rewrite id_kron; reflexivity.
  rewrite IHi.
  rewrite kron_mixed_product.
  reflexivity.
Qed.

Lemma GMmult_n_1_l : forall {n} (A : Square n),
  WF_GenMatrix A ->
  1 ⨉ A = A.
Proof. intros n A WF. simpl. rewrite GMmult_1_r; auto. Qed.


Lemma GMmult_n_1_r : forall n i,
  i ⨉ (I n) = I n.
Proof.
  intros n i.
  induction i; simpl.
  reflexivity.
  rewrite IHi.  
  rewrite GMmult_1_l; auto with wf_db.
Qed.


Lemma GMmult_n_add : forall {n} (A : Square n) (a b : nat),
  WF_GenMatrix A ->
  ((a + b) ⨉ A) = (a ⨉ A) × (b ⨉ A).
Proof. intros. 
       induction a; simpl.
       - rewrite GMmult_1_l; auto with wf_db.
       - rewrite IHa, GMmult_assoc; easy.
Qed.

Lemma GMmult_n_mult_r : forall {n} (A : Square n) (a b : nat),
  WF_GenMatrix A ->
  b ⨉ (a ⨉ A) = ((a*b) ⨉ A).
Proof. intros. 
       induction b; simpl.
       - replace (a * 0) with 0 by lia; easy. 
       - replace (a * S b) with (a + a * b) by lia.
         rewrite GMmult_n_add, <- IHb; auto.
Qed.

  
(*
Lemma GMmult_n_eigenvector : forall {n} (A : Square n) (ψ : Vector n) λ i,
  WF_GenMatrix ψ -> A × ψ = λ .* ψ ->
  i ⨉ A × ψ = (λ ^ i) .* ψ.
Proof.
  intros n A ψ λ i WF H.
  induction i; simpl.
  rewrite GMmult_1_l; auto.
  rewrite Mscale_1_l; auto.
  rewrite GMmult_assoc.
  rewrite IHi.
  rewrite Mscale_mult_dist_r.
  rewrite H.
  rewrite Mscale_assoc.
  rewrite Cmult_comm.
  reflexivity.
Qed.
*)





(** * Summation lemmas specific to matrices **)

(* due to dimension problems, we did not prove that GenMatrix m n is a ring with respect to either
   multiplication or kron. Thus all of these need to be proven *)
Lemma kron_Msum_distr_l : 
  forall {d1 d2 d3 d4} n (f : nat -> GenMatrix d1 d2) (A : GenMatrix d3 d4),
  A ⊗ big_sum f n = big_sum (fun i => A ⊗ f i) n.
Proof.
  intros.
  induction n; simpl. lgma.
  rewrite kron_plus_distr_l, IHn. reflexivity.
Qed.

Lemma kron_Msum_distr_r : 
  forall {d1 d2 d3 d4} n (f : nat -> GenMatrix d1 d2) (A : GenMatrix d3 d4),
  big_sum f n ⊗ A = big_sum (fun i => f i ⊗ A) n.
Proof.
  intros.
  induction n; simpl. lgma.
  rewrite kron_plus_distr_r, IHn. reflexivity.
Qed.

Lemma GMmult_Msum_distr_l : forall {d1 d2 m} n (f : nat -> GenMatrix d1 d2) (A : GenMatrix m d1),
  A × big_sum f n = big_sum (fun i => A × f i) n.
Proof.
  intros.
  induction n; simpl. 
  rewrite GMmult_0_r. reflexivity.
  rewrite GMmult_plus_distr_l, IHn. reflexivity.
Qed.

Lemma GMmult_Msum_distr_r : forall {d1 d2 m} n (f : nat -> GenMatrix d1 d2) (A : GenMatrix d2 m),
  big_sum f n × A = big_sum (fun i => f i × A) n.
Proof.
  intros.
  induction n; simpl. 
  rewrite GMmult_0_l. reflexivity.
  rewrite GMmult_plus_distr_r, IHn. reflexivity.
Qed.

Lemma Mscale_Msum_distr_r : forall {d1 d2} n (c : F) (f : nat -> GenMatrix d1 d2),
  big_sum (fun i => c .* (f i)) n = c .* big_sum f n.
Proof.
  intros d1 d2 n c f.
  induction n; simpl. lgma.
  rewrite Mscale_plus_distr_r, IHn. reflexivity.
Qed.

Lemma Mscale_Msum_distr_l : forall {d1 d2} n (f : nat -> F) (A : GenMatrix d1 d2),
  big_sum (fun i => (f i) .* A) n = big_sum f n .* A.
Proof.
  intros d1 d2 n f A.
  induction n; simpl. lgma.
  rewrite Mscale_plus_distr_l, IHn. reflexivity.
Qed.

(* TODO: add NtoG in Summation.v *)
(*
Lemma Msum_constant : forall {d1 d2} n (A : GenMatrix d1 d2),  big_sum (fun _ => A) n = INR n .* A.
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
*)


(*
Lemma Msum_adjoint : forall {d1 d2} n (f : nat -> GenMatrix d1 d2),
  (big_sum f n)† = big_sum (fun i => (f i)†) n.
Proof.
  intros.
  induction n; simpl.
  lma.
  rewrite GMplus_adjoint, IHn.  
  reflexivity.
Qed.
*)


Lemma Msum_Fsum : forall {d1 d2} n (f : nat -> GenMatrix d1 d2) i j,
  (big_sum f n) i j = big_sum (fun x => (f x) i j) n.
Proof.
  intros. 
  induction n; simpl.
  reflexivity.
  unfold GMplus.
  rewrite IHn.
  reflexivity.
Qed.

Lemma Msum_plus : forall n {d1 d2} (f g : nat -> GenMatrix d1 d2), 
    big_sum (fun x => f x .+ g x) n = big_sum f n .+ big_sum g n.
Proof.
  intros.
  induction n; simpl.
  lgma.
  rewrite IHn. lgma.
Qed.


Local Close Scope nat_scope.

(* some inner product lemmas *)
Lemma inner_product_scale_l : forall {n} (u v : Vector n) (c : F),
  ⟨c .* u, v⟩ = c * ⟨u,v⟩.
Proof. intros.
       unfold inner_product, scale, transpose, GMmult.
       rewrite (@big_sum_mult_l F _ _ _ R3).
       apply big_sum_eq_bounded; intros.
       ring.
Qed.       

Lemma inner_product_scale_r : forall {n} (u v : Vector n) (c : F),
  ⟨u, c .* v⟩ = c * ⟨u,v⟩.
Proof. intros.
       unfold inner_product, scale, transpose, GMmult.
       rewrite (@big_sum_mult_l F _ _ _ R3).
       apply big_sum_eq_bounded; intros.
       ring.
Qed.       

Lemma inner_product_plus_l : forall {n} (u v w : Vector n),
  ⟨u .+ v, w⟩ = ⟨u, w⟩ + ⟨v, w⟩.
Proof. intros.
       unfold inner_product, scale, transpose, GMplus, GMmult.
       rewrite <- (@big_sum_plus F _ _ R2).
       apply big_sum_eq_bounded; intros.
       ring.
Qed.       

Lemma inner_product_plus_r : forall {n} (u v w : Vector n),
  ⟨u, v .+ w⟩ = ⟨u, v⟩ + ⟨u, w⟩.
Proof. intros.
       unfold inner_product, scale, transpose, GMplus, GMmult.
       rewrite <- (@big_sum_plus F _ _ R2).
       apply big_sum_eq_bounded; intros.
       ring.
Qed.          

Lemma inner_product_big_sum_l : forall {n} (u : Vector n) (f : nat -> Vector n) (k : nat),
  ⟨big_sum f k, u⟩ = big_sum (fun i => ⟨f i, u⟩) k.
Proof. induction k.
       - unfold inner_product; simpl.
         rewrite (zero_transpose_eq n 1), (GMmult_0_l 1 n); easy.
       - simpl. 
         rewrite inner_product_plus_l, IHk.
         reflexivity.
Qed.       

Lemma inner_product_big_sum_r : forall {n} (u : Vector n) (f : nat -> Vector n) (k : nat),
  ⟨u, big_sum f k⟩ = big_sum (fun i => ⟨u, f i⟩) k.
Proof. induction k.
       - unfold inner_product; simpl.
         rewrite GMmult_0_r; easy.
       - simpl. 
         rewrite inner_product_plus_r, IHk.
         reflexivity.
Qed.       

Lemma inner_product_conj_sym : forall {n} (u v : Vector n),
  ⟨u, v⟩ = ⟨v, u⟩.
Proof. intros. 
       unfold inner_product, transpose, GMmult.
       apply big_sum_eq_bounded; intros.
       ring.
Qed.

Lemma inner_product_mafe_WF_l : forall {n} (u v : Vector n),
  ⟨u, v⟩ = ⟨make_WF u, v⟩.
Proof. intros. 
       unfold inner_product, transpose, GMmult, make_WF.
       apply big_sum_eq_bounded; intros.
       bdestruct_all; simpl; easy.
Qed.

Lemma inner_product_mafe_WF_r : forall {n} (u v : Vector n),
  ⟨u, v⟩ = ⟨u, make_WF v⟩.
Proof. intros. 
       unfold inner_product, transpose, GMmult, make_WF.
       apply big_sum_eq_bounded; intros.
       bdestruct_all; simpl; easy.
Qed.



(* TODO: could add norm, but need field for everything else 
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
  intros d ψ. unfold inner_product, GMmult.
  replace (fun y : nat => (ψ† O y * ψ y O)%G) with (fun y : nat => RtoC (Cmod (ψ y O) ^ 2)).
  apply Rsum_big_sum.
  apply functional_extensionality. intros.
  unfold adjoint. rewrite <- Cmod_sqr. symmetry. apply RtoC_pow.
Qed.
Local Open Scope nat_scope.
Lemma norm_real : forall {n} (v : Vector n), snd ⟨v,v⟩ = 0%R. 
Proof. intros. unfold inner_product, GMmult, adjoint.
       rewrite big_sum_snd_0. easy.
       intros. rewrite Gmult_comm.
       rewrite Gmult_conj_real.
       reflexivity.
Qed.
Lemma inner_product_ge_0 : forall {d} (ψ : Vector d),
  (0 <= fst ⟨ψ,ψ⟩)%R.
Proof.
  intros.
  unfold inner_product, GMmult, adjoint.
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
  WF_GenMatrix v -> (⟨v,v⟩ = 0%G <-> v = Zero). 
Proof. intros. split. 
       - intros. 
         destruct (genmat_equiv_dec v Zero).
         apply genmat_equiv_eq; try easy.
         assert (H' : v <> Zero). 
         { unfold not; intros. 
           apply n0. rewrite H1.
           easy. }
         apply nonzero_vec_nonzero_elem in H'; try easy.
         destruct H'. 
         unfold WF_GenMatrix in H.
         bdestruct (x <? n).
         assert (H0' := Rle_0_sqr).  
         unfold Rsqr in H0'. 
         assert (H' : (0 < fst (inner_product v v))%R).
         { unfold inner_product.
           unfold GMmult. 
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
         assert (H' : v x O = 0%G).
         { apply H. left; easy. }
         rewrite H' in H1; easy. 
       - intros. 
         unfold inner_product.  
         rewrite H0. 
         rewrite GMmult_0_r. 
         easy.
Qed.
Lemma norm_zero_iff_zero : forall {n} (v : Vector n),
  WF_GenMatrix v -> (norm v = 0%R <-> v = Zero). 
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
         rewrite GMmult_0_r. 
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
           ( ⟨ v, u ⟩^* * ⟨ v, u ⟩ * ⟨ v, v ⟩ ) by ring.       
         replace ((-1 * ⟨ v, u ⟩) ^* * (⟨ v, v ⟩ * ⟨ v, u ⟩) +
                    ⟨ v, u ⟩ ^* * ⟨ v, u ⟩ * ⟨ v, v ⟩) with 0%G by ring.
         rewrite (inner_product_conj_sym v u), <- (inner_product_conj_sym v v).
         rewrite <- Gmult_assoc.   
         replace (⟨ u, v ⟩ ^* * ⟨ u, v ⟩) with (Cmod ⟨ u, v ⟩ ^ 2) by apply Cmod_sqr.
         ring.
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
         rewrite Gmult_comm, Gmult_conj_real; easy. 
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
         rewrite H', GMmult_0_r.
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
     Cmod (big_sum (fun i => ((u i O)^* * (v i O))%G) n) ^ 2)%R.
Proof. intros.
       assert (H := Cauchy_Schwartz_ver1 u v).
       replace (big_sum (fun i : nat => (Cmod (u i 0%nat) ^ 2)%R) n) with (fst ⟨ u, u ⟩).
       replace (big_sum (fun i : nat => (Cmod (v i 0%nat) ^ 2)%R) n) with (fst ⟨ v, v ⟩).
       replace (Σ (fun i : nat => (u i 0%nat) ^* * v i 0%nat) n) with (⟨ u, v ⟩).
       lra.
       all : unfold inner_product, adjoint, GMmult; try easy. 
       all : rewrite (@big_sum_func_distr C R _ C_is_group _ R_is_group).
       all : try apply big_sum_eq_bounded; intros.
       all : try rewrite <- Cmod_sqr. 
       all : try (destruct a; destruct b; simpl; easy).
       destruct (v x 0%nat); unfold Cmod, pow, Gmult; simpl; lra. 
       destruct (u x 0%nat); unfold Cmod, pow, Gmult; simpl; lra. 
Qed.
Local Open Scope nat_scope.
Lemma Cplx_Cauchy :
  forall n (u v : nat -> C),
    ((big_sum (fun i => Cmod (u i) ^ 2) n) * (big_sum (fun i => Cmod (v i) ^ 2) n) >= Cmod (big_sum (fun i => ((u i)^* * (v i))%G) n) ^ 2)%R.
Proof. intros. 
       assert (H := Cplx_Cauchy_vector n (fun i j => u i) (fun i j => v i)).
       simpl in *.
       easy. 
Qed.       
*)



  
(** Printing *)


Local Open Scope nat_scope.


Parameter print_F : F -> string.
Fixpoint print_row {m n} i j (A : GenMatrix m n) : string :=
  match j with
  | 0   => "\n"
  | S j' => print_F (A i j') ++ ", " ++ print_row i j' A
  end.
Fixpoint print_rows {m n} i j (A : GenMatrix m n) : string :=
  match i with
  | 0   => ""
  | S i' => print_row i' n A ++ print_rows i' n A
  end.
Definition print_genmatrix {m n} (A : GenMatrix m n) : string :=
  print_rows m n A.


Local Close Scope nat_scope.



(** * Tactics **)


(* Note on "using [tactics]": Most generated subgoals will be of the form
   WF_GenMatrix M, where auto with wf_db will work.
   Occasionally WF_GenMatrix M will rely on rewriting to match an assumption in the
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
  (m <= n)%nat -> (x < m)%nat -> nth x (vec_to_list' m v) 0 = v (n - m + x)%nat O.
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
  (x < n)%nat -> nth x (vec_to_list v) 0 = v x O.
Proof.
  intros.
  unfold vec_to_list.
  rewrite nth_vec_to_list' by lia.
  replace (n - n + x)%nat with x by lia.
  reflexivity.
Qed.


  


  


(** Restoring GenMatrix dimensions *)
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
                        | GenMatrix ?m' ?n' => 
                            constr:(@GMmult F R0 R1 R2 R3 m' n' n' A' (I n'))
                        end
  | I _ × ?B          => let B' := restore_dims_rec B in 
                        match type of B' with 
                        | GenMatrix ?n' ?o' => 
                            constr:(@GMmult F R0 R1 R2 R3 n' n' o' (I n')  B')
                        end
  | ?A × @Zero F R0 ?n ?n  => let A' := restore_dims_rec A in 
                        match type of A' with 
                        | GenMatrix ?m' ?n' => 
                            constr:(@GMmult F R0 R1 R2 R3 m' n' n' A' (@Zero F R0 n' n'))
                        end
  | @Zero F R0 ?n ?n × ?B  => let B' := restore_dims_rec B in 
                        match type of B' with 
                        | GenMatrix ?n' ?o' => 
                            constr:(@GMmult F R0 R1 R2 R3 n' n' o' (@Zero F R0 n' n') B')
                        end
  | ?A × @Zero F R0 ?n ?o  => let A' := restore_dims_rec A in 
                        match type of A' with 
                        | GenMatrix ?m' ?n' => 
                            constr:(@GMmult F R0 R1 R2 R3 m' n' o A' (@Zero F R0 n' o))
                        end
  | @Zero F R0 ?m ?n × ?B  => let B' := restore_dims_rec B in 
                        match type of B' with 
                        | GenMatrix ?n' ?o' => 
                            constr:(@GMmult F R0 R1 R2 R3 n' n' o' (@Zero F R0 m n') B')
                        end
  | ?A .+ @Zero F R0 ?m ?n => let A' := restore_dims_rec A in 
                        match type of A' with 
                        | GenMatrix ?m' ?n' => 
                            constr:(@GMplus F R0 R1 R2 R3 m' n' A' (@Zero F R0 m' n'))
                        end
  | @Zero F R0 ?m ?n .+ ?B => let B' := restore_dims_rec B in 
                        match type of B' with 
                        | GenMatrix ?m' ?n' => 
                            constr:(@GMplus F R0 R1 R2 R3 m' n' (@Zero F R0 m' n') B')
                        end
(* general cases *)
  | ?A = ?B  => let A' := restore_dims_rec A in 
                let B' := restore_dims_rec B in 
                match type of A' with 
                | GenMatrix ?m' ?n' => 
                    constr:(@eq (GenMatrix m' n') A' B')
                  end
  | ?A × ?B   => let A' := restore_dims_rec A in 
                let B' := restore_dims_rec B in 
                match type of A' with 
                | GenMatrix ?m' ?n' =>
                  match type of B' with 
                  | GenMatrix ?n'' ?o' => 
                      constr:(@GMmult F R0 R1 R2 R3 m' n' o' A' B')
                  end
                end 
  | ?A ⊗ ?B   => let A' := restore_dims_rec A in 
                let B' := restore_dims_rec B in 
                match type of A' with 
                | GenMatrix ?m' ?n' =>
                  match type of B' with 
                  | GenMatrix ?o' ?p' => 
                      constr:(@Gkron F R0 R1 R2 R3 m' n' o' p' A' B')
                  end
                end
  (* | ?A †      => let A' := restore_dims_rec A in 
                match type of A' with
                | GenMatrix ?m' ?n' => constr:(@adjoint m' n' A')
                end *)
  | ?A .+ ?B => let A' := restore_dims_rec A in 
               let B' := restore_dims_rec B in 
               match type of A' with 
               | GenMatrix ?m' ?n' =>
                 match type of B' with 
                 | GenMatrix ?m'' ?n'' => 
                     constr:(@GMplus F R0 m' n' A' B')
                 end
               end
  | ?c .* ?A => let A' := restore_dims_rec A in 
               match type of A' with
               | GenMatrix ?m' ?n' => 
                   constr:(@scale F R0 R1 R2 R3 m' n' c A')
               end
  | ?n ⨂ ?A => let A' := restore_dims_rec A in
               match type of A' with
               | GenMatrix ?m' ?n' => 
                   constr:(@kron_n F R0 R1 R2 R3 n m' n' A')
               end
  (* For predicates (eg. WF_GenMatrix, Mixed_State) on Matrices *)
  | ?P ?m ?n ?A => match type of P with
                  | nat -> nat -> GenMatrix _ _ -> Prop =>
                    let A' := restore_dims_rec A in 
                    match type of A' with
                    | GenMatrix ?m' ?n' => constr:(P m' n' A')
                    end
                  end
  | ?P ?n ?A => match type of P with
               | nat -> GenMatrix _ _ -> Prop =>
                 let A' := restore_dims_rec A in 
                 match type of A' with
                 | GenMatrix ?m' ?n' => constr:(P m' A')
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


Lemma kron_n_m_split {o p} : forall n m (A : GenMatrix o p), 
  WF_GenMatrix A -> (n + m) ⨂ A = n ⨂ A ⊗ m ⨂ A.
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


(** GenMatrix Simplification *)


(* Old: 
Hint Rewrite kron_1_l kron_1_r GMmult_1_l GMmult_1_r id_kron id_adjoint_eq
     @GMmult_adjoint GMplus_adjoint @kron_adjoint @kron_mixed_product
     id_adjoint_eq adjoint_involutive using 
     (auto 100 with wf_db; autorewrite with M_db; auto 100 with wf_db; lia) : M_db.
*)

(* eauto will cause major choking... *)
Hint Rewrite  @kron_1_l @kron_1_r @GMmult_1_l @GMmult_1_r @Mscale_1_l 
     (* @id_adjoint_eq *) @id_transpose_eq using (auto 100 with wf_db) : M_db_light.
Hint Rewrite @kron_0_l @kron_0_r @GMmult_0_l @GMmult_0_r @GMplus_0_l @GMplus_0_r
     @Mscale_0_l @Mscale_0_r (* @zero_adjoint_eq *) @zero_transpose_eq using (auto 100 with wf_db) : M_db_light.

(* I don't like always doing restore_dims first, but otherwise sometimes leaves 
   unsolvable WF_GenMatrix goals. *)
Ltac Msimpl_light := try restore_dims; autorewrite with M_db_light.

Hint Rewrite (* @GMmult_adjoint @GMplus_adjoint @kron_adjoint *) @kron_mixed_product
     (* @adjoint_involutive *)  using (auto 100 with wf_db) : M_db.

Ltac Msimpl := try restore_dims; autorewrite with M_db_light M_db.

(** Distribute addition to the outside of matrix expressions. *)

Ltac distribute_plus :=
  repeat match goal with 
  | |- context [?a × (?b .+ ?c)] => rewrite (GMmult_plus_distr_l _ _ _ a b c)
  | |- context [(?a .+ ?b) × ?c] => rewrite (GMmult_plus_distr_r _ _ _ a b c)
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


(*
Ltac distribute_adjoint :=
  repeat match goal with
  | |- context [(?c .* ?A)†] => rewrite (Mscale_adj _ _ c A)
  | |- context [(?A .+ ?B)†] => rewrite (GMplus_adjoint _ _ A B)
  | |- context [(?A × ?B)†] => rewrite (GMmult_adjoint A B)
  | |- context [(?A ⊗ ?B)†] => rewrite (kron_adjoint A B)
  end.
*)

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
                        in constr:(list2D_to_genmatrix ls2d).   

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
  | [|- context[@GMmult ?m ?o ?p (@GMmult ?m ?n ?o ?A ?B) ?C]] => tac_lt p o; tac_lt p m; 
       let H := fresh "H" in 
       specialize (GMmult_assoc A B C) as H; simpl in H; rewrite H; clear H
  | [|- context[@GMmult ?m ?o ?p (@GMmult ?m ?n ?o ?A ?B) ?C]] => tac_lt n o; tac_lt n m; 
       let H := fresh "H" in 
       specialize (GMmult_assoc  A B C) as H; simpl in H; rewrite H; clear H
  | [|- context[@GMmult ?m ?n ?p ?A (@GMmult ?n ?o ?p ?B ?C)]] => tac_lt m n; tac_lt m p; 
       let H := fresh "H" in 
       specialize (GMmult_assoc A B C) as H; simpl in H; rewrite <- H; clear H
  | [|- context[@GMmult ?m ?n ?p ?A (@GMmult ?n ?o ?p ?B ?C)]] => tac_lt o n; tac_lt o p; 
       let H := fresh "H" in 
       specialize (GMmult_assoc A B C) as H; simpl in H; rewrite <- H; clear H
  end).


(* Helper function for crunch_matrix *)
Ltac solve_out_of_bounds := 
  repeat match goal with 
  | [H : WF_GenMatrix ?M |- context[?M ?a ?b] ] => 
      rewrite (H a b) by (left; simpl; lia) 
  | [H : WF_GenMatrix ?M |- context[?M ?a ?b] ] => 
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
                 | 0%nat   => _
                 | S _ => _
                 end] ] => is_var x; destruct x
  | [ |- context[match fst (Nat.divmod ?x _ _ _) with 
                 | 0%nat   => _
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
                      unfold list2D_to_genmatrix;    
                      autounfold with U_db;
                      prep_genmatrix_equality;
                      simpl;
                      destruct_m_eq';
                      simpl;
                      dumb_lRa; (* basic rewrites only *) 
                      try reflexivity;
                      try solve_out_of_bounds. 

Ltac compound M := 
  match M with
  | ?A × ?B  => idtac
  | ?A .+ ?B => idtac 
  (* | ?A †     => compound A *)
  end.

(* Reduce inner matrices first *)
Ltac reduce_aux M := 
  match M with 
  | ?A .+ ?B     => compound A; reduce_aux A
  | ?A .+ ?B     => compound B; reduce_aux B
  | ?A × ?B      => compound A; reduce_aux A
  | ?A × ?B      => compound B; reduce_aux B
  | @GMmult ?m ?n ?o ?A ?B      => let M' := evar_matrix m o in
                                 replace M with M';
                                 [| crunch_matrix ] 
  | @GMplus ?m ?n ?A ?B         => let M' := evar_matrix m n in
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
                     ring.
                     (* autorewrite with C_db; try ring. *)

(** Gridify **)


(** Gridify: Turns an matrix expression into a normal form with 
    plus on the outside, then tensor, then matrix multiplication.
    Eg: ((..×..×..)⊗(..×..×..)⊗(..×..×..)) .+ ((..×..)⊗(..×..))
*)
Local Open Scope nat_scope.

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
               | GenMatrix 2 2 => constr:(1)
               | GenMatrix 4 4 => constr:(2)
               | GenMatrix (2^?a) (2^?a) => constr:(a)
(*             | GenMatrix ?a ?b => idtac "bad dims";
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


Definition Gkron' := @Gkron.      
Lemma kron_shadow : @Gkron = Gkron'. Proof. reflexivity. Qed.

Definition GMmult' := @GMmult.
Lemma GMmult_shadow : @GMmult = GMmult'. Proof. reflexivity. Qed.

Ltac show_dimensions := try rewrite kron_shadow in *; 
                        try rewrite GMmult_shadow in *.
Ltac hide_dimensions := try rewrite <- kron_shadow in *; 
                        try rewrite <- GMmult_shadow in *.



(*
End LinAlgOverCommRing.
*)


  
End LinAlgOverCommRing.

(* TODO: add more of these *)

(*
Arguments WF_GenMatrix {F R0 m n}.

Arguments make_WF {F R0 m n}.



Arguments Zero {F R0 m n}.
Arguments I {F R0 R1 R2 R3 n}.


Arguments trace {F R0 n}.
Arguments scale {F R0 R1 R2 R3 m n}.
Arguments GMplus {F R0 m n}.
Arguments GMopp {F R0 R1 R2 R3 m n}.
Arguments GMminus {F R0 R1 R2 R3 m n}.
Arguments GMmult {F R0 R1 R2 R3 m n o}.
Arguments Gkron {F R0 R1 R2 R3 m n o p}.
Arguments transpose {F m n}.
Arguments GMmult_n {F R0 R1 R2 R3 m}.


*)

