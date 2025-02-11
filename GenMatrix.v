
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


Module Type FieldModule.
Parameter (F : Type)
  (R0 : Monoid F) (R1 : Group F)
  (R2 : Comm_Group F) (R3 : Ring F) 
  (R4 : Comm_Ring F) (R5 : Field F).

Definition F_field_theory : field_theory 0%G 1%G Gplus Gmult Gminus Gopp Gdiv Ginv eq := @G_field_theory F R0 R1 R2 R3 R4 R5.

Add Field F_field : F_field_theory.

#[export] Existing Instance R0.
#[export] Existing Instance R1.
#[export] Existing Instance R2.
#[export] Existing Instance R3.
#[export] Existing Instance R4.
#[export] Existing Instance R5.
End FieldModule.


Module LinAlgOverField
  (FM : FieldModule).

Include FM.

Lemma nonzero_div_nonzero : forall c : F, c <> 0%G -> / c <> 0%G.
Proof. intros. 
       unfold not; intros. 
        assert (H' : (c * (/ c) = c * 0%G)%G). 
        { rewrite H0; easy. } 
        rewrite Ginv_r in H'; try easy.
        rewrite Gmult_0_r in H'.
        apply G1_neq_0; easy.
Qed.

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


Definition GenMatrix (m n : nat) := nat -> nat -> F.

Definition WF_GenMatrix {m n: nat} (A : GenMatrix m n) : Prop := 
  forall x y, x >= m \/ y >= n -> A x y = 0. 

Definition make_WF {n m} (S : GenMatrix n m) : GenMatrix n m :=
  fun i j => if (i <? n) && (j <? m) then S i j else 0%G.

Notation GenVector n := (GenMatrix n 1).
Notation GenSquare n := (GenMatrix n n).

(** Equality via functional extensionality *)
Ltac prep_genmatrix_equality :=
  let x := fresh "x" in 
  let y := fresh "y" in 
  apply functional_extensionality; intros x;
  apply functional_extensionality; intros y.

(** Matrix equivalence *)

Definition genmat_equiv {m n : nat} (A B : GenMatrix m n) : Prop := 
  forall i j, i < m -> j < n -> A i j = B i j.

Infix "==" := genmat_equiv (at level 70) : genmatrix_scope.

Lemma genmat_equiv_refl : forall m n (A : GenMatrix m n), genmat_equiv A A.
Proof. unfold genmat_equiv; reflexivity. Qed.

Lemma genmat_equiv_eq : forall {m n : nat} (A B : GenMatrix m n),
  WF_GenMatrix A -> 
  WF_GenMatrix B -> 
  A == B ->
  A = B.
Proof.
  intros m n A' B' WFA WFB Eq.
  prep_genmatrix_equality.
  unfold genmat_equiv in Eq.
  bdestruct (x <? m).
  bdestruct (y <? n).
  + apply Eq; easy.
  + rewrite WFA, WFB; trivial; right; try lia.
  + rewrite WFA, WFB; trivial; left; try lia.
Qed.

(** Printing *)

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

(** 2D list representation *)
    
Definition list2D_to_genmatrix (l : list (list F)) : 
  GenMatrix (length l) (length (hd [] l)) :=
  (fun x y => nth y (nth x l []) 0).

Lemma WF_list2D_to_genmatrix : forall m n li, 
    length li = m ->
    (forall li', In li' li -> length li' = n)  ->
    @WF_GenMatrix m n (list2D_to_genmatrix li).
Proof.
  intros m n li L f x y [l | r].
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
Definition M23 : GenMatrix 2 3 :=
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

Definition M23' : GenMatrix 2 3 := 
  list2D_to_genmatrix  
  ([ [1; 1+1; 1+1+1];
    [1+1+1+1; 1+1+1+1+1; 1+1+1+1+1+1] ]).

Lemma M23eq : M23 = M23'.
Proof.
  unfold M23'.
  compute.
  prep_genmatrix_equality.
  do 4 (try destruct x; try destruct y; simpl; trivial).
Qed.


(** * Operands and operations **)


Definition Zero {m n : nat} : GenMatrix m n := fun x y => 0.

Definition I (n : nat) : GenSquare n := 
  (fun x y => if (x =? y) && (x <? n) then 1 else 0).


(* in many cases, n needs to be made explicit, but not always, hence it is made implicit here *)
Definition e_i {n : nat} (i : nat) : GenVector n :=
  fun x y => (if (x =? i) && (x <? n) && (y =? 0) then 1 else 0). 



(* Optional coercion to scalar (should be limited to 1 × 1 matrices):
Definition to_scalar (m n : nat) (A: GenMatrix m n) : F := A 0 0.
Coercion to_scalar : GenMatrix >-> F.
*)

(* This isn't used, but is interesting *)
Definition I__inf := fun x y => if x =? y then 1 else 0.
Notation "I∞" := I__inf : genmatrix_scope.



(*TODO: the placement of G's is horribly inconsistent... can probably be fixed since
 eventually Matrix n m will be something more specific like CMatrix n m *)
Definition trace {n : nat} (A : GenSquare n) := 
  big_sum (fun x => A x x) n.

Definition scale {m n : nat} (r : F) (A : GenMatrix m n) : GenMatrix m n := 
  fun x y => (r * A x y).

Definition dot {n : nat} (A : GenVector n) (B : GenVector n) : F :=
  big_sum (fun x => A x 0  * B x 0) n.

Definition GMplus {m n : nat} (A B : GenMatrix m n) : GenMatrix m n :=
  fun x y => (A x y + B x y).

Definition GMopp {m n : nat} (A : GenMatrix m n) : GenMatrix m n :=
  scale (Gopp 1) A.

Definition GMminus {m n : nat} (A B : GenMatrix m n) : GenMatrix m n :=
  GMplus A (GMopp B).

Definition GMmult {m n o : nat} (A : GenMatrix m n) (B : GenMatrix n o) : GenMatrix m o := 
  fun x z => big_sum (fun y => A x y * B y z) n.


(* Only well-defined when o and p are non-zero *)
Definition Gkron {m n o p : nat} (A : GenMatrix m n) (B : GenMatrix o p) : 
  GenMatrix (m*o) (n*p) :=
  fun x y => Gmult (A (x / o)%nat (y / p)%nat) (B (x mod o) (y mod p)).

Definition direct_sum {m n o p : nat} (A : GenMatrix m n) (B : GenMatrix o p) :
  GenMatrix (m+o) (n+p) :=
  fun x y =>  if (x <? m) || (y <? n) then A x y else B (x - m)%nat (y - n)%nat.

Definition transpose {m n} (A : GenMatrix m n) : GenMatrix n m := 
  fun x y => A y x.

(* NB: no adjoint! 
Definition adjoint {m n} (A : GenMatrix m n) : GenMatrix n m := 
  fun x y => (A y x)^*.
*)


(* no adjoint! so these are defined in terms of transpose. good for R, but is this correct? *)
Definition inner_product {n} (u v : GenVector n) : F := 
  GMmult (transpose u) (v) 0 0.

Definition outer_product {n} (u v : GenVector n) : GenSquare n := 
  GMmult u (transpose v).

(** Kronecker of n copies of A *)
Fixpoint kron_n n {m1 m2} (A : GenMatrix m1 m2) : GenMatrix (m1^n) (m2^n) :=
  match n with
  | 0    => I 1
  | S n' => Gkron (kron_n n' A) A
  end.

(** Kronecker product of a list *)
Fixpoint big_kron {m n} (As : list (GenMatrix m n)) : 
  GenMatrix (m^(length As)) (n^(length As)) := 
  match As with
  | [] => I 1
  | A :: As' => Gkron A (big_kron As')
  end.

(** Product of n copies of A *)
Fixpoint GMmult_n n {m} (A : GenSquare m) : GenSquare m :=
  match n with
  | 0    => I m
  | S n' => GMmult A (GMmult_n n' A)
  end.

(** Direct sum of n copies of A *)
Fixpoint direct_sum_n n {m1 m2} (A : GenMatrix m1 m2) : GenMatrix (n*m1) (n*m2) :=
  match n with
  | 0    => @Zero 0 0
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
Notation Σ := (@big_sum F R0).  (* we intoduce Σ notation here *)
Notation "n ⨂ A" := (kron_n n A) (at level 30, no associativity) : genmatrix_scope.
Notation "⨂ A" := (big_kron A) (at level 60): genmatrix_scope.
Notation "n ⨉ A" := (GMmult_n n A) (at level 30, no associativity) : genmatrix_scope.
Notation "⟨ u , v ⟩" := (inner_product u v) (at level 0) : genmatrix_scope. 

#[export] Hint Unfold Zero I e_i trace dot GMplus GMopp scale GMmult Gkron genmat_equiv transpose : U_db.



(** * Showing that M is a vector space *)
#[global] Program Instance GM_is_monoid : forall n m, Monoid (GenMatrix n m) := 
  { Gzero := @Zero n m
  ; Gplus := GMplus
  }.
Solve All Obligations with program_simpl; prep_genmatrix_equality; autounfold with U_db; ring.


#[global] Program Instance GM_is_group : forall n m, Group (GenMatrix n m) :=
  { Gopp := GMopp }.
Solve All Obligations with program_simpl; prep_genmatrix_equality; autounfold with U_db; ring.


#[global] Program Instance GM_is_comm_group : forall n m, Comm_Group (GenMatrix n m).
Solve All Obligations with program_simpl; prep_genmatrix_equality; autounfold with U_db; ring.


#[global] Program Instance GM_is_module_space : forall n m, Module_Space (GenMatrix n m) F :=
  { Vscale := scale }.
Solve All Obligations with program_simpl; prep_genmatrix_equality; autounfold with U_db; ring.

#[global] Program Instance GM_is_vector_space : forall n m, Vector_Space (GenMatrix n m) F.



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
  repeat (destruct i as [|i]; simpl; [|apply <- Nat.succ_lt_mono in Hi]; try solve_end); clear Hi;
  repeat (destruct j as [|j]; simpl; [|apply <- Nat.succ_lt_mono in Hj]; try solve_end); clear Hj.

Ltac lgma' :=
  apply genmat_equiv_eq;
  repeat match goal with
  | [ |- WF_GenMatrix (?A) ]  => auto with wf_db (* (try show_wf) *)
  | [ |- genmat_equiv (?A) (?B) ] => by_cell; try ring (* try lca  *)
  end.

(* lemmas which are useful for simplifying proofs involving matrix operations *)
Lemma kron_simplify : forall (n m o p : nat) (a b : GenMatrix n m) (c d : GenMatrix o p), 
    a = b -> c = d -> (a ⊗ c)%GM = (b ⊗ d)%GM.
Proof. intros; subst; easy. 
Qed.

Lemma n_kron_simplify : forall (n m : nat) (a b : GenMatrix n m) (n m : nat), 
    a = b -> n = m -> n ⨂ a = m ⨂ b.
Proof. intros; subst; easy. 
Qed.

Lemma Mtranspose_simplify : forall (n m : nat) (a b : GenMatrix n m), 
    a = b -> a⊤ = b⊤.
Proof. intros; subst; easy. 
Qed.

(*
Lemma Madjoint_simplify : forall (n m : nat) (a b : GenMatrix n m), 
    a = b -> a† = b†.
Proof. intros; subst; easy. 
Qed.
*)

Lemma Mmult_simplify : forall (n m o : nat) (a b : GenMatrix n m) (c d : GenMatrix m o), 
    a = b -> c = d -> a × c = b × d.
Proof. intros; subst; easy. 
Qed.

Lemma Mmult_n_simplify : forall (n : nat) (a b : GenSquare n) (c d : nat), 
    a = b -> c = d -> c ⨉ a = d ⨉ b.
Proof. intros; subst; easy. 
Qed.

Lemma dot_simplify : forall (n : nat) (a b c d: GenVector n), 
    a = b -> c = d -> a ∘ c = b ∘ c.
Proof. intros; subst; easy. 
Qed.

Lemma Mplus_simplify : forall (n m: nat) (a b : GenMatrix n m) (c d : GenMatrix n m), 
    a = b -> c = d -> a .+ c = b .+ d.
Proof. intros; subst; easy. 
Qed.

Lemma Mscale_simplify : forall (n m: nat) (a b : GenMatrix n m) (c d : F), 
    a = b -> c = d -> c .* a = d .* b.
Proof. intros; subst; easy. 
Qed.



(** * Proofs about well-formedness **)



Lemma WF_GenMatrix_dim_change : forall (m n m' n' : nat) (A : GenMatrix m n),
  m = m' ->
  n = n' ->
  @WF_GenMatrix m n A ->
  @WF_GenMatrix m' n' A.
Proof. intros. subst. easy. Qed.

Lemma WF_make_WF : forall {m n} (A : GenMatrix m n), WF_GenMatrix (make_WF A).
Proof. intros. 
       unfold WF_GenMatrix, make_WF; intros. 
       destruct H as [H | H].
       bdestruct (x <? m); try lia; easy. 
       bdestruct (y <? n); bdestruct (x <? m); try lia; easy.
Qed.

Lemma WF_Zero : forall m n : nat, WF_GenMatrix (@Zero m n).
Proof. intros m n. unfold WF_GenMatrix. reflexivity. Qed.

Lemma WF_I : forall n : nat, WF_GenMatrix (I n). 
Proof. 
  unfold WF_GenMatrix, I. intros n x y H. simpl.
  destruct H; bdestruct (x =? y); bdestruct (x <? n); trivial; lia.
Qed.

Lemma WF_I1 : WF_GenMatrix (I 1). Proof. apply WF_I. Qed.

Lemma WF_e_i : forall {n : nat} (i : nat),
  WF_GenMatrix (@e_i n i).
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
  + rewrite H; [ring | auto].
  + rewrite H0; [ring | auto].
Qed.

Lemma WF_kron : forall {m n o p q r : nat} (A : GenMatrix m n) (B : GenMatrix o p), 
                  (q = m * o)%nat -> (r = n * p)%nat -> 
                  WF_GenMatrix A -> WF_GenMatrix B -> @WF_GenMatrix q r (A ⊗ B).
Proof.
  unfold WF_GenMatrix, Gkron.
  intros m n o p q r A B Nn No H H0 x y H1. subst.
  bdestruct (o =? 0). rewrite H0; [ring|lia]. 
  bdestruct (p =? 0). rewrite H0; [ring|lia]. 
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
                  (q = m + o)%nat -> (r = n + p)%nat -> 
                  WF_GenMatrix A -> WF_GenMatrix B -> @WF_GenMatrix q r (A .⊕ B).
Proof. 
  unfold WF_GenMatrix, direct_sum. 
  intros; subst.
  destruct H3; bdestruct_all; simpl; try apply H1; try apply H2. 
  all : lia.
Qed.

Lemma WF_transpose : forall {m n : nat} (A : GenMatrix m n), 
                     WF_GenMatrix A -> WF_GenMatrix A⊤. 
Proof. unfold WF_GenMatrix, transpose. intros m n A H x y H0. apply H. 
       destruct H0; auto. Qed.

(* Lemma WF_adjoint : forall {m n : nat} (A : GenMatrix m n), 
      WF_GenMatrix A -> WF_GenMatrix A†. 
Proof. unfold WF_GenMatrix, adjoint, Cconj. intros m n A H x y H0. simpl. 
rewrite H. lca. lia. Qed. *)

Lemma WF_outer_product : forall {n} (u v : GenVector n),
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

Lemma WF_GMmult_n : forall n {m} (A : GenSquare m),
   WF_GenMatrix A -> WF_GenMatrix (GMmult_n n A).
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

Local Close Scope nat_scope.


(** * Tactics for showing well-formedness *)


Local Open Scope nat.
Local Open Scope G.

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

(* Create HintDb wf_db. *)
#[export] Hint Resolve WF_Zero WF_I WF_I1 WF_e_i WF_mult WF_plus WF_scale WF_transpose
     (* WF_adjoint *) WF_outer_product WF_big_kron WF_kron_n WF_kron 
     WF_GMmult_n WF_make_WF WF_Msum : wf_db.
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

Lemma Mplus_make_WF : forall {n m} (A B : GenMatrix m n),
  make_WF A .+ make_WF B = make_WF (A .+ B).
Proof. intros. 
       apply genmat_equiv_eq; auto with wf_db.
       unfold genmat_equiv; intros. 
       unfold make_WF, GMplus.
       bdestruct (i <? m); bdestruct (j <? n); try lia; simpl. 
       easy.
Qed.
  
Lemma Mmult_make_WF : forall {m n o} (A : GenMatrix m n) (B : GenMatrix n o),
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

Lemma trace_plus_dist : forall (n : nat) (A B : GenSquare n), 
    trace (A .+ B) = (trace A + trace B).
Proof. 
  intros.
  unfold trace, GMplus.
  rewrite (@big_sum_plus F R0 R1 R2). 
  easy.  
Qed.

Lemma trace_mult_dist : forall n p (A : GenSquare n), trace (p .* A) = (p * trace A).
Proof.
  intros.
  unfold trace, scale.
  rewrite (@big_sum_mult_l F R0 R1 R2 R3). 
  easy.
Qed.

Lemma GMplus_0_l : forall (m n : nat) (A : GenMatrix m n), Zero .+ A = A.
Proof. intros. lgma. Qed.

Lemma GMplus_0_r : forall (m n : nat) (A : GenMatrix m n), A .+ Zero = A.
Proof. intros. lgma. Qed.
    
Lemma GMmult_0_l : forall (m n o : nat) (A : GenMatrix n o), @Zero m n × A = Zero.
Proof.
  intros m n o A. 
  unfold GMmult, Zero.
  prep_genmatrix_equality.
  apply (@big_sum_0 F R0).
  intros.
  ring.
Qed.

Lemma GMmult_0_r : forall (m n o : nat) (A : GenMatrix m n), A × @Zero n o = Zero.
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
      simpl. dumb_lRa.
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
    simpl. dumb_lRa.
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
  bdestruct (z =? y); bdestruct (z <? n); simpl; try ring; try lia. 
Qed.

Lemma kron_0_l : forall (m n o p : nat) (A : GenMatrix o p), 
  @Zero m n ⊗ A = Zero.
Proof.
  intros m n o p A.
  prep_genmatrix_equality.
  unfold Zero, Gkron.
  rewrite Gmult_0_l.
  reflexivity.
Qed.

Lemma kron_0_r : forall (m n o p : nat) (A : GenMatrix m n), 
   A ⊗ @Zero o p = Zero.
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
  unfold Gkron.
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

(* Theorem adjoint_involutive : forall (m n : nat) (A : GenMatrix m n), A†† = A.
Proof. intros. lma. Qed.   *)

Lemma id_transpose_eq : forall n, (I n)⊤ = (I n).
Proof.
  intros n. unfold transpose, I.
  prep_genmatrix_equality.
  bdestruct (y =? x); bdestruct (x =? y); bdestruct (y <? n); bdestruct (x <? n);
    trivial; lia.
Qed.

Lemma zero_transpose_eq : forall m n, (@Zero m n)⊤ = @Zero n m.
Proof. reflexivity. Qed.

(* Lemma id_adjoint_eq : forall n, (I n)† = (I n).
Proof.
  intros n.
  unfold adjoint, I.
  prep_genmatrix_equality.
  bdestruct (y =? x); bdestruct (x =? y); bdestruct (y <? n); bdestruct (x <? n);
    try lia; lca.
Qed.

Lemma zero_adjoint_eq : forall m n, (@Zero m n)† = @Zero n m.
Proof. unfold adjoint, Zero. rewrite Cconj_0. reflexivity. Qed. *)

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
  induction n.
  + simpl.
    clear B.
    induction o. reflexivity.
    simpl. rewrite IHo. ring.
  + simpl. 
    rewrite <- IHn.
    simpl.
    rewrite (@big_sum_mult_l F R0 R1 R2 R3).
    rewrite <- (@big_sum_plus F R0 R1 R2).
    apply big_sum_eq.
    apply functional_extensionality. intros z.
    rewrite Gmult_plus_distr_r.
    rewrite Gmult_assoc.
    reflexivity.
Qed.

Lemma GMmult_plus_distr_l : forall (m n o : nat) (A : GenMatrix m n) (B C : GenMatrix n o), 
                           A × (B .+ C) = A × B .+ A × C.
Proof. 
  intros m n o A B C.
  unfold GMplus, GMmult.
  prep_genmatrix_equality.
  rewrite <- (@big_sum_plus F R0 R1 R2).
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
  rewrite <- (@big_sum_plus F R0 R1 R2).
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

Lemma Mscale_0_r : forall (m n : nat) (c : F), c .* @Zero m n = Zero.
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

Lemma Mscale_div : forall {n m} (c : F) (A B : GenMatrix n m),
  c <> 0 -> c .* A = c .* B -> A = B.
Proof. intros. 
       rewrite <- Mscale_1_l. rewrite <- (Mscale_1_l n m A).
       rewrite <- (Ginv_l c).
       rewrite <- Mscale_assoc.
       rewrite H0. 
       lgma.
       apply H.
Qed.

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
  rewrite (@big_sum_mult_l F R0 R1 R2 R3). 
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
  rewrite (@big_sum_mult_l F R0 R1 R2 R3). 
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

(* Lemma Mscale_adj : forall (m n : nat) (x : F) (A : GenMatrix m n),
    (x .* A)† = x^* .* A†.
Proof.
  intros m n x A.
  unfold scale, adjoint.
  prep_genmatrix_equality.
  rewrite Cconj_mult_distr.          
  reflexivity.
Qed. *)

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

(* Lemma GMplus_adjoint : forall (m n : nat) (A : GenMatrix m n) (B : GenMatrix m n),
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
Qed. *)

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
  + rewrite (@big_sum_product F R0 R1 R2 R3).
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
  (@GMmult mp nq or (@Gkron m n p q A B) (@Gkron n' o q' r C D)) =
  (@Gkron m o p r (@GMmult m n o A C) (@GMmult p q r B D)).
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
  (forall i, WF_GenMatrix (nth i l1 (@Zero n m))) ->
  (forall i, WF_GenMatrix (nth i l2 (@Zero n m))) ->
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

(* Lemma kron_n_adjoint : forall n {m1 m2} (A : GenMatrix m1 m2),
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

Lemma GMmult_n_kron_distr_l : forall {m n} i (A : GenSquare m) (B : GenSquare n),
  i ⨉ (A ⊗ B) = (i ⨉ A) ⊗ (i ⨉ B).
Proof.
  intros m n i A B.
  induction i; simpl.
  rewrite id_kron; reflexivity.
  rewrite IHi.
  rewrite kron_mixed_product.
  reflexivity.
Qed.

Lemma GMmult_n_1_l : forall {n} (A : GenSquare n),
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


Lemma GMmult_n_add : forall {n} (A : GenSquare n) (a b : nat),
  WF_GenMatrix A ->
  ((a + b) ⨉ A) = (a ⨉ A) × (b ⨉ A).
Proof. intros. 
       induction a; simpl.
       - rewrite GMmult_1_l; auto with wf_db.
       - rewrite IHa, GMmult_assoc; easy.
Qed.

Lemma GMmult_n_mult_r : forall {n} (A : GenSquare n) (a b : nat),
  WF_GenMatrix A ->
  b ⨉ (a ⨉ A) = ((a*b) ⨉ A).
Proof. intros. 
       induction b; simpl.
       - replace (a * 0) with 0 by lia; easy. 
       - replace (a * S b) with (a + a * b) by lia.
         rewrite GMmult_n_add, <- IHb; auto.
Qed.

Lemma GMmult_n_eigenvector : forall {n} (A : GenSquare n) (ψ : GenVector n) λ i,
  WF_GenMatrix ψ -> A × ψ = λ .* ψ ->
  i ⨉ A × ψ = (G_big_mult (repeat λ i))%G .* ψ.
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
  rewrite Gmult_comm.
  reflexivity.
Qed.



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

Lemma Mmult_Msum_distr_l : forall {d1 d2 m} n (f : nat -> GenMatrix d1 d2) (A : GenMatrix m d1),
  A × big_sum f n = big_sum (fun i => A × f i) n.
Proof.
  intros.
  induction n; simpl. 
  rewrite GMmult_0_r. reflexivity.
  rewrite GMmult_plus_distr_l, IHn. reflexivity.
Qed.

Lemma Mmult_Msum_distr_r : forall {d1 d2 m} n (f : nat -> GenMatrix d1 d2) (A : GenMatrix d2 m),
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

Lemma Msum_constant : forall {d1 d2} n (A : GenMatrix d1 d2),  big_sum (fun _ => A) n = (times_n 1%G n) .* A.
Proof.
  intros. 
  induction n.
  simpl. lgma.
  simpl big_sum.
  rewrite IHn.
  simpl. 
  rewrite Mscale_plus_distr_l.
  lgma.
Qed.

(* Lemma Msum_adjoint : forall {d1 d2} n (f : nat -> GenMatrix d1 d2),
  (big_sum f n)† = big_sum (fun i => (f i)†) n.
Proof.
  intros.
  induction n; simpl.
  lgma.
  rewrite GMplus_adjoint, IHn.  
  reflexivity.
Qed. *)

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
  clear.
  intros.
  induction n; simpl.
  lgma.
  rewrite IHn. lgma.
Qed.



(** * Tactics **)

Local Close Scope nat_scope.

(* Note on "using [tactics]": Most generated subgoals will be of the form
   WF_GenMatrix M, where auto with wf_db will work.
   Occasionally WF_GenMatrix M will rely on rewriting to match an assumption in the
   context, here we recursively autorewrite (which adds time).
   kron_1_l requires proofs of (n > 0)%nat, here we use lia. *)

(* *)

(* Convert a list to a vector *)
Fixpoint vec_to_list' {nmax : nat} (n : nat) (v : GenVector nmax) :=
  match n with
  | O    => nil
  | S n' => v (nmax - n)%nat O :: vec_to_list' n' v
  end.
Definition vec_to_list {n : nat} (v : GenVector n) := vec_to_list' n v.

Lemma vec_to_list'_length : forall m n (v : GenVector n), length (vec_to_list' m v) = m.
Proof.
  intros.
  induction m; auto.
  simpl. rewrite IHm.
  reflexivity.
Qed.

Lemma vec_to_list_length : forall n (v : GenVector n), length (vec_to_list v) = n.
Proof. intros. apply vec_to_list'_length. Qed.

Lemma nth_vec_to_list' : forall {m n} (v : GenVector n) x,
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

Lemma nth_vec_to_list : forall n (v : GenVector n) x,
  (x < n)%nat -> nth x (vec_to_list v) 0 = v x O.
Proof.
  intros.
  unfold vec_to_list.
  rewrite nth_vec_to_list' by lia.
  replace (n - n + x)%nat with x by lia.
  reflexivity.
Qed.


(** Restoring GenMatrix Dimensions *)


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
                        | GenMatrix ?m' ?n' => constr:(@GMmult m' n' n' A' (I n'))
                        end
  | I _ × ?B          => let B' := restore_dims_rec B in 
                        match type of B' with 
                        | GenMatrix ?n' ?o' => constr:(@GMmult n' n' o' (I n')  B')
                        end
  | ?A × @Zero ?n ?n  => let A' := restore_dims_rec A in 
                        match type of A' with 
                        | GenMatrix ?m' ?n' => constr:(@GMmult m' n' n' A' (@Zero n' n'))
                        end
  | @Zero ?n ?n × ?B  => let B' := restore_dims_rec B in 
                        match type of B' with 
                        | GenMatrix ?n' ?o' => constr:(@GMmult n' n' o' (@Zero n' n') B')
                        end
  | ?A × @Zero ?n ?o  => let A' := restore_dims_rec A in 
                        match type of A' with 
                        | GenMatrix ?m' ?n' => constr:(@GMmult m' n' o A' (@Zero n' o))
                        end
  | @Zero ?m ?n × ?B  => let B' := restore_dims_rec B in 
                        match type of B' with 
                        | GenMatrix ?n' ?o' => constr:(@GMmult n' n' o' (@Zero m n') B')
                        end
  | ?A .+ @Zero ?m ?n => let A' := restore_dims_rec A in 
                        match type of A' with 
                        | GenMatrix ?m' ?n' => constr:(@GMplus m' n' A' (@Zero m' n'))
                        end
  | @Zero ?m ?n .+ ?B => let B' := restore_dims_rec B in 
                        match type of B' with 
                        | GenMatrix ?m' ?n' => constr:(@GMplus m' n' (@Zero m' n') B')
                        end
(* general cases *)
  | ?A = ?B  => let A' := restore_dims_rec A in 
                let B' := restore_dims_rec B in 
                match type of A' with 
                | GenMatrix ?m' ?n' => constr:(@eq (GenMatrix m' n') A' B')
                  end
  | ?A × ?B   => let A' := restore_dims_rec A in 
                let B' := restore_dims_rec B in 
                match type of A' with 
                | GenMatrix ?m' ?n' =>
                  match type of B' with 
                  | GenMatrix ?n'' ?o' => constr:(@GMmult m' n' o' A' B')
                  end
                end 
  | ?A ⊗ ?B   => let A' := restore_dims_rec A in 
                let B' := restore_dims_rec B in 
                match type of A' with 
                | GenMatrix ?m' ?n' =>
                  match type of B' with 
                  | GenMatrix ?o' ?p' => constr:(@Gkron m' n' o' p' A' B')
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
                 | GenMatrix ?m'' ?n'' => constr:(@GMplus m' n' A' B')
                 end
               end
  | ?c .* ?A => let A' := restore_dims_rec A in 
               match type of A' with
               | GenMatrix ?m' ?n' => constr:(@scale m' n' c A')
               end
  | ?n ⨂ ?A => let A' := restore_dims_rec A in
               match type of A' with
               | GenMatrix ?m' ?n' => constr:(@kron_n n m' n' A')
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
#[global] Hint Rewrite kron_1_l kron_1_r GMmult_1_l GMmult_1_r id_kron id_adjoint_eq
     @GMmult_adjoint GMplus_adjoint @kron_adjoint @kron_mixed_product
     id_adjoint_eq adjoint_involutive using 
     (auto 100 with wf_db; autorewrite with M_db; auto 100 with wf_db; lia) : M_db.
*)

(* eauto will cause major choking... *)
#[global] Hint Rewrite  @kron_1_l @kron_1_r @GMmult_1_l @GMmult_1_r @Mscale_1_l 
     (* @id_adjoint_eq *) @id_transpose_eq using (auto 100 with wf_db) : M_db_light.
#[global] Hint Rewrite @kron_0_l @kron_0_r @GMmult_0_l @GMmult_0_r @GMplus_0_l @GMplus_0_r
     @Mscale_0_l @Mscale_0_r (* @zero_adjoint_eq *) @zero_transpose_eq using (auto 100 with wf_db) : M_db_light.

(* I don't like always doing restore_dims first, but otherwise sometimes leaves 
   unsolvable WF_GenMatrix goals. *)
Ltac Msimpl_light := try restore_dims; autorewrite with M_db_light.

#[global] Hint Rewrite (* @GMmult_adjoint @GMplus_adjoint @kron_adjoint *) @kron_mixed_product
     (* @adjoint_involutive *) using (auto 100 with wf_db) : M_db.

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

(* Ltac distribute_adjoint :=
  repeat match goal with
  | |- context [(?c .* ?A)†] => rewrite (Mscale_adj _ _ c A)
  | |- context [(?A .+ ?B)†] => rewrite (GMplus_adjoint _ _ A B)
  | |- context [(?A × ?B)†] => rewrite (GMmult_adjoint A B)
  | |- context [(?A ⊗ ?B)†] => rewrite (kron_adjoint A B)
  end. *)


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


End LinAlgOverField.




(* Use case. *)
(* Require Import Complex.

Declare Module CField : FieldModule
  with Definition F := C
  with Definition R0 := C_is_monoid
  with Definition R1 := C_is_group
  with Definition R2 := C_is_comm_group
  with Definition R3 := C_is_ring
  with Definition R4 := C_is_comm_ring
  with Definition R5 := C_is_field.

Module CMatrixMod := LinAlgOverField CField.

Notation CMatrix := CMatrixMod.GenMatrix.

Import CMatrixMod.

Check eq_refl : CMatrixMod.F = C.

Print GenMatrix.

Require Import Matrix.

Check eq_refl : CMatrix = Matrix. *)

