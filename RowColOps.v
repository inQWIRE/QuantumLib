Require Import Psatz.   
Require Import Reals. 
  
Require Export Matrix.




(** Here, we define many different types of row and column operations *)




Local Open Scope nat_scope.

                    
(** * Defining matrix altering/col operations *)

(* in what follows, T is a set of vectors, A is a square, v/as' are vectors/sets of scalars *)

Definition get_col {m n} (T : Matrix m n) (i : nat) : Vector m :=
  fun x y => (if (y =? O) then T x i else C0).   

#[deprecated(note="Use get_col instead")]
Notation get_vec i S := (get_col S i) (only parsing).

Definition get_row {m n} (T : Matrix m n) (i : nat) : Matrix 1 n :=
  fun x y => (if (x =? O) then T i y else C0).  

Definition reduce_row {m n} (T : Matrix (S m) n) (row : nat) : Matrix m n :=
  fun x y => if x <? row
             then T x y
             else T (1 + x) y.

Definition reduce_col {m n} (T : Matrix m (S n)) (col : nat) : Matrix m n :=
  fun x y => if y <? col
             then T x y
             else T x (1 + y).

(* more specific form for vectors *)
Definition reduce_vecn {n} (v : Vector (S n)) : Vector n :=
  fun x y => if x <? n
             then v x y
             else v (1 + x) y.

(* More specific form for squares *)
Definition get_minor {m n} (A : Matrix (S m) (S n)) (row col : nat) : Matrix m n :=
  fun x y => (if x <? row 
              then (if y <? col 
                    then A x y
                    else A x (1+y))
              else (if y <? col 
                    then A (1+x) y
                    else A (1+x) (1+y))).

#[deprecated(note="Use get_minor instead")]
Notation reduce := get_minor (only parsing).


(* more general than col_append *)
Definition smash {m n1 n2} (T1 : Matrix m n1) (T2 : Matrix m n2) : Matrix m (n1 + n2) :=
  fun i j => if j <? n1 then T1 i j else T2 i (j - n1).

(* TODO: combine smash and col_wedge *)
Definition col_wedge {m n} (T : Matrix m n) (v : Vector m) (spot : nat) : Matrix m (S n) :=
  fun i j => if j <? spot 
             then T i j
             else if j =? spot
                  then v i 0
                  else T i (j-1).

Definition row_wedge {m n} (T : Matrix m n) (v : Matrix 1 n) (spot : nat) : Matrix (S m) n :=
  fun i j => if i <? spot 
             then T i j
             else if i =? spot
                  then v 0 j
                  else T (i-1) j.

(*
#[deprecated(note="Use col_wedge instead")]
*)
Definition col_append {m n} (T : Matrix m n) (v : Vector m) : Matrix m (S n) :=
  col_wedge T v n.


(*
#[deprecated(note="Use row_wedge instead")]
*)
Definition row_append {m n} (T : Matrix m n) (v : Matrix 1 n) : Matrix (S m) n :=
  row_wedge T v m. 



Definition col_swap {m n} (T : Matrix m n) (x y : nat) : Matrix m n := 
  fun i j => if (j =? x) 
             then T i y
             else if (j =? y) 
                  then T i x
                  else T i j.

Definition row_swap {m n} (T : Matrix m n) (x y : nat) : Matrix m n := 
  fun i j => if (i =? x) 
             then T y j
             else if (i =? y) 
                  then T x j
                  else T i j.

Definition col_scale {m n} (T : Matrix m n) (col : nat) (a : C) : Matrix m n := 
  fun i j => if (j =? col) 
             then (a * T i j)%C
             else T i j.

Definition row_scale {m n} (T : Matrix m n) (row : nat) (a : C) : Matrix m n := 
  fun i j => if (i =? row) 
             then (a * T i j)%C
             else T i j.

(* generalizations of col_scale and row_scale. Both sets of as' are vectors where the col/row 
   corresponds to the scaled col/row. Can also show that this is the same as multiplying 
   by the identity with scalars on diag *)
Definition col_scale_many {m n} (T : Matrix m n) (as' : Matrix 1 n) : Matrix m n := 
  fun i j => ((as' O j) * (T i j))%C. 

Definition row_scale_many {m n} (T : Matrix m n) (as' : Vector m) : Matrix m n := 
  fun i j => ((as' i O) * (T i j))%C.

(* adding one column to another *)
Definition col_add {m n} (T : Matrix m n) (col to_add : nat) (a : C) : Matrix m n := 
  fun i j => if (j =? col) 
             then (T i j + a * T i to_add)%C
             else T i j.

(* adding one row to another *)
Definition row_add {m n} (T : Matrix m n) (row to_add : nat) (a : C) : Matrix m n := 
  fun i j => if (i =? row) 
             then (T i j + a * T to_add j)%C
             else T i j.

(* generalizing col_add *)
Definition gen_new_col (m n : nat) (T : Matrix m n) (as' : Vector n) : Vector m :=
  big_sum (fun i => (as' i O) .* (get_col T i)) n.

Definition gen_new_row (m n : nat) (T : Matrix m n) (as' : Matrix 1 m) : Matrix 1 n :=
  big_sum (fun i => (as' O i) .* (get_row T i)) m.

(* adds all columns to single column *)
Definition col_add_many {m n} (T : Matrix m n) (as' : Vector n) (col : nat) : Matrix m n :=
  fun i j => if (j =? col) 
             then (T i j + (gen_new_col m n T as') i O)%C
             else T i j.

Definition row_add_many {m n} (T : Matrix m n) (as' : Matrix 1 m) (row : nat) : Matrix m n :=
  fun i j => if (i =? row) 
             then (T i j + (gen_new_row m n T as') O j)%C
             else T i j.

(* adds single column to each other column *)
Definition col_add_each {m n} (T : Matrix m n) (as' : Matrix 1 n) (col : nat) : Matrix m n := 
  T .+ ((get_col T col) × as').

Definition row_add_each {m n} (T : Matrix m n) (as' : Vector m) (row : nat) : Matrix m n := 
  T .+ (as' × get_row T row).

Definition make_col_val {m n} (T : Matrix m n) (col : nat) (a : C) : Matrix m n :=
  fun i j => if (j =? col) && (i <? m)
             then a
             else T i j.

Definition make_row_val {m n} (T : Matrix m n) (row : nat) (a : C) : Matrix m n :=
  fun i j => if (i =? row) && (j <? n)
             then a
             else T i j.

Definition col_to_front {m n} (T : Matrix m n) (col : nat) : Matrix m n := 
  fun i j => if (j =? O) 
          then T i col
          else if (j <? col + 1) then T i (j - 1) else T i j.

Definition row_to_front {m n} (T : Matrix m n) (row : nat) : Matrix m n := 
  fun i j => if (i =? O) 
          then T row j
          else if (i <? row + 1) then T (i - 1) j else T i j.

Definition col_replace {m n} (T : Matrix m n) (col rep : nat) : Matrix m n := 
  fun i j => if (j =? rep) 
          then T i col
          else T i j.

Definition row_replace {m n} (T : Matrix m n) (row rep : nat) : Matrix m n := 
  fun i j => if (i =? rep) 
          then T row j
          else T i j.


(* using previous def's, takes matrix and increases its rank by 1 (assuming c <> 0) *)
Definition pad1 {m n : nat} (A : Matrix m n) (c : C) : Matrix (S m) (S n) :=
  col_wedge (row_wedge A Zero 0) (c .* e_i 0) 0.






(** * WF lemmas about these new operations *)

Lemma WF_get_col : forall {m n} (i : nat) (T : Matrix m n),
  WF_Matrix T -> WF_Matrix (get_col T i). 
Proof. unfold WF_Matrix, get_col in *.
       intros.
       bdestruct (y =? 0); try lia; try easy.
       apply H.
       destruct H0. 
       left; easy.
       lia. 
Qed.

Lemma WF_get_row : forall {m n} (i : nat) (T : Matrix m n),
  WF_Matrix T -> WF_Matrix (get_row T i). 
Proof. unfold WF_Matrix, get_row in *.
       intros.
       bdestruct (x =? 0); try lia; try easy.
       apply H.
       destruct H0. 
       lia. 
       right; easy.
Qed.

Lemma WF_reduce_row : forall {m n} (row : nat) (T : Matrix (S m) n),
  row < (S m) -> WF_Matrix T -> WF_Matrix (reduce_row T row).
Proof. unfold WF_Matrix, reduce_row. intros. 
       bdestruct (x <? row). 
       - destruct H1 as [H1 | H1].
         + assert (nibzo : forall (a b c : nat), a < b -> b < c -> 1 + a < c).
           { lia. }
           apply (nibzo x row (S m)) in H2.
           simpl in H2. lia. apply H.
         + apply H0; auto.
       - apply H0. destruct H1. 
         + left. simpl. lia.
         + right. apply H1. 
Qed.

Lemma WF_reduce_col : forall {m n} (col : nat) (T : Matrix m (S n)),
  col < (S n) -> WF_Matrix T -> WF_Matrix (reduce_col T col).
Proof. unfold WF_Matrix, reduce_col. intros. 
       bdestruct (y <? col). 
       - destruct H1 as [H1 | H1].   
         + apply H0; auto. 
         + assert (nibzo : forall (a b c : nat), a < b -> b < c -> 1 + a < c).
           { lia. }
           apply (nibzo y col (S n)) in H2.
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

Lemma get_minor_is_redrow_redcol : forall {m n} (A : Matrix (S m) (S n)) (row col : nat),
  get_minor A row col = reduce_col (reduce_row A row) col.
Proof. intros. 
       prep_matrix_equality.
       unfold get_minor, reduce_col, reduce_row.
       bdestruct (x <? row); bdestruct (y <? col); try easy.
Qed. 

Lemma get_minor_is_redcol_redrow : forall {m n} (A : Matrix (S m) (S n)) (row col : nat),
  get_minor A row col = reduce_row (reduce_col A col) row.
Proof. intros. 
       prep_matrix_equality.
       unfold get_minor, reduce_col, reduce_row.
       bdestruct (x <? row); bdestruct (y <? col); try easy.
Qed. 

Lemma WF_get_minor : forall {m n} (A : Matrix (S m) (S n)) (row col : nat),
  row < S m -> col < S n -> WF_Matrix A -> WF_Matrix (get_minor A row col).
Proof. intros.
       rewrite get_minor_is_redrow_redcol.
       apply WF_reduce_col; try easy.
       apply WF_reduce_row; try easy.
Qed.

Lemma WF_col_swap : forall {m n} (T : Matrix m n) (x y : nat),
  x < n -> y < n -> WF_Matrix T -> WF_Matrix (col_swap T x y).
Proof. unfold WF_Matrix, col_swap in *.
       intros. 
       bdestruct (y0 =? x); bdestruct (y0 =? y); destruct H2; try lia. 
       all : apply H1; try (left; apply H2).
       auto.
Qed.

Lemma WF_row_swap : forall {m n} (T : Matrix m n) (x y : nat),
  x < m -> y < m -> WF_Matrix T -> WF_Matrix (row_swap T x y).
Proof. unfold WF_Matrix, row_swap in *.
       intros. 
       bdestruct (x0 =? x); bdestruct (x0 =? y); destruct H2; try lia. 
       all : apply H1; try (right; apply H2).
       auto.
Qed.

Lemma WF_col_scale : forall {m n} (T : Matrix m n) (x : nat) (a : C),
  WF_Matrix T -> WF_Matrix (col_scale T x a).
Proof. unfold WF_Matrix, col_scale in *.
       intros. 
       apply H in H0.
       rewrite H0.
       rewrite Cmult_0_r.
       bdestruct (y =? x); easy.
Qed.

Lemma WF_row_scale : forall {m n} (T : Matrix m n) (x : nat) (a : C),
  WF_Matrix T -> WF_Matrix (row_scale T x a).
Proof. unfold WF_Matrix, row_scale in *.
       intros. 
       apply H in H0.
       rewrite H0.
       rewrite Cmult_0_r.
       bdestruct (x0 =? x); easy.
Qed.

Lemma WF_col_scale_many : forall {m n} (T : Matrix m n) (as' : Matrix m 1),
  WF_Matrix T -> WF_Matrix (col_scale_many T as').
Proof. unfold WF_Matrix, col_scale_many in *.
       intros. 
       apply H in H0.
       rewrite H0.
       rewrite Cmult_0_r; easy. 
Qed.

Lemma WF_row_scale_many : forall {m n} (T : Matrix m n) (as' : Vector n),
  WF_Matrix T -> WF_Matrix (row_scale_many T as').
Proof. unfold WF_Matrix, row_scale_many in *.
       intros. 
       apply H in H0.
       rewrite H0.
       rewrite Cmult_0_r; easy. 
Qed.

Lemma WF_col_add : forall {m n} (T : Matrix m n) (x y : nat) (a : C),
  x < n -> WF_Matrix T -> WF_Matrix (col_add T x y a).
Proof. unfold WF_Matrix, col_add in *.
       intros.
       bdestruct (y0 =? x); destruct H1; try lia. 
       do 2 (rewrite H0; auto). ring. 
       all : apply H0; auto.
Qed.

Lemma WF_row_add : forall {m n} (T : Matrix m n) (x y : nat) (a : C),
  x < m -> WF_Matrix T -> WF_Matrix (row_add T x y a).
Proof. unfold WF_Matrix, row_add in *.
       intros.
       bdestruct (x0 =? x); destruct H1; try lia. 
       do 2 (rewrite H0; auto). ring. 
       all : apply H0; auto.
Qed.

Lemma WF_gen_new_col : forall {m n} (T : Matrix m n) (as' : Vector n),
  WF_Matrix T -> WF_Matrix (gen_new_col m n T as').
Proof. intros.
       unfold gen_new_col. 
       apply WF_Msum; intros. 
       apply WF_scale. 
       apply WF_get_col.
       easy.
Qed.

Lemma WF_gen_new_row : forall {m n} (T : Matrix m n) (as' : Matrix 1 m),
  WF_Matrix T -> WF_Matrix (gen_new_row m n T as').
Proof. intros.
       unfold gen_new_row.
       apply WF_Msum; intros. 
       apply WF_scale. 
       apply WF_get_row.
       easy.
Qed.

Lemma WF_col_add_many : forall {m n} (T : Matrix m n) (as' : Vector n) (col : nat),
  col < n -> WF_Matrix T -> WF_Matrix (col_add_many T as' col).
Proof. unfold WF_Matrix, col_add_many.
       intros. 
       bdestruct (y =? col).
       assert (H4 := (WF_gen_new_col T as')).
       rewrite H4, H0; try easy.
       ring. destruct H2; lia. 
       rewrite H0; easy.
Qed.

Lemma WF_row_add_many : forall {m n} (T : Matrix m n) (as' : Matrix 1 m) (row : nat),
  row < m -> WF_Matrix T -> WF_Matrix (row_add_many T as' row).
Proof. unfold WF_Matrix, row_add_many.
       intros. 
       bdestruct (x =? row).
       assert (H4 := (WF_gen_new_row T as')).
       rewrite H4, H0; try easy.
       ring. destruct H2; lia. 
       rewrite H0; easy.
Qed.

Lemma WF_col_wedge : forall {m n} (T : Matrix m n) (v : Vector m) (spot : nat),
  spot <= n -> WF_Matrix T -> WF_Matrix v -> WF_Matrix (col_wedge T v spot).
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

Lemma WF_row_wedge : forall {m n} (T : Matrix m n) (v : Matrix 1 n) (spot : nat),
  spot <= m -> WF_Matrix T -> WF_Matrix v -> WF_Matrix (row_wedge T v spot).
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

#[deprecated(note="Use WF_col_wedge instead")]
Notation WF_col_append := WF_col_wedge (only parsing).


#[deprecated(note="Use WF_row_wedge instead")]
Notation WF_row_append := WF_row_wedge (only parsing).


Lemma WF_smash : forall {m n1 n2} (T1 : Matrix m n1) (T2 : Matrix m n2),
  WF_Matrix T1 -> WF_Matrix T2 -> WF_Matrix (smash T1 T2).
Proof. unfold WF_Matrix, smash in *.
       intros. 
       bdestruct (y <? n1).
       - apply H; lia. 
       - apply H0; lia.
Qed.

Lemma WF_col_add_each : forall {m n} (col : nat) (as' : Matrix 1 n) (T : Matrix m n),
  WF_Matrix T -> WF_Matrix as' -> WF_Matrix (col_add_each T as' col).
Proof. intros.
       unfold col_add_each.
       apply WF_plus; try easy;
       apply WF_mult; try easy;
       apply WF_get_col; easy.
Qed.

Lemma WF_row_add_each : forall {m n} (row : nat) (as' : Vector m) (T : Matrix m n),
  WF_Matrix T -> WF_Matrix as' -> WF_Matrix (row_add_each T as' row).
Proof. intros.
       unfold row_add_each.
       apply WF_plus; try easy;
       apply WF_mult; try easy;
       apply WF_get_row; easy.
Qed.

Lemma WF_make_col_val : forall {m n} (T : Matrix m n) (col : nat) (a : C),
  col < n ->
  WF_Matrix T -> WF_Matrix (make_col_val T col a).
Proof. unfold make_col_val, WF_Matrix.
       intros. 
       bdestruct_all; simpl; rewrite H0; try easy.
Qed.

Lemma WF_make_row_val : forall {m n} (T : Matrix m n) (row : nat) (a : C),
  row < m ->
  WF_Matrix T -> WF_Matrix (make_row_val T row a).
Proof. unfold make_row_val, WF_Matrix.
       intros. 
       bdestruct_all; simpl; rewrite H0; try easy.
Qed.

Lemma WF_col_to_front : forall {m n} (T : Matrix m n) (col : nat), 
  col < n -> 
  WF_Matrix T -> 
  WF_Matrix (col_to_front T col).
Proof. intros. 
       unfold WF_Matrix, col_to_front; intros. 
       bdestruct_all; apply H0; lia.
Qed.

Lemma WF_row_to_front : forall {m n} (T : Matrix m n) (row : nat), 
  row < m -> 
  WF_Matrix T -> 
  WF_Matrix (row_to_front T row).
Proof. intros. 
       unfold WF_Matrix, row_to_front; intros. 
       bdestruct_all; apply H0; lia.
Qed.

Lemma WF_col_replace : forall {m n} (T : Matrix m n) (col rep : nat), 
  rep < n -> 
  WF_Matrix T -> 
  WF_Matrix (col_replace T col rep).
Proof. intros. 
       unfold WF_Matrix, col_replace; intros. 
       bdestruct_all; apply H0; lia.
Qed.

Lemma WF_row_replace : forall {m n} (T : Matrix m n) (row rep : nat), 
  rep < m -> 
  WF_Matrix T -> 
  WF_Matrix (row_replace T row rep).
Proof. intros. 
       unfold WF_Matrix, row_replace; intros. 
       bdestruct_all; apply H0; lia.
Qed.



#[export] Hint Resolve WF_get_col WF_get_row WF_reduce_row WF_reduce_col WF_reduce_vecn WF_get_minor : wf_db.
#[export] Hint Resolve WF_row_append WF_col_append WF_row_wedge WF_col_wedge WF_smash : wf_db.
#[export] Hint Resolve WF_col_swap WF_row_swap WF_col_scale WF_row_scale WF_col_add WF_row_add : wf_db.
#[export] Hint Resolve WF_gen_new_col WF_gen_new_row WF_col_add_many WF_row_add_many : wf_db.
#[export] Hint Resolve WF_col_scale_many WF_row_scale_many WF_col_add_each WF_row_add_each  : wf_db.
#[export] Hint Resolve WF_make_col_val WF_make_row_val WF_col_to_front WF_row_to_front 
             col_replace row_replace: wf_db.

#[export] Hint Extern 1 (Nat.lt _ _) => lia : wf_db.
#[export] Hint Extern 1 (Nat.le _ _) => lia : wf_db.
#[export] Hint Extern 1 (lt _ _) => lia : wf_db.
#[export] Hint Extern 1 (le _ _) => lia : wf_db.

Lemma WF_pad1 : forall {m n : nat} (A : Matrix m n) (c : C),
  WF_Matrix A -> WF_Matrix (pad1 A c).
Proof. intros. 
       unfold pad1; auto with wf_db.
Qed.

Lemma WF_pad1_conv : forall {m n : nat} (A : Matrix m n) (c : C),
  WF_Matrix (pad1 A c) -> WF_Matrix A.
Proof. intros. 
       unfold pad1, WF_Matrix, col_wedge, row_wedge, e_i in *.
       intros. 
       rewrite <- (H (S x) (S y)); try lia. 
       bdestruct (S y <? 0); bdestruct (S y =? 0); try lia. 
       bdestruct (S x =? 0); bdestruct (S x <? 0); try lia; try easy.
       do 2 rewrite Sn_minus_1; easy.
Qed.


#[export] Hint Resolve WF_pad1 WF_pad1_conv : wf_db.



(** * proving basic lemmas about these new functions *)


Lemma get_col_reduce_col : forall {m n} (i col : nat) (T : Matrix m (S n)),
  i < col -> get_col (reduce_col T col) i = get_col T i.
Proof. intros. 
       prep_matrix_equality. 
       unfold get_col, reduce_col.
       bdestruct (i <? col); try lia; easy.
Qed.

Lemma get_col_conv : forall {m n} (x y : nat) (T : Matrix m n),
  (get_col T y) x 0 = T x y.
Proof. intros. unfold get_col.
       easy.
Qed.

Lemma get_row_conv : forall {m n} (x y : nat) (T : Matrix m n),
  (get_row T x) 0 y = T x y.
Proof. intros. unfold get_row.
       easy.
Qed.

Lemma get_col_mult : forall {n} (i : nat) (A B : Square n),
  A × (get_col B i) = get_col (A × B) i.
Proof. intros. unfold get_col, Mmult.
       prep_matrix_equality.
       bdestruct (y =? 0).
       - reflexivity.
       - apply @big_sum_0. intros.
         apply Cmult_0_r.
Qed.

Lemma det_by_get_col : forall {m n} (A B : Matrix m n),
  (forall i, get_col A i = get_col B i) -> A = B.
Proof. intros. prep_matrix_equality.
       rewrite <- get_col_conv.
       rewrite <- (get_col_conv _ _ B).
       rewrite H.
       reflexivity.
Qed.

Lemma get_col_reduce_wedge_miss : forall {m n} (T : Matrix m (S n)) (v : Vector m) (i : nat),
  i < n -> get_col (col_wedge (reduce_col T n) v n) i = get_col T i.
Proof. intros. 
       prep_matrix_equality. 
       unfold get_col, col_wedge, reduce_col.
       bdestruct_all; easy. 
Qed.

#[deprecated(note="Use get_col_reduce_wedge_miss instead")]
Notation get_col_reduce_append_miss := get_col_reduce_wedge_miss (only parsing).

Lemma get_col_reduce_wedge_hit : forall {m n} (T : Matrix m (S n)) (v : Vector m),
  WF_Matrix v -> get_col (col_wedge (reduce_col T n) v n) n = v.
Proof. intros.        
       unfold get_col, col_wedge, reduce_col.
       prep_matrix_equality. 
       bdestruct (y =? 0).
       - bdestruct_all; subst; easy. 
       - rewrite H; try lia; easy.
Qed.

#[deprecated(note="Use get_col_reduce_wedge_hit instead")]
Notation get_col_reduce_append_hit := get_col_reduce_wedge_hit (only parsing).


Lemma get_col_over : forall {m n} (T : Matrix m (S n)) (i : nat),
  WF_Matrix T -> i > n -> 
  get_col T i = Zero.
Proof. intros. 
       prep_matrix_equality. 
       unfold get_col.
       bdestruct_all; try easy.  
       rewrite H. easy.
       right. lia. 
Qed.

Lemma get_col_col_scale_many : forall {m n} (T : Matrix m n) (as' : Matrix 1 n) (i : nat),
  get_col (col_scale_many T as') i = as' O i .* get_col T i.
Proof. intros. 
       unfold get_col, col_scale_many, scale.
       prep_matrix_equality.
       bdestruct_all; lca.
Qed.

Lemma get_row_row_scale_many : forall {m n} (T : Matrix m n) (as' : Vector m) (i : nat),
  get_row (row_scale_many T as') i = as' i O .* get_row T i.
Proof. intros. 
       unfold get_row, row_scale_many, scale.
       prep_matrix_equality.
       bdestruct_all; lca.
Qed.


Lemma col_scale_reduce_col_same : forall {m n} (T : Matrix m (S n)) (y col : nat) (a : C),
  y = col -> reduce_col (col_scale T col a) y = reduce_col T y.
Proof. intros.
       prep_matrix_equality. 
       unfold reduce_col, col_scale. 
       bdestruct (y0 <? y); bdestruct (y0 =? col); bdestruct (1 + y0 =? col); try lia; easy. 
Qed.

Lemma col_swap_get_minor_before : forall {n : nat} (A : Square (S n)) (row col c1 c2 : nat),
  col < (S c1) -> col < (S c2) ->
  get_minor (col_swap A (S c1) (S c2)) row col = col_swap (get_minor A row col) c1 c2.
Proof. intros. 
       prep_matrix_equality. 
       unfold get_minor, col_swap.
       bdestruct (c1 <? col); bdestruct (c2 <? col); try lia. 
       simpl. 
       bdestruct (x <? row); bdestruct (y <? col); bdestruct (y =? c1);
         bdestruct (y =? S c1); bdestruct (y =? c2); bdestruct (y =? S c2); try lia; try easy. 
Qed.

Lemma col_scale_get_minor_before : forall {n : nat} (A : Square (S n)) (x y col : nat) (a : C),
  y < col -> get_minor (col_scale A col a) x y = col_scale (get_minor A x y) (col - 1) a.
Proof. intros. 
       prep_matrix_equality. 
       destruct col; try lia. 
       rewrite Sn_minus_1. 
       unfold get_minor, col_scale. 
       bdestruct (x0 <? x); bdestruct (y0 <? y); bdestruct (y0 =? S col);
         bdestruct (y0 =? col); bdestruct (1 + y0 =? S col); try lia; easy. 
Qed.

Lemma col_scale_get_minor_same : forall {n : nat} (A : Square (S n)) (x y col : nat) (a : C),
  y = col -> get_minor (col_scale A col a) x y = get_minor A x y.
Proof. intros. 
       prep_matrix_equality. 
       unfold get_minor, col_scale. 
       bdestruct (x0 <? x); bdestruct (y0 <? y);
         bdestruct (y0 =? col); bdestruct (1 + y0 =? col); try lia; easy. 
Qed.

Lemma col_scale_get_minor_after : forall {n : nat} (A : Square (S n)) (x y col : nat) (a : C),
  y > col -> get_minor (col_scale A col a) x y = col_scale (get_minor A x y) col a.
Proof. intros. 
       prep_matrix_equality. 
       unfold get_minor, col_scale. 
       bdestruct (x0 <? x); bdestruct (y0 <? y);
         bdestruct (y0 =? col); bdestruct (1 + y0 =? col); try lia; easy. 
Qed.

Lemma row_scale_get_minor_before : forall {n : nat} (A : Square (S n)) (x y row : nat) (a : C),
  x < row -> get_minor (row_scale A row a) x y = row_scale (get_minor A x y) (row - 1) a.
Proof. intros. 
       prep_matrix_equality. 
       destruct row; try lia. 
       rewrite Sn_minus_1. 
       unfold get_minor, row_scale. 
       bdestruct_all; simpl; easy.
Qed.

Lemma row_scale_get_minor_same : forall {n : nat} (A : Square (S n)) (x y row : nat) (a : C),
  x = row -> get_minor (row_scale A row a) x y = get_minor A x y.
Proof. intros. 
       prep_matrix_equality. 
       unfold get_minor, row_scale. 
       bdestruct_all; simpl; easy. 
Qed.

Lemma row_scale_get_minor_after : forall {n : nat} (A : Square (S n)) (x y row : nat) (a : C),
  x > row -> get_minor (row_scale A row a) x y = row_scale (get_minor A x y) row a.
Proof. intros. 
       prep_matrix_equality. 
       unfold get_minor, row_scale. 
       bdestruct_all; simpl; easy.
Qed.

Lemma mcv_reduce_col_same : forall {m n} (T : Matrix m (S n)) (col : nat) (a : C),
  reduce_col (make_col_val T col a) col = reduce_col T col.
Proof. intros. 
       prep_matrix_equality. 
       unfold reduce_col, make_col_val. 
       bdestruct (y <? col); bdestruct (1 + y <? col); 
         bdestruct (y =? col); bdestruct (1 + y =? col); try lia; easy. 
Qed.

Lemma mrv_reduce_row_same : forall {m n} (T : Matrix (S m) n) (row : nat) (a : C),
  reduce_row (make_row_val T row a) row = reduce_row T row.
Proof. intros. 
       prep_matrix_equality. 
       unfold reduce_row, make_row_val. 
       bdestruct (x <? row); bdestruct (1 + x <? row); 
         bdestruct (x =? row); bdestruct (1 + x =? row); try lia; easy. 
Qed.

Lemma col_add_many_reduce_col_same : forall {m n} (T : Matrix m (S n)) (v : Vector (S n))
                                            (col : nat),
  reduce_col (col_add_many T v col) col = reduce_col T col.
Proof. intros. 
       unfold reduce_col, col_add_many.
       prep_matrix_equality. 
       bdestruct (y <? col); bdestruct (1 + y <? col); 
         bdestruct (y =? col); bdestruct (1 + y =? col); try lia; easy. 
Qed.

Lemma row_add_many_reduce_row_same : forall {m n} (T : Matrix (S m) n) (v : Matrix 1 (S m))
                                            (row : nat),
  reduce_row (row_add_many T v row) row = reduce_row T row.
Proof. intros. 
       unfold reduce_row, row_add_many.
       prep_matrix_equality. 
       bdestruct (x <? row); bdestruct (1 + x <? row); 
         bdestruct (x =? row); bdestruct (1 + x =? row); try lia; easy. 
Qed.

Lemma col_wedge_reduce_col_same : forall {m n} (T : Matrix m n) (v : Vector n)
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

Lemma row_wedge_reduce_row_same : forall {m n} (T : Matrix m n) (v : Matrix 1 m)
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

Lemma col_wedge_zero : forall {m n} (T : Matrix m n) (j : nat),
  col_wedge T Zero j = Zero ->
  T = Zero.
Proof. intros. 
       prep_matrix_equality.
       unfold col_wedge in H.
       apply (f_equal_inv x) in H.
       bdestruct (y <? j).
       - apply (f_equal_inv y) in H.
         bdestruct (y <? j); try lia. 
         easy.
       - apply (f_equal_inv (y + 1)) in H.
         bdestruct (y + 1 <? j); bdestruct (y + 1 =? j); try lia.
         replace (y + 1 - 1)%nat with y in H by lia.
         rewrite H; easy.
Qed.

Lemma row_wedge_zero : forall {m n} (T : Matrix m n) (i : nat),
  row_wedge T Zero i = Zero ->
  T = Zero.
Proof. intros. 
       prep_matrix_equality.
       unfold row_wedge in H.
       bdestruct (x <? i).
       - apply (f_equal_inv x) in H.
         apply (f_equal_inv y) in H.
         bdestruct (x <? i); try lia. 
         easy.
       - apply (f_equal_inv (x + 1)) in H.
         apply (f_equal_inv y) in H.
         bdestruct (x + 1 <? i); bdestruct (x + 1 =? i); try lia.
         replace (x + 1 - 1)%nat with x in H by lia.
         rewrite H; easy.
Qed.

Lemma col_add_many_reduce_row : forall {m n} (T : Matrix (S m) n) (v : Vector n) (col row : nat),
  col_add_many (reduce_row T row) v col = reduce_row (col_add_many T v col) row.
Proof. intros. 
       prep_matrix_equality. 
       unfold col_add_many, reduce_row, gen_new_col, scale, get_col. 
       bdestruct (y =? col); try lia; try easy. 
       bdestruct (x <? row); try lia. 
       apply f_equal_gen; auto.
       do 2 rewrite Msum_Csum.
       apply big_sum_eq_bounded; intros. 
       bdestruct (x <? row); try lia; easy.
       apply f_equal_gen; auto.
       do 2 rewrite Msum_Csum.
       apply big_sum_eq_bounded; intros. 
       bdestruct (x <? row); try lia; easy.
Qed.

Lemma col_swap_same : forall {m n} (T : Matrix m n) (x : nat),
  col_swap T x x = T.
Proof. intros. 
       unfold col_swap. 
       prep_matrix_equality. 
       bdestruct (y =? x); try easy.
       rewrite H; easy.
Qed. 

Lemma row_swap_same : forall {m n} (T : Matrix m n) (x : nat),
  row_swap T x x = T.
Proof. intros. 
       unfold row_swap. 
       prep_matrix_equality. 
       bdestruct (x0 =? x); try easy.
       rewrite H; easy.
Qed. 

Lemma col_swap_diff_order : forall {m n} (T : Matrix m n) (x y : nat),
  col_swap T x y = col_swap T y x.
Proof. intros. 
       prep_matrix_equality. 
       unfold col_swap.
       bdestruct (y0 =? x); bdestruct (y0 =? y); try easy.
       rewrite <- H, <- H0; easy.
Qed.

Lemma row_swap_diff_order : forall {m n} (T : Matrix m n) (x y : nat),
  row_swap T x y = row_swap T y x.
Proof. intros. 
       prep_matrix_equality. 
       unfold row_swap.
       bdestruct (x0 =? x); bdestruct (x0 =? y); try easy.
       rewrite <- H, <- H0; easy.
Qed.

Lemma col_swap_inv : forall {m n} (T : Matrix m n) (x y : nat),
  T = col_swap (col_swap T x y) x y.
Proof. intros. 
       prep_matrix_equality. 
       unfold col_swap.
       bdestruct (y0 =? x); bdestruct (y0 =? y); 
         bdestruct (y =? x); bdestruct (x =? x); bdestruct (y =? y); 
         try easy. 
       all : (try rewrite H; try rewrite H0; try rewrite H1; easy).
Qed.

Lemma row_swap_inv : forall {m n} (T : Matrix m n) (x y : nat),
  T = row_swap (row_swap T x y) x y.
Proof. intros. 
       prep_matrix_equality. 
       unfold row_swap.
       bdestruct (x0 =? x); bdestruct (x0 =? y); 
         bdestruct (y =? x); bdestruct (x =? x); bdestruct (y =? y); 
         try easy. 
       all : (try rewrite H; try rewrite H0; try rewrite H1; easy).
Qed.

Lemma col_swap_get_col : forall {m n} (T : Matrix m n) (x y : nat),
  get_col (col_swap T x y) x = get_col T y.
Proof. intros. 
       prep_matrix_equality. 
       unfold get_col, col_swap. 
       bdestruct (x =? x); bdestruct (x =? y); try lia; try easy.
Qed.

Lemma col_swap_get_col_miss : forall {m n} (T : Matrix m n) (i x y : nat),
  i <> x -> i <> y -> 
  get_col (col_swap T x y) i = get_col T i.
Proof. intros. 
       prep_matrix_equality. 
       unfold get_col, col_swap.
       bdestruct_all; easy.
Qed.

Lemma col_swap_three : forall {m n} (T : Matrix m n) (x y z : nat),
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

Lemma col_to_front_swap_col : forall {m n} (T : Matrix m n) (col : nat),
  (S col) < n -> 
  col_to_front T (S col) = col_to_front (col_swap T col (S col)) col.
Proof. intros. 
       unfold col_to_front, col_swap.
       prep_matrix_equality.
       bdestruct_all; auto; subst.
       replace (S col - 1)%nat with col by lia.
       easy.
Qed.

Lemma row_to_front_swap_row : forall {m n} (T : Matrix m n) (row : nat),
  (S row) < m -> 
  row_to_front T (S row) = row_to_front (row_swap T row (S row)) row.
Proof. intros. 
       unfold row_to_front, row_swap.
       prep_matrix_equality.
       bdestruct_all; auto; subst.
       replace (S row - 1)%nat with row by lia.
       easy.
Qed.


Lemma col_to_front_0 : forall {m n} (T : Matrix m n),
  col_to_front T 0 = T.
Proof. intros. 
       unfold col_to_front.
       prep_matrix_equality.
       bdestruct_all; subst; easy.
Qed.

Lemma row_to_front_0 : forall {m n} (T : Matrix m n),
  row_to_front T 0 = T.
Proof. intros. 
       unfold row_to_front.
       prep_matrix_equality.
       bdestruct_all; subst; easy.
Qed.

Lemma reduce_wedge_split_0 : forall {m n} (T : Matrix m (S n)), 
  WF_Matrix T -> T = col_wedge (reduce_col T O) (get_col T O) O.
Proof. intros. 
       prep_matrix_equality. 
       unfold col_wedge, get_col, reduce_col.
       bdestruct_all; subst; try easy.
       replace (1 + (y - 1)) with y by lia.
       easy.
Qed.

Lemma reduce_wedge_split_n : forall {m n} (T : Matrix m (S n)), 
  WF_Matrix T -> T = col_wedge (reduce_col T n) (get_col T n) n.
Proof. intros. 
       prep_matrix_equality. 
       unfold col_wedge, get_col, reduce_col.
       bdestruct_all; subst; try easy.
       do 2 (rewrite H; try lia); easy. 
Qed.

#[deprecated(note="Use reduce_wedge_split_n instead")]
 Notation reduce_append_split := reduce_wedge_split_n (only parsing).

(* the dimensions don't match, so this is a bit weird *)
Lemma smash_zero : forall {m n} (T : Matrix m n) (i : nat),
  WF_Matrix T -> smash T (@Zero m i) = T. 
Proof. intros. 
       prep_matrix_equality.
       unfold smash, Zero. 
       bdestruct (y <? n); try easy.
       rewrite H; try lia; easy.
Qed.

Lemma smash_assoc : forall {m n1 n2 n3}
                           (T1 : Matrix m n1) (T2 : Matrix m n2) (T3 : Matrix m n3),
  smash (smash T1 T2) T3 = smash T1 (smash T2 T3).
Proof. intros. 
       unfold smash.
       prep_matrix_equality.
       bdestruct (y <? n1 + n2); bdestruct (y <? n1); 
         bdestruct (y - n1 <? n2); try lia; try easy.
       assert (H' : y - (n1 + n2) = y - n1 - n2).
       lia. rewrite H'; easy.
Qed.

Lemma smash_wedge : forall {m n} (T : Matrix m n) (v : Vector m),
  WF_Matrix T -> WF_Matrix v ->
  col_wedge T v n = smash T v.
Proof. intros. 
       unfold smash, col_wedge, WF_Matrix in *.
       prep_matrix_equality. 
       bdestruct (y =? n); bdestruct (y <? n); try lia; try easy.
       rewrite H1.
       rewrite Nat.sub_diag; easy. 
       rewrite H0, H; try lia; try easy.
Qed.

#[deprecated(note="Use smash_wedge instead")]
 Notation smash_append := smash_wedge (only parsing).


Lemma smash_reduce : forall {m n1 n2} (T1 : Matrix m n1) (T2 : Matrix m (S n2)),
  reduce_col (smash T1 T2) (n1 + n2) = smash T1 (reduce_col T2 n2).
Proof. intros. 
       prep_matrix_equality. 
       unfold reduce_col, smash. 
       bdestruct (y <? n1 + n2); bdestruct (y <? n1); bdestruct (1 + y <? n1);
         bdestruct (y - n1 <? n2); try lia; try easy.
       assert (H' : 1 + y - n1 = 1 + (y - n1)). lia.  
       rewrite H'; easy.
Qed.

Lemma split_col : forall {m n} (T : Matrix m (S n)), 
  T = smash (get_col T 0) (reduce_col T 0).
Proof. intros. 
       prep_matrix_equality. 
       unfold smash, get_col, reduce_col.
       bdestruct (y <? 1); bdestruct (y =? 0); bdestruct (y - 1 <? 0); try lia; try easy.
       rewrite H0; easy. 
       destruct y; try lia. 
       simpl. assert (H' : y - 0 = y). lia. 
       rewrite H'; easy.
Qed.


Lemma get_minor_col_to_front : forall {n} (A : Square (S n)) (col x : nat),
  get_minor (col_to_front A col) x 0 = get_minor A x col.
Proof. intros.   
       unfold get_minor, col_to_front.
       prep_matrix_equality.
       bdestruct_all; auto.
       all : apply f_equal; lia.
Qed.

Lemma get_minor_row_to_front : forall {n} (A : Square (S n)) (row y : nat),
  get_minor (row_to_front A row) 0 y = get_minor A row y.
Proof. intros.   
       unfold get_minor, row_to_front.
       prep_matrix_equality.
       bdestruct_all; auto.
       all : apply f_equal_gen; try apply f_equal; lia.
Qed.

Lemma get_minor_col_replace : forall {n} (A : Square (S n)) (col rep x : nat),
  get_minor (col_replace A col rep) x rep = get_minor A x rep.
Proof. intros. 
       unfold get_minor, col_replace.
       prep_matrix_equality.
       bdestruct_all; subst; auto.
Qed.

Lemma get_minor_row_replace : forall {n} (A : Square (S n)) (row rep y : nat),
  get_minor (row_replace A row rep) rep y = get_minor A rep y.
Proof. intros. 
       unfold get_minor, row_replace.
       prep_matrix_equality.
       bdestruct_all; subst; auto.
Qed.

Lemma reduce_row_reduce_col : forall {m n} (T : Matrix (S m) (S n)) (i j : nat),
  reduce_col (reduce_row T i) j = reduce_row (reduce_col T j) i.
Proof. intros. 
       prep_matrix_equality. 
       unfold reduce_col, reduce_row.
       bdestruct (y <? j); bdestruct (x <? i); try lia; try easy. 
Qed.

Lemma reduce_col_swap_01 : forall {m n} (T : Matrix m (S (S n))),
  reduce_col (reduce_col (col_swap T 0 1) 0) 0 = reduce_col (reduce_col T 0) 0.
Proof. intros. 
       prep_matrix_equality. 
       unfold reduce_col, col_swap.
       bdestruct (y <? 0); bdestruct (1 + y <? 0); try lia. 
       bdestruct (1 + (1 + y) =? 0); bdestruct (1 + (1 + y) =? 1); try lia. 
       easy. 
Qed.

Lemma reduce_col_2x : forall {m n} (T : Matrix m (S (S n))) (i j : nat),
  i < j ->
  reduce_col (reduce_col T i) (j - 1) = reduce_col (reduce_col T j) i.
Proof. intros. 
       destruct j; try lia.
       replace (S j - 1) with j by lia.
       prep_matrix_equality. 
       unfold reduce_col.
       bdestruct_all; easy. 
Qed.

Lemma get_minor_2x_0 : forall {n} (A : Square (S (S n))) (x y : nat),
  x <= y ->
  (get_minor (get_minor A x 0) y 0) = (get_minor (get_minor A (S y) 0) x 0).
Proof. intros.
       prep_matrix_equality.
       unfold get_minor. 
       bdestruct (y0 <? 0); bdestruct (1 + y0 <? 0); try lia. 
       bdestruct (x0 <? y); bdestruct (x0 <? S y); bdestruct (x0 <? x); 
         bdestruct (1 + x0 <? S y); bdestruct (1 + x0 <? x); 
         try lia; try easy.
Qed.     

Lemma col_add_split : forall {n} (A : Square (S n)) (i : nat) (c : C),
  col_add A 0 i c = col_wedge (reduce_col A 0) (get_col A 0 .+ c.* get_col A i) 0.
Proof. intros. 
       prep_matrix_equality. 
       unfold col_add, col_wedge, reduce_col, get_col, Mplus, scale.
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

Lemma col_swap_end_reduce_col_hit : forall {m n} (T : Matrix n (S (S m))) (i : nat),
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

Lemma col_swap_reduce_row : forall {m n} (T : Matrix (S n) m) (x y row : nat),
  col_swap (reduce_row T row) x y = reduce_row (col_swap T x y) row.
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


Lemma col_add_double : forall {m n} (T : Matrix m n) (x : nat) (a : C),
  col_add T x x a = col_scale T x (C1 + a)%C.
Proof. intros. 
       prep_matrix_equality. 
       unfold col_add, col_scale. 
       bdestruct (y =? x).
       - rewrite H; ring. 
       - easy.
Qed.

Lemma row_add_double : forall {m n} (T : Matrix m n) (x : nat) (a : C),
  row_add T x x a = row_scale T x (C1 + a)%C.
Proof. intros. 
       prep_matrix_equality. 
       unfold row_add, row_scale. 
       bdestruct (x0 =? x).
       - rewrite H; ring. 
       - easy.
Qed.

Lemma col_add_swap : forall {m n} (T : Matrix m n) (x y : nat) (a : C),
  col_swap (col_add T x y a) x y = col_add (col_swap T x y) y x a. 
Proof. intros. 
       prep_matrix_equality. 
       unfold col_swap, col_add.
       bdestruct (y0 =? x); bdestruct (y =? x);
         bdestruct (y0 =? y); bdestruct (x =? x); try lia; easy. 
Qed.
       
Lemma row_add_swap : forall {m n} (T : Matrix m n) (x y : nat) (a : C),
  row_swap (row_add T x y a) x y = row_add (row_swap T x y) y x a. 
Proof. intros. 
       prep_matrix_equality. 
       unfold row_swap, row_add.
       bdestruct_all; easy.
Qed.

Lemma col_add_inv : forall {m n} (T : Matrix m n) (x y : nat) (a : C),
  x <> y -> T = col_add (col_add T x y a) x y (-a).
Proof. intros. 
       prep_matrix_equality.
       unfold col_add.
       bdestruct (y0 =? x); bdestruct (y =? x); try lia. 
       ring. easy. 
Qed.

Lemma row_add_inv : forall {m n} (T : Matrix m n) (x y : nat) (a : C),
  x <> y -> T = row_add (row_add T x y a) x y (-a).
Proof. intros. 
       prep_matrix_equality.
       unfold row_add.
       bdestruct (x0 =? x); bdestruct (y =? x); try lia. 
       ring. easy. 
Qed.

Lemma col_swap_make_WF : forall {m n} (T : Matrix m n) (x y : nat),
  x < n -> y < n -> col_swap (make_WF T) x y = make_WF (col_swap T x y).
Proof. intros.
       unfold make_WF, col_swap. 
       prep_matrix_equality.
       bdestruct_all; try easy. 
Qed.

Lemma col_scale_make_WF : forall {m n} (T : Matrix m n) (x : nat) (c : C),
  col_scale (make_WF T) x c = make_WF (col_scale T x c).
Proof. intros.
       unfold make_WF, col_scale. 
       prep_matrix_equality.
       bdestruct_all; try easy; simpl; ring. 
Qed.

Lemma scalar_make_WF : forall {m n} (T : Matrix m n) (c : C),
  c .* (make_WF T) = make_WF (c .* T).
Proof. intros. 
       unfold scale, make_WF.
       prep_matrix_equality. 
       bdestruct_all; simpl; ring.
Qed.

Lemma col_add_make_WF : forall {m n} (T : Matrix m n) (x y : nat) (c : C),
  x < n -> y < n -> col_add (make_WF T) x y c = make_WF (col_add T x y c).
Proof. intros.
       unfold make_WF, col_add. 
       prep_matrix_equality.
       bdestruct_all; try easy; simpl; ring. 
Qed.

Lemma transpose_make_WF : forall {m n} (T : Matrix m n),
  (make_WF T) ⊤ = make_WF (T⊤).
Proof. intros. 
       unfold transpose, make_WF.
       prep_matrix_equality. 
       bdestruct_all; simpl; ring.
Qed.

Lemma gen_new_vec_0 : forall {m n} (T : Matrix m n) (as' : Vector n),
  as' == Zero -> gen_new_col m n T as' = Zero.
Proof. intros.
       unfold mat_equiv, gen_new_col in *.
       prep_matrix_equality.
       rewrite Msum_Csum.
       unfold Zero in *.
       apply (@big_sum_0_bounded); intros. 
       rewrite H; try lia. 
       rewrite Mscale_0_l.
       easy.
Qed.

Lemma gen_new_row_0 : forall {m n} (T : Matrix m n) (as' : Matrix 1 m),
  as' == Zero -> gen_new_row m n T as' = Zero.
Proof. intros.
       unfold mat_equiv, gen_new_row in *.
       prep_matrix_equality.
       rewrite Msum_Csum.
       unfold Zero in *.
       apply (@big_sum_0_bounded); intros. 
       rewrite H; try lia. 
       rewrite Mscale_0_l.
       easy.
Qed.

Lemma col_add_many_0 : forall {m n} (T : Matrix m n) (as' : Vector n) (col : nat),
  as' == Zero -> T = col_add_many T as' col. 
Proof. intros. 
       unfold col_add_many in *.
       prep_matrix_equality.
       bdestruct (y =? col); try easy.
       rewrite gen_new_vec_0; try easy.
       unfold Zero; ring. 
Qed.

Lemma row_add_many_0 : forall {m n} (T : Matrix m n) (as' : Matrix 1 m) (row : nat),
  as' == Zero -> T = row_add_many T as' row.
Proof. intros. 
       unfold row_add_many in *.
       prep_matrix_equality. 
       bdestruct (x =? row); try easy.
       rewrite gen_new_row_0; try easy.
       unfold Zero; ring. 
Qed.

Lemma gen_new_vec_mat_equiv : forall {m n} (T : Matrix m n) (as' bs : Vector n),
  as' == bs -> gen_new_col m n T as' = gen_new_col m n T bs.
Proof. unfold mat_equiv, gen_new_col; intros.
       prep_matrix_equality.
       do 2 rewrite Msum_Csum.
       apply big_sum_eq_bounded; intros. 
       rewrite H; try lia. 
       easy.
Qed.

Lemma gen_new_row_mat_equiv : forall {m n} (T : Matrix m n) (as' bs : Matrix 1 m),
  as' == bs -> gen_new_row m n T as' = gen_new_row m n T bs.
Proof. unfold mat_equiv, gen_new_row; intros.
       prep_matrix_equality.
       do 2 rewrite Msum_Csum.
       apply big_sum_eq_bounded; intros. 
       rewrite H; try lia. 
       easy.
Qed.

Lemma col_add_many_mat_equiv : forall {m n} (T : Matrix m n) (as' bs : Vector n) (col : nat),
  as' == bs -> col_add_many T as' col = col_add_many T bs col.
Proof. intros. 
       unfold col_add_many.
       rewrite (gen_new_vec_mat_equiv _ as' bs); easy.
Qed.

Lemma row_add_many_mat_equiv : forall {m n} (T : Matrix m n) (as' bs : Matrix 1 m) (row : nat),
  as' == bs -> row_add_many T as' row = row_add_many T bs row.
Proof. intros. 
       unfold row_add_many.
       rewrite (gen_new_row_mat_equiv _ as' bs); easy.
Qed.

Lemma col_add_each_0 : forall {m n} (T : Matrix m n) (v : Matrix 1 n) (col : nat),
  v = Zero -> T = col_add_each T v col.
Proof. intros. 
       rewrite H.
       unfold col_add_each.
       rewrite Mmult_0_r; auto.
       erewrite Mplus_0_r; auto.
Qed.

Lemma row_add_each_0 : forall {m n} (T : Matrix m n) (v : Vector m) (row : nat) ,
  v = Zero -> T = row_add_each T v row.
Proof. intros. 
       rewrite H.
       unfold row_add_each.
       rewrite Mmult_0_l; auto.
       erewrite Mplus_0_r; auto.
Qed.


(* TODO: this should have just been the origional definition... *)
Lemma gen_new_col_is_mul : forall {m n} (T : Matrix m n) (as' : Vector n),
  WF_Matrix as' -> 
  gen_new_col m n T as' = T × as'.
Proof. intros. 
       prep_matrix_equality.
       unfold Mmult, gen_new_col.
       rewrite Msum_Csum.
       apply big_sum_eq_bounded; intros.
       unfold scale, get_col.
       bdestruct_all; subst. ring.
       rewrite (H x0 y); try ring.
       right; try lia.
Qed.

Lemma gen_new_row_is_mul : forall {m n} (T : Matrix m n) (as' : Matrix 1 m),
  WF_Matrix as' -> 
  gen_new_row m n T as' = as' × T.
Proof. intros. 
       prep_matrix_equality.
       unfold Mmult, gen_new_row.
       rewrite Msum_Csum.
       apply big_sum_eq_bounded; intros.
       unfold scale, get_row.
       bdestruct_all; subst. ring.
       rewrite (H x x0); try ring.
       left; try lia.
Qed.



Lemma col_add_many_mul : forall {m n} (T : Matrix m n) (as' : Vector n) (i col : nat), 
  i < m ->
  col < n ->
  ((T × as')) i O = 
    (col_add_many
       (col_scale T col (as' col O)) 
       (make_row_val as' col C0) 
       col) i col.  
Proof. intros. 
       unfold col_add_many, Mmult, col_scale, make_row_val, gen_new_col. 
       rewrite Msum_Csum.        
       bdestruct_all.
       destruct n; try lia.
       replace (S n) with (col + 1 + (n - col)) by lia.
       repeat rewrite big_sum_sum; simpl. 
       repeat rewrite Cplus_0_l.
       rewrite Cplus_assoc, Nat.add_0_r.
       rewrite (Cplus_comm _ (T i col * as' col O))%C.
       rewrite <- 2 Cplus_assoc.
       apply f_equal_gen; try apply f_equal.
       ring.    
       apply f_equal_gen; try apply f_equal; auto.
       bdestruct_all; simpl. 
       unfold scale, make_row_val, scale.  
       rewrite Cmult_0_l, Cplus_0_r.
       apply big_sum_eq_bounded; intros.
       unfold get_col; simpl.
       bdestruct_all; simpl; ring.
       apply big_sum_eq_bounded; intros.
       unfold scale, get_col.
       bdestruct_all; simpl.
       ring.
Qed.
       

(* lemmas about operations w.r.t.involving adjoint *) 

Lemma col_swap_adjoint : forall {m n} (T : Matrix m n) (x y : nat), 
  col_swap (adjoint T) x y = adjoint (row_swap T x y).
Proof. intros. 
       unfold adjoint, col_swap, row_swap.
       prep_matrix_equality.
       bdestruct_all; easy.
Qed.

Lemma row_swap_adjoint : forall {m n} (T : Matrix m n) (x y : nat), 
  row_swap (adjoint T) x y = adjoint (col_swap T x y).
Proof. intros. 
       unfold adjoint, col_swap, row_swap.
       prep_matrix_equality.
       bdestruct_all; easy.
Qed.


(*
(** * building up machinery to undo scaling *)

Local Open Scope group_scope.

(* v is thought of as a vector here, but is defined as a matrix so we dont need to use 
   get_row *)
Fixpoint get_common_multiple (m n : nat) (v : Matrix m n) : F :=
  match n with
  | O => 1
  | S n' => 
      match (Geq_dec (v O n') 0) with
      | left _ => get_common_multiple m n' (reduce_col v n')
      | right _ => (v O n') * (get_common_multiple m n' (reduce_col v n'))
      end
  end.

Arguments get_common_multiple {m n}.


Lemma gcm_simplify_eq_0 : forall {m n} (v : Matrix m (S n)),
  v O n = 0 -> 
  get_common_multiple v = get_common_multiple (reduce_col v n).
Proof. intros. 
       simpl. 
       destruct (Geq_dec (v O n) C0); try easy.
Qed.

Lemma gcm_simplify_neq_0 : forall {m n} (v : Matrix m (S n)),
  v O n <> 0 -> 
  get_common_multiple v = v O n * get_common_multiple (reduce_col v n).
Proof. intros. 
       simpl. 
       destruct (Geq_dec (v O n) C0); try easy.
Qed.


Lemma gcm_mat_equiv : forall {m n} (v1 v2 : Matrix m n),
  get_row v1 O ≡ get_row v2 O ->
  get_common_multiple v1 = get_common_multiple v2. 
Proof. induction n; intros. 
       - easy.
       - simpl.
         assert (H' : forall i, i < S n -> v1 O i = v2 O i).
         { intros. 
           unfold mat_equiv in H.
           apply (H O i) in H0; auto. }
         rewrite H', (IHn _ (reduce_col v2 n)); try lia; auto.
         unfold mat_equiv, get_row, reduce_col in *; intros.     
         apply (H _ j) in H0; try lia.
         bdestruct_all; easy.
Qed.

Lemma gcm_reduce_col_nonzero : forall {m n} (v : Matrix m (S n)) (i : nat),
  i < S n -> v O i <> 0 ->
  get_common_multiple v = v O i * get_common_multiple (reduce_col v i).
Proof. induction n; intros.
       - destruct i; try lia.
         rewrite <- gcm_simplify_neq_0; easy.
       - bdestruct (i =? S n); subst.
         + rewrite <- gcm_simplify_neq_0; auto.
         + destruct (Geq_dec (v O (S n)) 0). 
           * rewrite gcm_simplify_eq_0; auto.
             rewrite (IHn _ i); try lia.
             apply f_equal_gen; try apply f_equal.
             unfold reduce_col.
             bdestruct (i <? S n); try lia; auto.
             rewrite gcm_simplify_eq_0.
             rewrite <- reduce_col_2x; try lia.
             replace (S n - 1)%nat with n by lia.
             easy.
             all : unfold reduce_col; 
             bdestruct_all; try lia; simpl; easy.
           * rewrite gcm_simplify_neq_0; auto.
             rewrite (IHn _ i); try lia.
             rewrite gcm_simplify_neq_0.
             do 2 rewrite Cmult_assoc.
             apply f_equal_gen; try apply f_equal.
             unfold reduce_col.
             bdestruct_all; simpl; try lia; ring. 
             rewrite <- reduce_col_2x; try lia.
             replace (S n - 1)%nat with n by lia; easy.
             all : unfold reduce_col; 
             bdestruct_all; try lia; simpl; easy.
Qed.

Lemma gcm_reduce_col_zero : forall {m n} (v : Matrix m (S n)) (i : nat),
  i < S n -> v O i = 0 ->
  get_common_multiple v = get_common_multiple (reduce_col v i).
Proof. induction n; intros.
       - destruct i; try lia.
         rewrite <- gcm_simplify_eq_0; easy.
       - bdestruct (i =? S n); subst.
         + rewrite <- gcm_simplify_eq_0; auto.
         + destruct (Geq_dec (v O (S n)) 0). 
           * rewrite gcm_simplify_eq_0; auto.
             rewrite (IHn _ i); try lia.
             rewrite (IHn _ n); try lia.             
             rewrite <- reduce_col_2x; try lia.
             replace (S n - 1)%nat with n by lia.
             easy.
             all : unfold reduce_col; 
               bdestruct_all; try lia; simpl; easy.
           * rewrite gcm_simplify_neq_0; auto.
             rewrite (IHn _ i); try lia.
             rewrite gcm_simplify_neq_0.
             apply f_equal_gen; try apply f_equal.
             unfold reduce_col.
             bdestruct_all; simpl; try lia; ring. 
             rewrite <- reduce_col_2x; try lia.
             replace (S n - 1)%nat with n by lia; easy.
             all : unfold reduce_col; 
             bdestruct_all; try lia; simpl; easy.
Qed.

Lemma gcm_breakdown : forall {m n} (v : Matrix m (S n)) (i : nat),
  i < S n ->
  get_common_multiple v =  
  get_common_multiple (get_col v i) * get_common_multiple (reduce_col v i).
Proof. intros.
       simpl. 
       replace (get_col v i O O) with (v O i).
       destruct (Geq_dec (v O i) 0).
       - rewrite <- (gcm_reduce_col_zero _ i); auto.
         simpl; ring.
       - rewrite Cmult_1_r, <- (gcm_reduce_col_nonzero _ i); auto.
       - unfold get_col; easy.
Qed.


Lemma gcm_col_swap_le : forall {m n} (v : Matrix m (S n)) (i j : nat),
  i < j -> j < S n ->
  get_common_multiple v = get_common_multiple (col_swap v i j).
Proof. intros.
       destruct n.
       destruct i; destruct j; try lia.
       rewrite (gcm_breakdown _ i); try lia.
       rewrite (gcm_breakdown (reduce_col v i) (j - 1)); try lia.
       rewrite (gcm_breakdown (col_swap v i j) i); try lia.
       rewrite (gcm_breakdown (reduce_col (col_swap v i j) i) (j - 1)); try lia.
       replace (reduce_col (reduce_col (col_swap v i j) i) (j - 1)) with
         (reduce_col (reduce_col v i) (j - 1)).
       do 2 rewrite Cmult_assoc.
       apply f_equal_gen; try apply f_equal; auto.
       rewrite Cmult_comm.
       apply f_equal_gen; repeat try apply f_equal.      
       all : unfold get_col, reduce_col, col_swap;
       prep_matrix_equality;
       bdestruct_all; auto.
       replace (1 + (j - 1))%nat with j by lia. 
       easy.
Qed.    

Lemma gcm_col_swap : forall {m n} (v : Matrix m (S n)) (i j : nat),
  i < S n -> j < S n ->
  get_common_multiple v = get_common_multiple (col_swap v i j).
Proof. intros. 
       bdestruct (i <? j); bdestruct (i =? j); bdestruct (j <? i); try lia; subst.
       apply gcm_col_swap_le; lia.
       rewrite col_swap_same; auto.
       rewrite col_swap_diff_order.
       apply gcm_col_swap_le; lia.
Qed.


Opaque get_common_multiple.

*)


(*

Definition csm_to_scalar {n} (as' : Matrix 1 n) : Matrix 1 n :=
  match n with
  | O => Zero 
  | S n' => (fun i j => @get_common_multiple 1 n' (reduce_col as' j))
  end.


Lemma csm_to_scalar_ver : forall {n} (as' : Matrix 1 n) (i j : nat),  
  i < n -> j < n ->
  as' O i <> 0 -> as' O j <> 0 ->
  as' O i * csm_to_scalar as' O i = as' O j * csm_to_scalar as' O j.
Proof. intros.
       destruct n; try lia; simpl.
       rewrite <- 2 gcm_reduce_col_nonzero; auto.
Qed. 

*)


(** * more complicated lemmas/proofs as we begin to show the correspondence of the operations with matrix multiplication *)


Lemma col_scale_many_col_scale : forall {m n} (T : Matrix m n) (as' : Matrix 1 n) (e : nat),
  col_scale_many T as' = col_scale (col_scale_many T (make_col_val as' e C1)) e (as' 0 e).
Proof. intros. 
       unfold col_scale_many, col_scale, make_col_val.
       prep_matrix_equality.
       bdestruct_all; simpl; subst; try ring.
Qed.


Lemma col_scale_scalar : forall {m n} (T : Matrix m n) (x : nat) (a : C),
  a .* T = col_scale_many (col_scale T x a) (fun i j => if (j =? x) then C1 else a).
Proof. intros. 
       prep_matrix_equality. 
       unfold col_scale, col_scale_many, scale.
       bdestruct (y =? x); try easy.
       ring.
Qed.

Lemma row_scale_scalar : forall {m n} (T : Matrix m n) (x : nat) (a : C),
  a .* T = row_scale_many (row_scale T x a) (fun i j => if (i =? x) then C1 else a).
Proof. intros. 
       prep_matrix_equality. 
       unfold row_scale, row_scale_many, scale.
       bdestruct (x0 =? x); try easy.
       ring. 
Qed.

(*
Lemma col_scale_many_scalar : forall {m n} (T : Matrix m n) (as' : Matrix 1 n),
  WF_Matrix T -> 
  (forall j, j < n -> as' O j <> 0) ->
  (as' O O * csm_to_scalar as' O O) .* T = 
    col_scale_many (col_scale_many T as') (csm_to_scalar as').
Proof. intros. 
       apply mat_equiv_eq; auto with wf_db.
       unfold mat_equiv; intros. 
       destruct n; try lia.
       unfold col_scale_many, scale.
       rewrite (csm_to_scalar_ver _ O j); try lia; auto.
       ring.
       apply H0; lia.
Qed.
*)

Local Open Scope nat_scope. 


(* allows for induction on col_add_many *)
Lemma col_add_many_col_add : forall {m n} (T : Matrix m n) (as' : Vector n) (col e : nat),
  col <> e -> e < n -> as' col 0 = C0 ->
  col_add_many T as' col = 
  col_add (col_add_many T (make_row_val as' e C0) col) col e (as' e 0).
Proof. intros. 
       unfold col_add_many, col_add, gen_new_col.
       prep_matrix_equality.
       bdestruct (y =? col); try easy.
       bdestruct (e =? col); try lia.
       rewrite <- Cplus_assoc.
       apply f_equal_gen; try easy.
       assert (H' : n = e + (n - e)). lia. 
       rewrite H'.
       do 2 rewrite Msum_Csum. 
       rewrite big_sum_sum.
       rewrite big_sum_sum.
       rewrite <- Cplus_assoc.
       apply f_equal_gen; try apply f_equal; auto. 
       apply big_sum_eq_bounded; intros.
       unfold make_row_val.
       bdestruct (x0 =? e); try lia; easy. 
       destruct (n - e); try lia. 
       do 2 rewrite <- big_sum_extend_l.
       unfold make_row_val.
       bdestruct (e + 0 =? e); try lia. 
       unfold scale; simpl.
       rewrite Cmult_0_l, Cplus_0_l.
       rewrite Cplus_comm.
       apply f_equal_gen; try apply f_equal; auto. 
       apply big_sum_eq_bounded; intros.
       bdestruct (e + S x0 =? e); try lia; easy.
       unfold get_col. simpl. 
       rewrite Nat.add_0_r; easy.
Qed.

(* shows that we can eliminate a column in a matrix using col_add_many *)
Lemma col_add_many_cancel : forall {m n} (T : Matrix m (S n)) (as' : Vector (S n)) (col : nat),
  col < (S n) -> as' col O = C0 ->
  (reduce_col T col) × (reduce_row as' col) = -C1%C .* (get_col T col) -> 
  (forall i : nat, (col_add_many T as' col) i col = C0).
Proof. intros. 
       unfold col_add_many, gen_new_col.
       bdestruct (col =? col); try lia. 
       rewrite Msum_Csum. 
       assert (H' : (big_sum (fun x : nat => (as' x O .* get_col T x) i O) (S n) = 
                     (Mmult (reduce_col T col) (reduce_row as' col)) i O)%C).
       { unfold Mmult.
         replace (S n) with (col + (S (n - col))) by lia; rewrite big_sum_sum. 
         rewrite (le_plus_minus' col n); try lia; rewrite big_sum_sum. 
         apply f_equal_gen; try apply f_equal; auto. 
         apply big_sum_eq_bounded; intros. 
         unfold get_col, scale, reduce_col, reduce_row. 
         bdestruct (x <? col); simpl; try lia; ring.
         rewrite <- le_plus_minus', <- big_sum_extend_l, Nat.add_0_r, H0; try lia. 
         unfold scale; rewrite Cmult_0_l, Cplus_0_l.
         apply big_sum_eq_bounded; intros. 
         unfold get_col, scale, reduce_col, reduce_row. 
         bdestruct (col + x <? col); simpl; try lia. 
         assert (p3 : (col + S x) = (S (col + x))). lia.
         rewrite p3. ring. }
       rewrite H', H1.
       unfold scale, get_col. 
       bdestruct (0 =? 0); try lia. 
       simpl; ring.
Qed.

Lemma col_add_many_inv : forall {m n} (T : Matrix m n) (as' : Vector n) (col : nat) ,
  as' col O = C0 -> T = col_add_many (col_add_many T as' col) (-C1%C .* as') col.
Proof. intros. 
       unfold col_add_many, gen_new_col.
       prep_matrix_equality. 
       bdestruct (y =? col); try easy.
       rewrite <- (Cplus_0_r (T x y)).
       rewrite <- Cplus_assoc.
       apply f_equal_gen; try apply f_equal; auto; try ring.
       do 2 rewrite Msum_Csum. 
       rewrite <- (@big_sum_plus C _ _ C_is_comm_group). 
       rewrite @big_sum_0_bounded; auto.
       intros. 
       unfold get_col, scale.
       bdestruct (0 =? 0); bdestruct (x0 =? col); try lia; try lca.
       rewrite Msum_Csum.
       bdestruct (0 =? 0); try lia. 
       rewrite H3, H. 
       lca. 
Qed.

(* like above, allows for induction on col_add_each *)
Lemma col_add_each_col_add : forall {m n} (T : Matrix m n) (as' : Matrix 1 n) (col e : nat),
  col <> e -> (forall x, as' x col = C0) ->
              col_add_each T as' col = 
              col_add (col_add_each T (make_col_val as' e C0) col) e col (as' 0 e).
Proof. intros.
       prep_matrix_equality.
       unfold col_add_each, col_add, make_col_val, Mmult, Mplus, get_col, big_sum.
       bdestruct (y =? col); bdestruct (y =? e); bdestruct (col =? e); 
         bdestruct (e =? e); bdestruct (0 =? 0); simpl; try lia; try ring. 
       rewrite H0. 
       rewrite H2. ring.
Qed.

Lemma row_add_each_row_add : forall {m n} (T : Matrix m n) (as' : Vector m) (row e : nat),
  row <> e -> (forall y, as' row y = C0) ->
              row_add_each T as' row = 
              row_add (row_add_each T (make_row_val as' e C0) row) e row (as' e 0).
Proof. intros.
       prep_matrix_equality.
       unfold row_add_each, row_add, make_row_val, Mmult, Mplus, get_row, big_sum.
       bdestruct (x =? row); bdestruct (x =? e); bdestruct (row =? e); 
         bdestruct (e =? e); bdestruct (0 =? 0); simpl; try lia; try ring. 
       rewrite H0. 
       rewrite H2. ring.
Qed.

(* must use make_col_zero here instead of just as' col 0 = C0, since def requires stronger hyp *)
Lemma col_add_each_inv : forall {m n} (T : Matrix m n) (as' : Matrix 1 n) (col : nat),
  T = col_add_each (col_add_each T (make_col_val as' col C0) col) 
                   (make_col_val (-C1%C .* as') col C0) col.
Proof. intros. 
       prep_matrix_equality. 
       unfold col_add_each, make_col_val, Mmult, Mplus, get_col, scale.
       simpl. bdestruct (y =? col); bdestruct (col =? col); simpl; try lia; try ring. 
Qed.

Lemma row_add_each_inv : forall {m n} (T : Matrix m n) (as' : Vector m) (row : nat),
  T = row_add_each (row_add_each T (make_row_val as' row C0) row)
                   (make_row_val (-C1%C .* as') row C0) row.
                   
Proof. intros. 
       prep_matrix_equality. 
       unfold row_add_each, make_row_val, Mmult, Mplus, get_row, scale.
       simpl. bdestruct (x =? row); bdestruct (row =? row); simpl; try lia; try ring. 
Qed.


(* we can show that we get from col_XXX to row_XXX via transposing *)
(* helpful, since we can bootstrap many lemmas on cols for rows *)
Lemma get_col_transpose : forall {m n} (A : Matrix m n) (i : nat),
  (get_col A i)⊤ = get_row (A⊤) i.
Proof. intros. 
       prep_matrix_equality. 
       unfold get_col, get_row, transpose. 
       easy.
Qed.

Lemma get_row_transpose : forall {m n} (A : Matrix m n) (i : nat),
  (get_row A i)⊤ = get_col (A⊤) i.
Proof. intros. 
       prep_matrix_equality. 
       unfold get_col, get_row, transpose. 
       easy.
Qed.

Lemma col_swap_transpose : forall {m n} (A : Matrix m n) (x y : nat),
  (col_swap A x y)⊤ = row_swap (A⊤) x y.
Proof. intros. 
       prep_matrix_equality. 
       unfold row_swap, col_swap, transpose. 
       easy. 
Qed.

Lemma row_swap_transpose : forall {m n} (A : Matrix m n) (x y : nat),
  (row_swap A x y)⊤ = col_swap (A⊤) x y.
Proof. intros. 
       prep_matrix_equality. 
       unfold row_swap, col_swap, transpose. 
       easy. 
Qed.

Lemma col_scale_transpose : forall {m n} (A : Matrix m n) (x : nat) (a : C),
  (col_scale A x a)⊤ = row_scale (A⊤) x a.
Proof. intros. 
       prep_matrix_equality. 
       unfold row_scale, col_scale, transpose. 
       easy. 
Qed.

Lemma row_scale_transpose : forall {m n} (A : Matrix m n) (x : nat) (a : C),
  (row_scale A x a)⊤ = col_scale (A⊤) x a.
Proof. intros. 
       prep_matrix_equality. 
       unfold row_scale, col_scale, transpose. 
       easy. 
Qed.

Lemma col_scale_many_transpose : forall {m n} (A : Matrix m n) (as' : Matrix 1 n),
  (col_scale_many A as')⊤ = row_scale_many (A⊤) (as'⊤).
Proof. intros. 
       prep_matrix_equality. 
       unfold row_scale_many, col_scale_many, transpose. 
       easy. 
Qed.

Lemma row_scale_many_transpose : forall {m n} (A : Matrix m n) (as' : Vector m),
  (row_scale_many A as')⊤ = col_scale_many (A⊤) (as'⊤).
Proof. intros. 
       prep_matrix_equality. 
       unfold row_scale_many, col_scale_many, transpose. 
       easy. 
Qed.

Lemma col_add_transpose : forall {m n} (A : Matrix m n) (col to_add : nat) (a : C),
  (col_add A col to_add a)⊤ = row_add (A⊤) col to_add a.
Proof. intros. 
       prep_matrix_equality. 
       unfold row_add, col_add, transpose. 
       easy. 
Qed.

Lemma row_add_transpose : forall {m n} (A : Matrix m n) (row to_add : nat) (a : C),
  (row_add A row to_add a)⊤ = col_add (A⊤) row to_add a.
Proof. intros. 
       prep_matrix_equality. 
       unfold row_add, col_add, transpose. 
       easy. 
Qed.

Lemma col_add_many_transpose : forall {m n} (A : Matrix m n) (as' : Vector n) (col : nat),
  (col_add_many A as' col)⊤ = row_add_many (A⊤) (as'⊤) col.
Proof. intros. 
       prep_matrix_equality. 
       unfold row_add_many, col_add_many, transpose. 
       bdestruct (x =? col); try easy.
       apply f_equal_gen; try apply f_equal; auto.  
       unfold gen_new_col, gen_new_row, get_col, get_row, scale.
       do 2 rewrite Msum_Csum.
       apply big_sum_eq_bounded; intros. 
       easy. 
Qed.

Lemma row_add_many_transpose : forall {m n} (A : Matrix m n) (as' : Matrix 1 m) (row : nat),
  (row_add_many A as' row)⊤ = col_add_many (A⊤) (as'⊤) row.
Proof. intros. 
       prep_matrix_equality. 
       unfold row_add_many, col_add_many, transpose. 
       bdestruct (y =? row); try easy. 
       apply f_equal_gen; try apply f_equal; auto. 
       unfold gen_new_col, gen_new_row, get_col, get_row, scale.
       do 2 rewrite Msum_Csum.
       apply big_sum_eq_bounded; intros. 
       easy. 
Qed.

Lemma col_add_each_transpose : forall {m n} (A : Matrix m n) (as' : Matrix 1 n) (col : nat), 
  (col_add_each A as' col)⊤ = row_add_each (A⊤) (as'⊤) col.
Proof. intros. 
       unfold row_add_each, col_add_each. 
       rewrite Mplus_transpose.
       rewrite Mmult_transpose; auto.
Qed.

Lemma row_add_each_transpose : forall {m n} (A : Matrix m n) (as' : Vector m) (row : nat),
  (row_add_each A as' row)⊤ = col_add_each (A⊤) (as'⊤) row.
Proof. intros. 
       unfold row_add_each, col_add_each. 
       rewrite Mplus_transpose.
       rewrite Mmult_transpose; auto.
Qed.

Lemma get_minor_transpose : forall {n} (A : Square (S n)) (i j : nat),
  (get_minor A i j)⊤ = get_minor (A⊤) j i.
Proof. intros. 
       prep_matrix_equality.
       unfold get_minor, transpose.
       bdestruct_all; easy.
Qed.


(** the idea is to show that col operations correspond to multiplication by special matrices. *)
(** Thus, we show that the col ops all satisfy various multiplication rules *)
Lemma swap_preserves_mul_lt : forall {m n o} (A : Matrix m n) (B : Matrix n o) (x y : nat),
  x < y -> x < n -> y < n -> A × B = (col_swap A x y) × (row_swap B x y).
Proof. intros. 
       prep_matrix_equality. 
       unfold Mmult. 
       bdestruct (x <? n); try lia.
       rewrite (le_plus_minus' x n); try lia.
       do 2 rewrite big_sum_sum. 
       apply Cplus_simplify. 
       apply big_sum_eq_bounded.
       intros. 
       unfold col_swap, row_swap.
       bdestruct (x1 =? x); bdestruct (x1 =? y); try lia; try easy.   
       destruct (n - x) as [| x'] eqn:E; try lia. 
       do 2 rewrite <- big_sum_extend_l.
       rewrite Cplus_comm.
       rewrite (Cplus_comm (col_swap A x y x0 (x + 0)%nat * row_swap B x y (x + 0)%nat y0)%C _).
       bdestruct ((y - x - 1) <? x'); try lia.  
       rewrite (le_plus_minus' (y - x - 1) x'); try lia. 
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


Lemma swap_preserves_mul : forall {m n o} (A : Matrix m n) (B : Matrix n o) (x y : nat),
  x < n -> y < n -> A × B = (col_swap A x y) × (row_swap B x y).
Proof. intros. bdestruct (x <? y).
       - apply swap_preserves_mul_lt; easy.
       - destruct H1.
         + rewrite col_swap_same, row_swap_same; easy.
         + rewrite col_swap_diff_order, row_swap_diff_order. 
           apply swap_preserves_mul_lt; lia.
Qed.

Lemma scale_preserves_mul : forall {m n o} (A : Matrix m n) (B : Matrix n o) (x : nat) (a : C),
  A × (row_scale B x a) = (col_scale A x a) × B.
Proof. intros. 
       prep_matrix_equality. 
       unfold Mmult. 
       apply big_sum_eq_bounded.
       intros. 
       unfold col_scale, row_scale.
       bdestruct (x1 =? x).
       - rewrite Cmult_assoc.
         ring. 
       - reflexivity. 
Qed.     

Lemma scale_many_preserves_mul : forall {m n o} (A : Matrix m n) (B : Matrix n o) 
                                   (as' : Vector n),
  A × (row_scale_many B as') = (col_scale_many A (as'⊤)) × B.
Proof. intros. 
       prep_matrix_equality.
       unfold Mmult, row_scale_many, col_scale_many, transpose.
       apply big_sum_eq_bounded; intros.
       ring.
Qed.

Lemma add_preserves_mul_lt : forall {m n o} (A : Matrix m n) (B : Matrix n o) 
                                                (x y : nat) (a : C),
   x < y -> x < n -> y < n -> A × (row_add B y x a) = (col_add A x y a) × B.
Proof. intros.  
       prep_matrix_equality. 
       unfold Mmult.   
       bdestruct (x <? n); try lia.
       rewrite (le_plus_minus' x n); try lia.       
       do 2 rewrite big_sum_sum.
       apply Cplus_simplify. 
       apply big_sum_eq_bounded.
       intros. 
       unfold row_add, col_add.
       bdestruct (x1 =? y); bdestruct (x1 =? x); try lia; easy. 
       destruct (n - x) as [| x'] eqn:E; try lia. 
       do 2 rewrite <- big_sum_extend_l.
       rewrite Cplus_comm. 
       rewrite (Cplus_comm (col_add A x y a x0 (x + 0)%nat * B (x + 0)%nat y0)%C _).
       bdestruct ((y - x - 1) <? x'); try lia.  
       rewrite (le_plus_minus' (y - x - 1) x'); try lia. 
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


Lemma add_preserves_mul : forall {m n o} (A : Matrix m n) (B : Matrix n o) 
                                             (x y : nat) (a : C),
   x < n -> y < n -> A × (row_add B y x a) = (col_add A x y a) × B.
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

Lemma cam_ca_switch : forall {m n} (T : Matrix m n) (as' : Vector n) (col to_add : nat) (c : C),
  as' col 0 = C0 -> to_add <> col -> 
  col_add (col_add_many T as' col) col to_add c = 
  col_add_many (col_add T col to_add c) as' col.
Proof. intros. 
       prep_matrix_equality. 
       unfold col_add, col_add_many.
       bdestruct (y =? col); try lia; try easy.
       repeat rewrite <- Cplus_assoc.
       apply f_equal_gen; try apply f_equal; auto. 
       bdestruct (to_add =? col); try lia.
       rewrite Cplus_comm.
       apply f_equal_gen; try apply f_equal; auto. 
       unfold gen_new_col.
       do 2 rewrite Msum_Csum.
       apply big_sum_eq_bounded; intros. 
       unfold get_col, scale; simpl.
       bdestruct (x0 =? col); try ring. 
       rewrite H4, H; ring.
Qed.

Lemma col_add_many_preserves_mul_some : forall (m n o e col : nat) 
                                               (A : Matrix m n) (B : Matrix n o) (v : Vector n),
  WF_Matrix v -> (skip_count col e) < n -> col < n -> 
  (forall i : nat, (skip_count col e) < i -> v i 0 = C0) -> v col 0 = C0 ->
  A × (row_add_each B v col) = (col_add_many A v col) × B.  
Proof. induction e as [| e].
       - intros. 
         destruct n; try easy.  
         rewrite (col_add_many_col_add _ _ col (skip_count col 0)); try easy.
         rewrite <- (col_add_many_0 A (make_row_val v (skip_count col 0) C0) col).
         rewrite (row_add_each_row_add _ _ col (skip_count col 0)); try easy.
         rewrite <- (row_add_each_0 B (make_row_val v (skip_count col 0) C0) col).
         apply add_preserves_mul; try easy.
         apply mat_equiv_eq; auto with wf_db.
         unfold mat_equiv; intros. 
         destruct j; try lia. 
         unfold make_row_val.
         bdestruct (i =? skip_count col 0); try lia; try easy. 
         destruct col; destruct i; try easy.
         rewrite H2; try easy. unfold skip_count in *. 
         bdestruct (0 <? 0); lia. 
         rewrite H2; try easy.
         unfold skip_count in *. simpl; lia. 
         all : try apply skip_count_not_skip.
         intros. destruct y; try easy.
         apply H; lia. 
         unfold mat_equiv, make_row_val; intros. 
         destruct j; try lia. 
         bdestruct (i =? skip_count col 0); try lia; try easy. 
         destruct col; try easy.
         destruct i; try easy.
         rewrite H2; try easy. 
         unfold skip_count in *; simpl in *; lia. 
         rewrite H2; try easy.
         unfold skip_count in *; simpl in *; lia. 
       - intros. 
         destruct n; try easy.
         rewrite (col_add_many_col_add _ _ col (skip_count col (S e))); try easy.
         rewrite (row_add_each_row_add _ _ col (skip_count col (S e))); try easy.
         rewrite add_preserves_mul; try easy.
         rewrite cam_ca_switch. 
         rewrite IHe; try easy; auto with wf_db.
         assert (p : e < S e). lia. 
         apply (skip_count_mono col) in p.
         lia. 
         intros.
         unfold make_row_val.
         bdestruct (i =? skip_count col (S e)); try easy. 
         unfold skip_count in *. 
         bdestruct (e <? col); bdestruct (S e <? col); try lia. 
         all : try (apply H2; lia). 
         bdestruct (i =? col); bdestruct (S e =? col); try lia. 
         rewrite H8; apply H3.
         apply H2. lia. 
         unfold make_row_val.
         bdestruct (col =? skip_count col (S e)); try easy.
         unfold make_row_val.
         bdestruct (col =? skip_count col (S e)); try easy.
         assert (H4 := skip_count_not_skip). auto.
         all : try apply skip_count_not_skip.
         intros. 
         destruct y; try easy.
         apply H; lia. 
Qed.

Lemma col_add_many_preserves_mul: forall (m n o col : nat) 
                                               (A : Matrix m n) (B : Matrix n o) (v : Vector n),
  WF_Matrix v -> col < n -> v col 0 = C0 ->
  A × (row_add_each B v col) = (col_add_many A v col) × B.  
Proof. intros. 
       destruct n; try easy.
       destruct n.
       - assert (H' : v = Zero).
         apply mat_equiv_eq; auto with wf_db.
         unfold mat_equiv; intros. 
         destruct i; destruct j; destruct col; try lia; easy.
         rewrite <- col_add_many_0, <- row_add_each_0; try easy.
         rewrite H'; easy.
       - apply (col_add_many_preserves_mul_some _ _ _ n col); try easy.
         unfold skip_count.
         bdestruct (n <? col); lia. 
         intros. 
         unfold skip_count in H2.
         bdestruct (n <? col). 
         bdestruct (col =? (S n)); try lia. 
         bdestruct (i =? (S n)). 
         rewrite H5, <- H4. apply H1.
         apply H; lia. 
         apply H; lia. 
Qed.

(* we can prove col_add_each version much more easily using transpose *)
Lemma col_add_each_preserves_mul: forall (m n o col : nat) (A : Matrix m n) 
                                                         (B : Matrix n o) (v : Matrix 1 n),
  WF_Matrix v -> col < n -> v 0 col = C0 ->
  A × (row_add_many B v col) = (col_add_each A v col) × B.  
Proof. intros. 
       assert (H' : ((B⊤) × (row_add_each (A⊤) (v⊤) col))⊤ = 
                               ((col_add_many (B⊤) (v⊤) col) × (A⊤))⊤).  
       rewrite col_add_many_preserves_mul; auto with wf_db; try easy.
       do 2 rewrite Mmult_transpose in H'; auto.
       rewrite row_add_each_transpose in H'. 
       rewrite col_add_many_transpose in H'. 
       repeat rewrite transpose_involutive in H'.
       easy. 
Qed.




(** proving lemmas about (I n) *)


(* first, facts about the ops on (I n) *)
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
       bdestruct_all; try easy; simpl; ring.
Qed.

Lemma col_row_scale_many_invr_I : forall (n : nat) (as' : Matrix 1 n), 
  col_scale_many (I n) as' = row_scale_many (I n) (as'⊤).
Proof. intros. 
       prep_matrix_equality.
       unfold col_scale_many, row_scale_many, transpose, I.
       bdestruct_all; try easy; simpl; subst; ring.
Qed.


Lemma col_row_add_invr_I : forall (n x y : nat) (c : C), 
  x < n -> y < n -> col_add (I n) x y c = row_add (I n) y x c.
Proof. intros. 
       prep_matrix_equality.
       unfold col_add, row_add, I.
       bdestruct_all; try easy; simpl; ring.
Qed.

Lemma row_each_col_many_invr_I : forall (n col : nat) (v : Vector n),
  WF_Matrix v -> col < n -> v col 0 = C0 ->
  row_add_each (I n) v col = col_add_many (I n) v col.  
Proof. intros. 
       rewrite <- (Mmult_1_r), <- col_add_many_preserves_mul, 
         Mmult_1_l; auto with wf_db. 
Qed.

Lemma row_many_col_each_invr_I : forall (n col : nat) (v : Matrix 1 n),
  WF_Matrix v -> col < n -> v 0 col = C0 ->
  row_add_many (I n) v col = col_add_each (I n) v col.  
Proof. intros. 
       rewrite <- (Mmult_1_r), <- col_add_each_preserves_mul, 
         Mmult_1_l; auto with wf_db. 
Qed.


(* Now to the column/row operations matrices!! *)
Lemma col_swap_mult_r : forall {m n} (A : Matrix m n) (x y : nat),
  x < n -> y < n -> WF_Matrix A -> 
  col_swap A x y = A × (row_swap (I n) x y).
Proof. intros.
       assert (H2 := (swap_preserves_mul A (row_swap (I n) x y) x y)). 
       rewrite <- (Mmult_1_r _ _ (col_swap A x y)); auto with wf_db.
       rewrite H2; try easy.
       rewrite <- (row_swap_inv (I n) x y).
       reflexivity. 
Qed.

Lemma row_swap_mult_l : forall {m n} (A : Matrix m n) (x y : nat),
  x < m -> y < m -> WF_Matrix A -> 
  row_swap A x y = (col_swap (I m) x y) × A.
Proof. intros.
       assert (H2 := (swap_preserves_mul (row_swap (I m) x y) A x y)). 
       rewrite <- (Mmult_1_l _ _ (row_swap A x y)); auto with wf_db.
       rewrite col_row_swap_invr_I; auto.
       rewrite H2; try easy.
       rewrite <- col_row_swap_invr_I; auto.
       rewrite <- (col_swap_inv (I m) x y).
       reflexivity. 
Qed.

Lemma col_scale_mult_r : forall {m n} (A : Matrix m n) (x : nat) (a : C),
  WF_Matrix A -> 
  col_scale A x a = A × (row_scale (I n) x a).
Proof. intros. 
       rewrite scale_preserves_mul.
       rewrite Mmult_1_r; auto with wf_db. 
Qed.

Lemma col_scale_many_mult_r : forall {m n} (A : Matrix m n) (as' : Matrix 1 n),
  WF_Matrix A -> 
  col_scale_many A as' = A × (row_scale_many (I n) (as'⊤)).
Proof. intros. 
       rewrite scale_many_preserves_mul.
       rewrite Mmult_1_r; auto with wf_db. 
Qed.


Lemma col_add_mult_r : forall {m n} (A : Matrix m n) (x y : nat) (a : C),
  x < n -> y < n -> WF_Matrix A -> 
  col_add A x y a = A × (row_add (I n) y x a).
Proof. intros. 
       rewrite add_preserves_mul; auto.
       rewrite Mmult_1_r; auto with wf_db. 
Qed.

Lemma col_add_many_mult_r : forall {m n} (A : Matrix m n) (v : Vector n) (col : nat),
  WF_Matrix A -> WF_Matrix v -> col < n -> v col 0 = C0 ->
  col_add_many A v col = A × (row_add_each (I n) v col).
Proof. intros. 
       rewrite col_add_many_preserves_mul; try easy.
       rewrite Mmult_1_r; auto with wf_db.
Qed.

Lemma col_add_each_mult_r : forall {m n} (A : Matrix m n) (v : Matrix 1 n) (col : nat),
  WF_Matrix A -> WF_Matrix v -> col < n -> v 0 col = C0 ->
  col_add_each A v col = A × (row_add_many (I n) v col).
Proof. intros. 
       rewrite col_add_each_preserves_mul; try easy.
       rewrite Mmult_1_r; auto with wf_db.
Qed.





(** * lemmas about e_i *)


Lemma I_is_eis : forall {n} (i : nat),
  get_col (I n) i = e_i i. 
Proof. intros. 
       unfold get_col, e_i, I.
       prep_matrix_equality. 
       bdestruct_all; simpl; auto.
Qed. 


Lemma get_minor_diag_mul : forall {n} (A : Square (S n)) (v : Vector (S n)) (i : nat),
  i < S n ->
  get_col A i = e_i i -> 
  (get_minor A i i) × (reduce_row v i) = reduce_row (A × v) i.
Proof. intros.
       prep_matrix_equality.
       unfold get_minor, reduce_row, Mmult.
       replace n with (i + (n - i)) by lia.
       replace (S (i + (n - i))) with (i + 1 + (n - i)) by lia.
       do 5 rewrite big_sum_sum; simpl.
       bdestruct (x <? i).
       - rewrite <- get_col_conv, Nat.add_0_r, H0.
         unfold e_i; bdestruct_all; simpl.
         rewrite Cmult_0_l, 2 Cplus_0_r.
         apply f_equal_gen; try apply f_equal.
         all : apply big_sum_eq_bounded; intros.
         all : bdestruct_all; auto.
         repeat (apply f_equal_gen; try lia); easy.
       - rewrite <- get_col_conv, Nat.add_0_r, H0.
         unfold e_i; bdestruct_all; simpl.
         all : rewrite Cmult_0_l, 2 Cplus_0_r.
         all : apply f_equal_gen; try apply f_equal.
         all : apply big_sum_eq_bounded; intros.
         all : bdestruct_all; auto.
         all : repeat (apply f_equal_gen; try lia); easy.
Qed.


(* similar lemma for wedge *) 
Lemma wedge_mul : forall {m n} (A : Matrix m n) (v : Vector m) (a : Vector n) (i : nat),
  i <= n ->
  (col_wedge A v i) × (row_wedge a Zero i) = A × a.
Proof. intros. 
       prep_matrix_equality. 
       unfold Mmult.
       replace n with (i + (n - i)) by lia. 
       replace (S (i + (n - i))) with (i + 1 + (n - i)) by lia.
       do 3 rewrite big_sum_sum; simpl.
       unfold row_wedge, col_wedge, Zero.
       bdestruct (i + 0 <? i); bdestruct (i + 0 =? i); try lia.
       rewrite Cmult_0_r, 2 Cplus_0_r.
       apply f_equal_gen; try apply f_equal.
       all : apply big_sum_eq_bounded; intros.
       all : bdestruct_all; auto.
       repeat (apply f_equal_gen; try lia); easy.
Qed.

Lemma matrix_by_basis : forall {m n} (T : Matrix m n) (i : nat),
  i < n -> 
  get_col T i = T × e_i i.
Proof. intros. 
       unfold get_col, e_i, Mmult.
       prep_matrix_equality.
       bdestruct (y =? 0). 
       - rewrite (big_sum_unique (T x i) _ n); try easy.
         exists i. split.
         apply H. split.
         bdestruct (i =? i); bdestruct (i <? n); try lia; simpl; ring. 
         intros.
         bdestruct (x' =? i); try lia; simpl; ring. 
       - rewrite big_sum_0; try reflexivity.
         intros. rewrite andb_false_r. 
         lca.
Qed.    

Lemma matrix_by_basis_adjoint : forall {m n} (T : Matrix m n) (i : nat),
  i < m -> 
  get_row T i = (e_i i)† × T.
Proof. intros. 
       unfold get_row, e_i, Mmult, adjoint.
       prep_matrix_equality.
       bdestruct (x =? 0). 
       - rewrite (big_sum_unique (T i y) _ m); try easy.
         exists i. split.
         apply H. split.
         bdestruct (i =? i); bdestruct (i <? m); try lia; simpl; lca.  
         intros.
         bdestruct (x' =? i); try lia; simpl; lca. 
       - rewrite big_sum_0; try reflexivity.
         intros. rewrite andb_false_r. 
         lca.
Qed.    

Lemma get_entry_with_e_i : forall {m n} (T : Matrix m n) (i j : nat),
  i < m -> j < n ->
  T i j = ((e_i i)† × T × (e_i j)) O O.
Proof. intros.
       rewrite <- matrix_by_basis_adjoint, <- matrix_by_basis; auto.
Qed.

Lemma mat_equiv_of_equiv_on_ei : forall {n m} (A B : Matrix n m),
  (forall k, (k < m)%nat -> A × e_i k ≡ B × e_i k) ->
  A ≡ B.
Proof.
  intros n m A B Heq.
  intros i j Hi Hj.
  specialize (Heq j Hj).
  rewrite <- 2!(matrix_by_basis _ _ Hj) in Heq.
  specialize (Heq i O Hi ltac:(lia)).
  unfold get_col in Heq.
  rewrite Nat.eqb_refl in Heq.
  easy.
Qed.

Lemma eq_of_eq_on_ei : forall {n m} (A B : Matrix n m),
  WF_Matrix A -> WF_Matrix B ->
  (forall k, (k < m)%nat -> A × e_i k = B × e_i k) ->
  A = B.
Proof.
  intros n m A B HA HB HAB.
  apply mat_equiv_eq; [easy..|].
  apply mat_equiv_of_equiv_on_ei.
  intros k Hk.
  now rewrite HAB by easy.
Qed.


(** * Lemmas related to 1pad *)


Lemma pad1_conv : forall {m n} (T : Matrix m n) (c : C) (i j : nat),
  (pad1 T c) (S i) (S j) = T i j.
Proof. intros.
       unfold pad1, col_wedge, row_wedge, e_i.
       bdestruct (S j <? 0); bdestruct (S j =? 0); try lia.
       bdestruct (S i <? 0); bdestruct (S i =? 0); try lia.
       do 2 rewrite Sn_minus_1.
       easy.
Qed.

Lemma pad1_scale : forall {m n : nat} (T : Matrix m n) (c c0 : C),
  c0 .* pad1 T c = pad1 (c0 .* T) (c0 * c). 
Proof. intros. 
       unfold pad1, scale, col_wedge, row_wedge, e_i, Zero.
       prep_matrix_equality. 
       bdestruct_all; simpl; ring.
Qed.

Lemma pad1_mult : forall {m n o : nat} (T1 : Matrix m n) (T2 : Matrix n o) (c1 c2 : C),
  pad1 (T1 × T2) (c1 * c2) = (pad1 T1 c1) × (pad1 T2 c2).
Proof. intros. 
       prep_matrix_equality. 
       unfold Mmult. 
       destruct x. 
       - unfold pad1, col_wedge, row_wedge, e_i, scale.
         bdestruct_all. 
         rewrite <- big_sum_extend_l; simpl. 
         rewrite <- (Cplus_0_r (c1 * c2 * C1)).
         apply f_equal_gen; try apply f_equal; try ring.
         rewrite big_sum_0_bounded; try easy.
         intros; lca. 
         rewrite big_sum_0_bounded; try easy.
         simpl; intros. 
         bdestruct_all; unfold Zero; simpl; ring.
       - destruct y.
         unfold pad1, col_wedge, row_wedge, e_i, scale. 
         simpl. 
         rewrite big_sum_0_bounded; try ring.   
         bdestruct_all; simpl; ring. 
         intros. 
         bdestruct_all; simpl; ring.  
         rewrite pad1_conv.
         rewrite <- big_sum_extend_l.
         rewrite <- (Cplus_0_l (big_sum _ _)). 
         apply f_equal_gen; try apply f_equal; try easy.
         unfold pad1, col_wedge, row_wedge, e_i, scale. 
         bdestruct_all; simpl; ring.   
         apply big_sum_eq_bounded; intros. 
         do 2 rewrite pad1_conv; easy.
Qed.

Lemma pad1_adjoint : forall {m n} (T : Matrix m n) (c : C),
  (pad1 T c) † = pad1 (T†) (c^*).
Proof. intros. 
       prep_matrix_equality.
       unfold pad1, adjoint, col_wedge, row_wedge, scale, e_i, Zero.
       bdestruct_all; subst; simpl; try lca.
Qed.

Lemma pad1_row_wedge_mult : forall {m n} (T : Matrix m n) (v : Vector n) (c : C),
  pad1 T c × row_wedge v Zero 0 = row_wedge (T × v) Zero 0.
Proof. intros. 
       prep_matrix_equality.
       destruct x.
       - unfold pad1, Mmult, col_wedge, row_wedge, scale, e_i, Zero.
         bdestruct_all;
         rewrite big_sum_0_bounded; try ring; intros;
         bdestruct_all; simpl; ring. 
       - destruct y;
         unfold pad1, Mmult, col_wedge, row_wedge, scale, e_i, Zero;
         bdestruct_all;
         rewrite <- big_sum_extend_l, <- Cplus_0_l;
         apply f_equal_gen; try apply f_equal; simpl; try ring;
         apply big_sum_eq_bounded; intros;
         bdestruct_all; do 2 rewrite Nat.sub_0_r; easy. 
Qed.

Lemma pad1_I : forall (n : nat), pad1 (I n) C1 = I (S n).
Proof. intros.  
       prep_matrix_equality. 
       destruct x; destruct y; try easy.
       3 : rewrite pad1_conv.
       all : try unfold pad1; unfold I, col_wedge, row_wedge, e_i, scale. 
       all : try (simpl; ring).
       bdestruct_all; simpl; ring.
Qed.

Lemma reduce_colrow_pad1 : forall {m n} (T : Matrix m n) (c : C),
  T = reduce_col (reduce_row (pad1 T c) 0) 0. 
Proof. intros. 
       prep_matrix_equality.
       unfold reduce_col, reduce_row, pad1, col_wedge, row_wedge, e_i, Zero. 
       bdestruct_all.
       destruct x; destruct y; easy.  
Qed.

Lemma get_minor_pad1 : forall {m n : nat} (A : Matrix m n) (c : C),
  A = get_minor (pad1 A c) 0 0.
Proof. intros. 
       rewrite get_minor_is_redrow_redcol.
       rewrite <- reduce_colrow_pad1.
       easy.
Qed.

Lemma pad1_reduce_colrow : forall {m n} (T : Matrix (S m) (S n)),
  (forall (i j : nat), (i = 0 \/ j = 0) /\ i <> j -> T i j = C0) ->
  T = pad1 (reduce_col (reduce_row T 0) 0) (T 0 0).
Proof. intros. 
       prep_matrix_equality.
       destruct x; destruct y.
       4 : rewrite pad1_conv.
       all : try unfold pad1; unfold col_wedge, row_wedge, e_i, scale; simpl.
       ring.
       rewrite H; auto.
       rewrite H; auto; ring.
       unfold reduce_col, reduce_row.
       bdestruct_all; easy.
Qed.

Lemma pad1_get_minor: forall {n : nat} (A : Square (S n)) (c : C),
  (forall (i j : nat), (i = 0 \/ j = 0) /\ i <> j -> A i j = C0) ->
  A = pad1 (get_minor A O O) (A 0 0).
Proof. intros. 
       rewrite get_minor_is_redrow_redcol.
       rewrite <- pad1_reduce_colrow;
       easy.
Qed.

(* ∃ weakens this lemma, but makes future proofs less messy *)
Lemma pad1ed_matrix : forall {m n} (A : Matrix (S m) (S n)) (c : C),
  (forall (i j : nat), (i = 0 \/ j = 0) /\ i <> j -> A i j = C0) -> A 0 0 = c ->
  exists a, pad1 a c = A.
Proof. intros.
       exists (reduce_col (reduce_row A 0) 0); subst.
       rewrite <- pad1_reduce_colrow; auto.
Qed.


Lemma pad1_col_swap : forall {m n} (A : Matrix m n) (x y : nat) (c : C),
  (pad1 (col_swap A x y) c) = col_swap (pad1 A c) (S x) (S y).
Proof. intros. 
       unfold pad1, col_wedge, row_wedge, col_swap, e_i, scale. 
       prep_matrix_equality; simpl. 
       bdestruct_all; try easy. 
       all : rewrite Nat.sub_0_r; easy.
Qed.

Lemma pad1_col_scale : forall {m n} (A : Matrix m n) (x : nat) (c1 c2 : C),
  (pad1 (col_scale A x c1) c2) = col_scale (pad1 A c2) (S x) c1.
Proof. intros. 
       unfold pad1, col_wedge, row_wedge, col_scale, e_i, scale. 
       prep_matrix_equality; simpl. 
       bdestruct_all; try easy. 
       unfold Zero; ring.
Qed.

Lemma pad1_col_add : forall {m n} (A : Matrix m n) (x y : nat) (c1 c2 : C),
  (pad1 (col_add A x y c1) c2) = col_add (pad1 A c2) (S x) (S y) c1.
Proof. intros. 
       unfold pad1, col_wedge, row_wedge, col_add, e_i, scale. 
       prep_matrix_equality; simpl.
       bdestruct_all; try easy. 
       all : rewrite Nat.sub_0_r; try easy.
       unfold Zero; ring.  
Qed.



(** * Some more general matrix lemmas with these new concepts *)

(* We can now show that matrix_equivalence is decidable *)
Lemma vec_equiv_dec : forall {n : nat} (A B : Vector n), 
    { A == B } + { ~ (A == B) }.
Proof. induction n as [| n'].
       - left; easy.
       - intros. destruct (IHn' (reduce_vecn A) (reduce_vecn B)).
         + destruct (Geq_dec (A n' 0) (B n' 0)).
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

Lemma mat_equiv_dec : forall {m n} (A B : Matrix m n), 
    { A == B } + { ~ (A == B) }.
Proof. induction n as [| n']. intros.  
       - left. easy.
       - intros. destruct (IHn' (reduce_col A n') (reduce_col B n')).
         + destruct (vec_equiv_dec (get_col A n') (get_col B n')).
           * left. 
             unfold mat_equiv in *.
             intros. 
             bdestruct (j =? n'); bdestruct (n' <? j); try lia.
             ++ apply (m1 i 0) in H.
                do 2 rewrite get_col_conv in H.
                rewrite H1. easy. lia. 
             ++ apply (m0 i j) in H.
                unfold reduce_col in H.
                bdestruct (j <? n'); try lia; try easy.
                lia. 
           * right. 
             unfold not, mat_equiv in *.
             intros. apply n.
             intros. 
             destruct j; try easy.
             do 2 rewrite get_col_conv.
             apply H; lia.
         + right. 
           unfold not, mat_equiv, reduce_col in *.
           intros. apply n. 
           intros. 
           bdestruct (j <? n'); try lia.
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

(* this is now outdated due to get_nonzero_entry_correct below *)
Lemma nonzero_vec_nonzero_elem : forall {n} (v : Vector n),
  WF_Matrix v -> 
  v <> Zero -> exists x, v x 0 <> C0.
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
         destruct (Geq_dec (v n' 0) C0). 
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


(* this function gets the x from above explicitly *)
Fixpoint get_nonzero_entry (n : nat) (v : Vector (S n)) : nat :=
  match n with 
  | O => O
  | S n' => match (Ceq_dec (v O O) C0) with
           | left _ => 1 + (get_nonzero_entry n' (reduce_row v O))
           | right _ => O
           end
  end.

Arguments get_nonzero_entry {n}.


Lemma get_nonzero_entry_bounds : forall {n} (v : Vector (S n)),
  WF_Matrix v -> 
  get_nonzero_entry v < (S n).  
Proof. induction n. 
       - intros; simpl; auto. 
       - intros; simpl.
         destruct (Ceq_dec (v 0 0) C0); try lia.
         apply -> Nat.succ_lt_mono.
         apply IHn; auto with wf_db.
Qed.

Lemma get_nonzero_entry_correct : forall {n} (v : Vector (S n)),
  WF_Matrix v -> 
  v <> Zero ->
  v (get_nonzero_entry v) 0 <> C0.
Proof. induction n; intros.  
       - destruct (Ceq_dec (v O O) C0).
         + assert (H' : v = Zero).
           { apply mat_equiv_eq; auto with wf_db.
             unfold mat_equiv; intros.
             destruct i; destruct j; try lia.
             rewrite e; easy. }
           easy.
         + unfold get_nonzero_entry; auto.
       - unfold get_nonzero_entry. 
         destruct (Ceq_dec (v O O) C0).
         + unfold not; intros; apply (IHn (reduce_row v 0)); auto with wf_db.
           contradict H0.
           apply <- (zero_reduce v O); auto.
         + auto. 
Qed.       


Lemma get_nonzero_entry_correct_row : forall {n} (v : Matrix 1 (S n)),
  WF_Matrix v -> 
  v <> Zero ->
  v 0 (get_nonzero_entry v⊤) <> C0.
Proof. intros.
       unfold not; intros; apply (get_nonzero_entry_correct v⊤); auto with wf_db.
       unfold not; intros; apply H0.
       apply (f_equal transpose) in H2.
       rewrite transpose_involutive in H2.
       rewrite H2. 
       prep_matrix_equality.
       unfold Zero, transpose; easy.
Qed.


(***********************************************************)
(** * Defining and proving lemmas relating to the determinant *)
(***********************************************************)


Fixpoint parity (n : nat) : C := 
  match n with 
  | 0 => C1
  | S 0 => -C1
  | S (S n) => parity n
  end. 


Lemma parity_S : forall (n : nat),
  (parity (S n) = -C1 * parity n)%C. 
Proof. intros.
       induction n as [| n']; try (simpl; ring).
       rewrite IHn'.
       simpl. 
       ring.
Qed.

Lemma parity_sqr : forall (n : nat),
  (parity n * parity n)%C = C1.
Proof. intros. 
       induction n.
       - simpl; ring.
       - rewrite parity_S.
         replace (- (C1) * parity n * (- (C1) * parity n))%C with (parity n * parity n)%C by ring.
         easy.
Qed.

Lemma parity_plus : forall (n m : nat),
  parity (n + m) = (parity n * parity m)%C.
Proof. intros. 
       induction n.
       - simpl; ring.
       - rewrite plus_Sn_m, parity_S, parity_S, IHn. 
         ring. 
Qed.



Fixpoint Determinant (n : nat) (A : Square n) : C :=
  match n with 
  | 0 => C1
  | S 0 => A 0 0
  | S n' => (big_sum (fun i => (parity i) * (A i 0) * 
                                 (Determinant n' (get_minor A i 0)))%C n)
  end.

Arguments Determinant {n}.

Lemma Det_simplify : forall {n} (A : Square (S n)),
  Determinant A =  
  (big_sum (fun i => (parity i) * (A i 0) * (Determinant (get_minor A i 0)))%C (S n)).
Proof. intros. 
       destruct n; try easy.
       simpl; ring.
Qed.

Lemma Det_simplify_fun : forall {n} (A : Square (S (S n))),
  (fun i : nat => parity i * A i 0 * Determinant (get_minor A i 0))%C =
  (fun i : nat => (big_sum (fun j => 
           (parity i) * (A i 0) * (parity j) * ((get_minor A i 0) j 0) * 
           (Determinant (get_minor (get_minor A i 0) j 0)))%C (S n)))%C.
Proof. intros. 
       apply functional_extensionality; intros. 
       rewrite Det_simplify. 
       rewrite (@big_sum_mult_l C _ _ _ C_is_ring). 
       apply big_sum_eq_bounded; intros. 
       lca.
Qed.


Lemma get_minor_I : forall (n : nat), get_minor (I (S n)) 0 0 = I n.
Proof. intros.
       apply mat_equiv_eq.
       apply WF_get_minor; try lia; auto with wf_db.
       apply WF_I.
       unfold mat_equiv; intros.
       unfold get_minor, I.
       bdestruct (i <? 0); bdestruct (j <? 0); try lia. 
       easy. 
Qed.       

Lemma Det_I : forall (n : nat), Determinant (I n) = C1.
Proof. intros.
       induction n as [| n'].
       - easy.
       - simpl. destruct n'; try easy.
         rewrite <- big_sum_extend_l.
         rewrite <- Cplus_0_r.
         rewrite <- Cplus_assoc.
         apply Cplus_simplify.
         rewrite get_minor_I, IHn'.
         lca.
         rewrite (@big_sum_extend_r C C_is_monoid).
         apply (@big_sum_0_bounded C C_is_monoid); intros.
         replace (I (S (S n')) (S x) 0) with C0 by easy.
         lca. 
Qed.

Lemma Det_make_WF : forall (n : nat) (A : Square n),
  Determinant A = Determinant (make_WF A).
Proof. induction n as [| n'].  
       - easy. 
       - intros. 
         destruct n'; try easy. 
         do 2 rewrite Det_simplify. 
         apply big_sum_eq_bounded; intros. 
         assert (H' : (get_minor (make_WF A) x 0) = make_WF (get_minor A x 0)).
         { prep_matrix_equality.
           unfold get_minor, make_WF.
           bdestruct_all; try easy. }
         rewrite H', IHn'.
         unfold make_WF. 
         bdestruct_all; easy. 
Qed.

Lemma Det_Mmult_make_WF_l : forall (n : nat) (A B : Square n),
  Determinant (A × B) = Determinant (make_WF A × B).
Proof. intros. 
       rewrite Det_make_WF, (Det_make_WF _ (make_WF A × B)).
       do 2 rewrite <- Mmult_make_WF.
       rewrite <- (eq_make_WF (make_WF A)); auto with wf_db.
Qed.

Lemma Det_Mmult_make_WF_r : forall (n : nat) (A B : Square n),
  Determinant (A × B) = Determinant (A × (make_WF B)).
Proof. intros. 
       rewrite Det_make_WF, (Det_make_WF _ (A × make_WF B)).
       do 2 rewrite <- Mmult_make_WF.
       rewrite <- (eq_make_WF (make_WF B)); auto with wf_db.
Qed.

Lemma Det_Mmult_make_WF : forall (n : nat) (A B : Square n),
  Determinant (A × B) = Determinant ((make_WF A) × (make_WF B)).
Proof. intros. 
       rewrite <- Det_Mmult_make_WF_r, <- Det_Mmult_make_WF_l; easy. 
Qed.

Local Open Scope C_scope.

Definition M22 : Square 2 :=
  fun x y => 
  match (x, y) with
  | (0, 0) => C1
  | (0, 1) => (C1+C1)%C
  | (1, 0) => (C1+C1+C1+C1)%C
  | (1, 1) => (C1+C1+C1+C1+C1)%C
  | _ => C0
  end.


Lemma Det_M22 : (Determinant M22) = (Copp (C1 + C1 + C1))%C.
Proof. simpl; unfold M22, get_minor; simpl.
       ring.
Qed.


(** Now, we show the effects of the column operations on determinant *)

Lemma Determinant_col_scale : forall {n} (A : Square n) (c : C) (col : nat),
  col < n -> Determinant (col_scale A col c) = (c * Determinant A)%C.
Proof. induction n.
       + intros. easy.
       + intros. simpl.  
         destruct n. 
         - simpl. unfold col_scale. 
           bdestruct (0 =? col); try lia; easy.
         - rewrite Cmult_plus_distr_l.
           apply Cplus_simplify.
           * rewrite (@big_sum_mult_l C _ _ _ C_is_ring).
             apply big_sum_eq_bounded.
             intros. 
             destruct col. 
             rewrite col_scale_get_minor_same; try lia. 
             unfold col_scale. bdestruct (0 =? 0); try lia. 
             lca. 
             rewrite col_scale_get_minor_before; try lia.
             rewrite Sn_minus_1.
             rewrite IHn; try lia. 
             unfold col_scale. 
             bdestruct (0 =? S col); try lia; lca.
           * destruct col. 
             rewrite col_scale_get_minor_same; try lia. 
             unfold col_scale. bdestruct (0 =? 0); try lia. 
             lca. 
             rewrite col_scale_get_minor_before; try lia.
             rewrite Sn_minus_1.
             rewrite IHn; try lia. 
             unfold col_scale. 
             bdestruct (0 =? S col); try lia; lca. 
Qed.

Lemma Determinant_row_scale : forall {n} (A : Square n) (c : C) (row : nat),
  row < n -> Determinant (row_scale A row c) = (c * Determinant A)%C.
Proof. induction n.
       - intros. easy.
       - intros. 
         do 2 rewrite Det_simplify.
         rewrite (@big_sum_mult_l C _ _ _ C_is_ring).
         apply big_sum_eq_bounded; intros.
         bdestruct (x <? row); bdestruct (x =? row); bdestruct (row <? x); try lia. 
         + rewrite row_scale_get_minor_before; auto.
           rewrite IHn; try lia. 
           unfold row_scale.
           bdestruct_all; lca.
         + rewrite row_scale_get_minor_same; auto.
           unfold row_scale.
           bdestruct_all; lca.
         + rewrite row_scale_get_minor_after; auto.
           rewrite IHn; try lia. 
           unfold row_scale.
           bdestruct_all; lca.
Qed.

Lemma Determinant_scalar : forall {n} (A : Square n) (c : C),
  Determinant (c .* A) = (c^n * Determinant A)%C.
Proof. induction n.
       - intros; simpl; ring.
       - intros. 
         do 2 rewrite Det_simplify.
         rewrite (@big_sum_mult_l C _ _ _ C_is_ring).
         apply big_sum_eq_bounded; intros. 
         replace (get_minor (c .* A) x 0) with (c .* (get_minor A x 0)).
         rewrite IHn; auto.
         unfold scale; simpl.  
         ring.
         unfold get_minor, scale.
         prep_matrix_equality.
         bdestruct_all; easy.
Qed.




(* some helper lemmas, since showing the effect of col_swap is a bit tricky *)
Lemma Det_diff_1 : forall {n} (A : Square (S (S n))),
  Determinant (col_swap A O 1) = 
  big_sum (fun i => (big_sum (fun j => ((A i 1) * (A (skip_count i j) O) * (parity i) * (parity j) * 
                             Determinant (get_minor (get_minor A i O) j O))%C )  
                             (S n))) (S (S n)).
Proof. intros. 
       rewrite Det_simplify.
       rewrite Det_simplify_fun.
       apply big_sum_eq_bounded; intros. 
       apply big_sum_eq_bounded; intros. 
       replace (col_swap A O 1%nat x O) with (A x 1%nat) by easy. 
       assert (H' : @get_minor (S n) (S n) (col_swap A O 1%nat) x O x0 O = A (skip_count x x0) O).
       { unfold get_minor, col_swap, skip_count. 
         simpl. bdestruct (x0 <? x)%nat; try easy. } 
       rewrite H'.    
       apply f_equal_gen; try apply f_equal; try easy. 
       ring.
Qed.

Lemma Det_diff_2 : forall {n} (A : Square (S (S n))),
  Determinant A = 
  big_sum (fun i => (big_sum (fun j => ((A i 0) * (A (skip_count i j) 1) * (parity i) * (parity j) * 
                             Determinant (get_minor (get_minor A i 0) j 0))%C)  
                             (S n))) (S (S n)).
Proof. intros. 
       rewrite Det_simplify.
       rewrite Det_simplify_fun.
       apply big_sum_eq_bounded; intros. 
       apply big_sum_eq_bounded; intros. 
       apply f_equal_gen; try apply f_equal; try easy. 
       assert (H' : @get_minor (S n) (S n) A x 0 x0 0 = A (skip_count x x0) 1%nat).
       { unfold get_minor, col_swap, skip_count. 
         simpl. bdestruct (x0 <? x); try easy. } 
       rewrite H'. 
       ring.
Qed.
  
(* if we show that swapping 0th col and 1st col, we can generalize using some cleverness *)
Lemma Determinant_swap_01 : forall {n} (A : Square n),
  1 < n -> Determinant (col_swap A 0 1) = -C1%C * (Determinant A).
Proof. intros.
       destruct n; try lia.
       destruct n; try lia. 
       rewrite Det_diff_1, Det_diff_2.
       apply big_sum_rearrange; intros.
       - unfold skip_count. 
         bdestruct (x <? (S y)); bdestruct (y <? x); try lia.
         rewrite Cmult_assoc.
         apply f_equal_gen; try apply f_equal. 
         rewrite parity_S.
         lca.  
         rewrite get_minor_2x_0; easy.
       - unfold skip_count. 
         bdestruct (x <? y); bdestruct (y <? (S x)); try lia.
         rewrite Cmult_assoc.
         apply f_equal_gen; try apply f_equal. 
         rewrite parity_S.
         lca.
         rewrite <- get_minor_2x_0; easy.
Qed.

(* swapping adjacent columns *)
Lemma Determinant_swap_adj : forall {n} (A : Square n) (i : nat),
  S i < n -> Determinant (col_swap A i (S i)) = -C1%C * (Determinant A).
Proof. induction n as [| n'].
       - easy.
       - intros. 
         destruct i. 
         + apply Determinant_swap_01; easy.
         + simpl. destruct n'; try lia.
           do 2 rewrite (@big_sum_extend_r C C_is_monoid). 
           rewrite (@big_sum_mult_l C _ _ _ C_is_ring).
           apply big_sum_eq_bounded; intros. 
           rewrite col_swap_get_minor_before; try lia. 
           rewrite IHn'; try lia. 
           replace (col_swap A (S i) (S (S i)) x 0%nat) with (A x 0%nat) by easy.
           lca.
Qed.

(* swapping columns i and i + (S k), use previous lemma to induct *)
Lemma Determinant_swap_ik : forall {n} (k i : nat) (A : Square n),
  i + (S k) < n -> Determinant (col_swap A i (i + (S k))) = -C1%C * (Determinant A).
Proof. induction k as [| k'].
       - intros. 
         replace (i + 1)%nat with (S i) by lia. 
         rewrite Determinant_swap_adj; try lia; ring. 
       - intros. 
         rewrite (col_swap_three A i (i + (S k')) (i + (S (S k')))); try lia. 
         rewrite IHk'; try lia. 
         replace (i + (S (S k')))%nat with (S (i + (S k')))%nat by lia. 
         rewrite Determinant_swap_adj; try lia.
         rewrite IHk'; try lia. 
         ring.
Qed.

(* finally, we can prove Determinant_swap *)
Lemma Determinant_swap : forall {n} (A : Square n) (i j : nat),
  i < n -> j < n -> i <> j ->
  Determinant (col_swap A i j) = -C1%C * (Determinant A).
Proof. intros. 
       bdestruct (i <? j); bdestruct (j <? i); try lia. 
       - replace j with (i + (S (j - i - 1)))%nat by lia. 
         rewrite Determinant_swap_ik; try lia; easy.
       - replace i with (j + (S (i - j - 1)))%nat by lia. 
         rewrite col_swap_diff_order. 
         rewrite Determinant_swap_ik; try lia; easy.
Qed.

Lemma Determinant_col_to_front : forall {n} (col : nat) (A : Square n),
  col < n -> 
  Determinant (col_to_front A col) = (parity col) * Determinant A.
Proof. induction col; intros.
       - rewrite col_to_front_0. 
         simpl; ring.
       - rewrite col_to_front_swap_col; auto.
         rewrite IHcol; try lia.
         rewrite Determinant_swap; try lia.
         rewrite parity_S.
         ring.
Qed.

Lemma col_0_Det_0 : forall {n} (A : Square n) (i : nat),
  i < n -> 
  get_col A i = Zero -> 
  Determinant A = C0.
Proof. intros n A i H H0.
       destruct n; try easy.
       destruct n.
       destruct i; try lia. 
       replace C0 with (@Zero 1 1 0 0)%C by easy.  
       rewrite <- H0. easy. 
       destruct i.
       - rewrite Det_simplify.
         apply (@big_sum_0_bounded C); intros. 
         replace (A x 0) with (@Zero (S (S n)) 1 x 0) by (rewrite <- H0; easy). 
         unfold Zero; lca.
       - rewrite (col_swap_inv _ 0 (S i)).
         rewrite Determinant_swap; try lia.
         rewrite Det_simplify.
         rewrite (@big_sum_mult_l C _ _ _ C_is_ring).
         apply (@big_sum_0_bounded C); intros. 
         replace (col_swap A 0 (S i) x 0) with 
                 (@Zero (S (S n)) 1 x 0) by (rewrite <- H0; easy). 
         unfold Zero; lca.
Qed.

Lemma row_0_Det_0 : forall {n} (A : Square n) (i : nat),
  i < n -> 
  get_row A i = Zero -> 
  Determinant A = C0.
Proof. induction n.
       - intros; try lia.
       - intros; destruct n.
         + simpl.
           destruct i; try lia. 
           rewrite <- get_row_conv, H0; easy.
         + rewrite Det_simplify. 
           rewrite big_sum_0_bounded; auto.
           intros. 
           bdestruct (i =? x); bdestruct (i <? x); bdestruct (x <? i); try lia; subst.
           rewrite <- get_row_conv, H0; unfold Zero; lca.
           rewrite (IHn _ i); try lca; try lia.
           2 : rewrite (IHn _ (i - 1)%nat); try lca; try lia.
           all : unfold get_row, get_minor.
           all : prep_matrix_equality.
           all : bdestruct_all; try easy.
           2 : replace (1 + (i - 1))%nat with i by lia.
           all : rewrite <- get_row_conv, H0; unfold Zero; lca.
Qed.           
           
Lemma col_same_Det_0 : forall {n} (A : Square n) (i j : nat),
  i < n -> j < n -> i <> j -> 
  get_col A i = get_col A j ->
  Determinant A = C0.
Proof. intros. 
       apply eq_neg_implies_0.
       rewrite <- (Determinant_swap _ i j); try easy.
       rewrite (det_by_get_col (col_swap A i j) A); try easy; intros. 
       prep_matrix_equality. 
       destruct y; try easy.
       bdestruct (i0 =? i); bdestruct (i0 =? j); try lia.
       - rewrite H3, col_swap_get_col, H2; easy.
       - rewrite H4, col_swap_diff_order, col_swap_get_col, H2; easy.
       - unfold col_swap, get_col. simpl. 
         bdestruct (i0 =? i); bdestruct (i0 =? j); try lia; easy.
Qed.

Lemma col_scale_same_Det_0 : forall {n} (A : Square n) (i j : nat) (c : C),
  i < n -> j < n -> i <> j -> 
  get_col A i = c .* (get_col A j) ->
  Determinant A = C0.
Proof. intros. 
       destruct (Ceq_dec c C0).
       - apply (col_0_Det_0 _ i); auto.
         rewrite H2, e.
         apply Mscale_0_l.
       - rewrite (col_scale_inv A j c); try easy.
         rewrite Determinant_col_scale; try easy.
         assert (H3 : Determinant (col_scale A j c) = C0).
         { apply (col_same_Det_0 _ i j); try easy.
           prep_matrix_equality.
           unfold get_col, col_scale. 
           bdestruct (y =? 0); try easy.
           bdestruct (i =? j); bdestruct (j =? j); try lia. 
           rewrite <- get_col_conv.
           rewrite H2.
           unfold scale.
           rewrite get_col_conv. 
           easy. }
         rewrite H3.
         lca. 
Qed.


(* use this to show det_col_add_0i *)
Lemma Det_col_add_comm : forall {n} (T : Matrix (S n) n) (v1 v2 : Vector (S n)),
  (Determinant (col_wedge T v1 0) + Determinant (col_wedge T v2 0) = 
   Determinant (col_wedge T (v1 .+ v2) 0)).
Proof. intros. 
       destruct n; try easy.
       do 3 rewrite Det_simplify.
       rewrite <- (@big_sum_plus C _ _ C_is_comm_group).
       apply big_sum_eq_bounded; intros. 
       repeat rewrite get_minor_is_redcol_redrow.
       repeat rewrite col_wedge_reduce_col_same.
       unfold col_wedge, Mplus.
       bdestruct (0 <? 0); bdestruct (0 =? 0); try lia. 
       simpl; ring.
Qed.

(* like before, we prove a specific case in order to prove the general case *)
Lemma Determinant_col_add0i : forall {n} (A : Square n) (i : nat) (c : C),
  i < n -> i <> 0 -> Determinant (col_add A 0 i c) = Determinant A.     
Proof. intros. 
       destruct n; try easy.
       rewrite col_add_split.
       assert (H' := (@Det_col_add_comm n (reduce_col A 0) (get_col A 0) (c .* get_col A i))).
       rewrite <- H'.
       rewrite <- Cplus_0_r.
       apply f_equal_gen; try apply f_equal; auto.
       assert (H1 : col_wedge (reduce_col A 0) (get_col A 0) 0 = A).
       { prep_matrix_equality.
         unfold col_wedge, reduce_col, get_col. 
         destruct y; try easy; simpl. 
         replace (y - 0)%nat with y by lia; easy. }
       rewrite H1; easy.
       apply (col_scale_same_Det_0 _ O i c); try lia; auto.
       prep_matrix_equality. 
       unfold get_col, col_wedge, reduce_col, scale; simpl. 
       bdestruct (y =? 0); bdestruct (i =? 0%nat); try ring; simpl in *; try lia.
       replace (S (i - 1)) with i by lia. 
       easy. 
Qed.

Lemma Determinant_col_add : forall {n} (A : Square n) (i j : nat) (c : C),
  i < n -> j < n -> i <> j -> Determinant (col_add A i j c) = Determinant A.     
Proof. intros. 
       destruct j.
       - rewrite <- col_swap_col_add_0.
         rewrite Determinant_swap. 
         rewrite Determinant_col_add0i.
         rewrite Determinant_swap. 
         ring. 
         all : easy. 
       - destruct i. 
         rewrite Determinant_col_add0i; try easy.
         rewrite <- col_swap_col_add_Si.
         rewrite Determinant_swap. 
         rewrite Determinant_col_add0i.
         rewrite Determinant_swap. 
         ring.
         all : try easy; try lia. 
Qed.

Lemma Determinant_pad1 : forall {n} (A : Square n) (c : C), 
  Determinant (pad1 A c) = c * Determinant A.
Proof. intros.
       rewrite Det_simplify, <- big_sum_extend_l, <- Cplus_0_r.
       apply f_equal_gen; try apply f_equal.
       rewrite <- get_minor_pad1.
       unfold pad1, col_wedge, row_wedge, e_i, scale; simpl; ring.
       apply @big_sum_0_bounded; intros.
       unfold pad1, col_wedge, row_wedge, e_i, scale; simpl; ring.
Qed.


(** Now we prove that A×Adj(A) = det(A) I *)


Lemma determinant_along_col : forall {n} (A : Square (S (S n))) (col rep : nat),
  rep < S (S n) ->
  Determinant (col_replace A col rep) = 
  big_sum (fun i => (A i col) * ((parity i) * (parity rep) *
                    (Determinant (get_minor A i rep))))%C (S (S n)).
Proof. intros. 
       rewrite <- (Cmult_1_l (Determinant (col_replace A col rep))).
       rewrite <- (parity_sqr rep), <- Cmult_assoc.
       rewrite <- Determinant_col_to_front; auto.
       rewrite Det_simplify, (@big_sum_mult_l C _ _ _ C_is_ring).
       apply big_sum_eq_bounded; intros.
       rewrite get_minor_col_to_front, get_minor_col_replace.
       replace (col_to_front (col_replace A col rep) rep x 0) with (A x col).
       lca.
       unfold col_to_front, col_replace; simpl. 
       bdestruct (rep =? rep); easy.
Qed.


Definition adjugate {n} (A : Square n) : Square n :=
  match n with 
  | O => fun i j => C0
  | S n => fun i j => if (i <? (S n)) && (j <? (S n)) 
                      then ((parity (i + j)) * @Determinant n (get_minor A j i))
                      else C0
  end.

            
Lemma WF_adjugate : forall {n} (A : Square n),
  WF_Matrix (adjugate A).
Proof. intros.
       destruct n;
       unfold WF_Matrix, adjugate; intros; auto. 
       bdestruct_all; easy.
Qed.

#[export] Hint Resolve WF_adjugate : wf_db.


Lemma mult_by_adjugate_single_col : forall {n} (A : Square n) (col rep : nat),
  col < n -> rep < n ->
  big_sum (fun y : nat => adjugate A rep y * A y col) n =
  Determinant (col_replace A col rep).
Proof. intros.
       destruct n; try lia.
       destruct n.
       - unfold adjugate, col_replace; destruct rep; destruct col; try lia; simpl.
         ring.
       - rewrite (determinant_along_col _ col rep); auto.
         apply big_sum_eq_bounded; intros.
         unfold adjugate.
         rewrite parity_plus.
         bdestruct_all. 
         simpl; ring.
Qed. 

Theorem mult_by_adjugate_l : forall {n} (A : Square n), 
  WF_Matrix A -> 
  (adjugate A) × A = (Determinant A) .* (I n). 
Proof. intros. 
       destruct n.
       prep_matrix_equality.
       unfold Mmult, scale, I; simpl.
       bdestruct_all; try lia; simpl; lca.
       apply mat_equiv_eq; auto with wf_db.
       unfold mat_equiv; intros.
       unfold Mmult.
       rewrite mult_by_adjugate_single_col; auto.
       unfold scale, I.
       bdestruct (i =? j); subst. 
       - replace (col_replace A j j) with A.         
         bdestruct_all; simpl; ring.
         unfold col_replace.
         prep_matrix_equality.
         bdestruct_all; auto.
       - rewrite (col_scale_same_Det_0 _ i j C1); auto.
         simpl; ring.
         unfold get_col, col_replace, scale.
         prep_matrix_equality.
         bdestruct_all; simpl; ring.
Qed.



(** Developting machinery for one and two level matrices *)  


  


Definition one_level_mat (n : nat) (a : C) (i : nat) : Matrix n n :=
  fun x y => if (x =? i) && (y =? i) then a else 
               if (x =? y) && (x <? n) then C1 else C0.

Definition two_level_mat (n : nat) (U : Matrix 2 2) (i j : nat) : Matrix n n :=
  fun x y => if (x =? i) && (y =? i) then U O O else 
               if (x =? i) && (y =? j) then U O 1%nat else 
                 if (x =? j) && (y =? i) then U 1%nat O else 
                   if (x =? j) && (y =? j) then U 1%nat 1%nat else 
                     if (x =? y) && (x <? n) then C1 else C0.

(* TODO: could generalize this with all the above matric splices *)
Definition get_two_rows {m n} (M : Matrix m n) (i j : nat) : Matrix 2 n :=
  fun x y => if (x =? 0) then M i y else
            if (x =? 1) then M j y else C0.

Lemma WF_one_level_mat : forall n a i, 
  i < n -> WF_Matrix (one_level_mat n a i).
Proof. intros.   
       unfold WF_Matrix, one_level_mat; intros. 
       bdestruct_all; simpl; try lia; easy.
Qed.

Lemma WF_two_level_mat : forall n U i j, 
  i < n -> j < n -> WF_Matrix (two_level_mat n U i j).
Proof. intros.   
       unfold WF_Matrix, two_level_mat; intros. 
       bdestruct_all; simpl; try lia; easy.
Qed.

Lemma WF_get_two_rows : forall {m n} (M : Matrix m n) i j, 
  WF_Matrix M ->
  WF_Matrix (get_two_rows M i j).
Proof. intros.   
       unfold WF_Matrix, get_two_rows; intros. 
       destruct H0;
       bdestruct_all; simpl; auto.
Qed.



(* in what follows, v should be thought as a vector, but I made the proofs more general *)


Lemma mult_by_one_level_mat : forall m n a i (v : Matrix m n),
  i < m -> 
  WF_Matrix v ->
  (one_level_mat m a i) × v = row_scale v i a.
Proof. intros. 
       apply mat_equiv_eq; auto with wf_db.
       apply WF_mult; auto.
       apply WF_one_level_mat; auto.
       unfold mat_equiv; intros. 
       unfold one_level_mat, Mmult, row_scale.
       apply big_sum_unique.
       exists i0; split; auto; split.          
       bdestruct_all; simpl; subst; auto; ring.
       intros. 
       bdestruct_all; simpl; ring.
Qed.         

(* TODO: build better machinery to express these facts *)
Lemma mult_by_two_level_mat_miss : forall m n U i j x y (v : Matrix m n),
  i < m -> j < m ->
  x <> i -> x <> j ->
  WF_Matrix v ->
  ((two_level_mat m U i j) × v) x y = v x y.
Proof. intros.
       unfold two_level_mat, Mmult.      
       bdestruct (x <? m).
       apply big_sum_unique.
       exists x; split; auto; split.          
       bdestruct_all; simpl; subst; auto; ring.
       intros. 
       bdestruct_all; simpl; ring.
       bdestruct_all; simpl.
       rewrite big_sum_0_bounded.
       rewrite H3; auto.
       intros; bdestruct_all; simpl; ring.
Qed.

Lemma mult_by_two_level_mat_row1 : forall m n U i j y (v : Matrix m n),
  i < j -> j < m ->
  WF_Matrix v ->
  ((two_level_mat m U i j) × v) i y = (U × (get_two_rows v i j)) O y.
Proof. intros.
       unfold two_level_mat, Mmult, get_two_rows.     
       simpl.
       apply big_sum_unique2.
       exists i, j; repeat (split; auto).
       bdestruct_all; simpl.
       ring. 
       intros. 
       bdestruct_all; simpl.
       ring.
Qed.

Lemma mult_by_two_level_mat_row2 : forall m n U i j y (v : Matrix m n),
  i < j -> j < m ->
  WF_Matrix v ->
  ((two_level_mat m U i j) × v) j y = (U × (get_two_rows v i j)) 1%nat y.
Proof. intros.
       unfold two_level_mat, Mmult, get_two_rows.     
       simpl.
       apply big_sum_unique2.
       exists i, j; repeat (split; auto).
       bdestruct_all; simpl.
       ring. 
       intros. 
       bdestruct_all; simpl.
       ring.
Qed.

(* combination of previous two lemmas *)
Lemma mult_by_two_level_mat : forall m n U i j (v : Matrix m n),
  i < j -> j < m ->
  WF_Matrix U ->
  WF_Matrix v ->
  get_two_rows ((two_level_mat m U i j) × v) i j = U × (get_two_rows v i j).
Proof. intros. 
       apply mat_equiv_eq.
       apply WF_get_two_rows; apply WF_mult; auto.
       apply WF_two_level_mat; try lia.
       apply WF_mult; auto.
       apply WF_get_two_rows; auto.
       unfold mat_equiv; intros.
       destruct i0.
       rewrite <- mult_by_two_level_mat_row1; try lia; auto.
       destruct i0; try lia. 
       rewrite <- mult_by_two_level_mat_row2; try lia; auto.
Qed.

(* TODO: a lot of repeated code here. How to do more efficiently? *)
Lemma two_level_mat_mult : forall n U1 U2 i j,
  i < j -> j < n ->
  WF_Matrix U1 ->
  WF_Matrix U2 ->
  (two_level_mat n U1 i j) × (two_level_mat n U2 i j) = (two_level_mat n (U1 × U2) i j).
Proof. intros. 
       apply mat_equiv_eq.
       apply WF_mult.
       all : try apply (WF_two_level_mat); auto; try lia.
       unfold mat_equiv; intros.
       unfold two_level_mat, Mmult.
       bdestruct (i0 =? i); bdestruct (i0 =? j); try lia; simpl; subst.
       - bdestruct (j0 =? i); bdestruct (j0 =? j); try lia; simpl; subst.
         + apply big_sum_unique2.
           exists i, j; repeat (split; auto).
           bdestruct_all; simpl; try ring.
           intros. 
           bdestruct_all; simpl; ring.
         + apply big_sum_unique2.
           exists i, j; repeat (split; auto).
           bdestruct_all; simpl; try ring.
           intros. 
           bdestruct_all; simpl; ring.
         + apply big_sum_unique.
           exists j0; repeat (split; auto).
           bdestruct_all; simpl; try ring.
           intros. 
           bdestruct_all; simpl; ring.
       - bdestruct (j0 =? i); bdestruct (j0 =? j); try lia; simpl; subst.
         + apply big_sum_unique2.
           exists i, j; repeat (split; auto).
           bdestruct_all; simpl; try ring.
           intros. 
           bdestruct_all; simpl; ring.
         + apply big_sum_unique2.
           exists i, j; repeat (split; auto).
           bdestruct_all; simpl; try ring.
           intros. 
           bdestruct_all; simpl; ring.
         + apply big_sum_unique.
           exists j0; repeat (split; auto).
           bdestruct_all; simpl; try ring.
           intros. 
           bdestruct_all; simpl; ring.
       - apply big_sum_unique.
         exists i0; repeat (split; auto).
         bdestruct_all; simpl; try ring.
         intros. 
         bdestruct_all; simpl; ring.
Qed.

 



(****)
