Require Export Complex.

Definition Matrix (m n : nat) := nat -> nat -> C.

Definition WF_Matrix {m n: nat} (A : Matrix m n) : Prop := 
  forall x y, x >= m \/ y >= n -> A x y = C0. 

Notation Vector n := (Matrix n 1).

Notation Square n := (Matrix n n).

Inductive indMatrix   : Matrix :=
| i_zero (m : nat) : fun m' n' -> 0
| i_identity (m : nat) : fun m' n' -> if (m' =? n') then C1 else C0
| i_scale (m n sc: nat) (A : Matrix m n) : fun m' n' -> sc * (A m' n')
| i_plus (m n : nat) (A B : Matrix m n) : fun m' n' -> A m' n' + B m' n'
| i_transpose (m n : nat) (A : Matrix m n) : fun m' n' -> A n' m'
| 