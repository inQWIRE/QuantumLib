Require Import String.
Require Import Ascii.
Require Import Reals.
Require Import QASM.
Require Import List.

Import ListNotations.

(* Print function from program to QASM code *)
Definition newline := String (Ascii.ascii_of_N 10) EmptyString.

Fixpoint print_bexp (bx : bexp) : string :=
  match bx with
  | BTrue => "true"
  | BFalse => "false"
  | BI x => x
  | BNot bx' => append "~" (print_bexp bx')
  | BAnd bx1 bx2 => append (print_bexp bx1) (append " ^ " (print_bexp bx2))
  end.

Definition print_binop (b : binop) : string :=
  match b with
  | plus => "+"
  | minus => "-"
  | times => "*"
  | div => "/"
  | pow => "^"
  end.
Definition print_unaryop (u : unaryop) : string :=
  match u with
  | sin => "sin"
  | cos => "cos"
  | tan => "tan"
  | e_to => "exp"
  | ln => "ln"
  | sqrt => "sqrt"
  | neg => "-"
  end.
Fixpoint print_exp (e : exp) : string :=
  match e with
  | e_real r => "(Real number : To implement)" (* To implement *)
  | e_nat n => writeNat n
  | e_pi => "pi"
  | e_id name => name
  | e_binop e1 b e2 => "(" ++ print_exp e1 ++ print_binop b
                             ++ print_exp e2 ++ ")"
  | e_unop u e => "(" ++ print_unaryop u ++ "(" ++ print_exp e ++ "))"
  end.

Definition print_argument (a : argument) : string :=
  match a with
  | a_id n => n
  | a_idx n i => n ++ "[" ++ writeNat i ++ "]"
  end.

Fixpoint print_idlist (args : idlist) : string :=
  match args with
  | [] => ""
  | h :: [] => h
  | h :: t => h ++ "," ++ print_idlist t
  end.
Fixpoint print_explist (exps : explist) : string :=
  match exps with
  | [] => ""
  | h :: [] => print_exp h
  | h :: t => print_exp h ++ "," ++ print_explist t
  end.
Fixpoint print_anylist (args : anylist) : string :=
  match args with
  | [] => ""
  | h :: [] => print_argument h
  | h :: t => print_argument h ++ "," ++ print_anylist t
  end.

Definition print_args (args : option idlist) : string :=
  match args with
  | None => ""
  | Some arglist => print_idlist arglist
  end.

Definition print_uop (op : uop) : string :=
  match op with
  | u_U l a => "u3(" ++ print_explist l ++ ") " ++ print_argument a ++ ";" ++ newline
  | u_CX a1 a2 => "cx " ++ print_argument a1 ++ "," ++ print_argument a2 ++ ";" ++ newline
  | u_app i l => i ++ " () " ++ print_anylist l ++ ";" ++ newline
  | u_call i es l => i ++ " (" ++ print_explist es ++ ") "
                       ++ print_anylist l ++ ";" ++ newline
  end.
Definition print_qop (op : qop) : string :=
  match op with
  | q_uop u => print_uop u
  | q_meas ain aout => "measure " ++ print_argument ain ++ " -> "
                                  ++ print_argument aout ++ ";" ++ newline
  | q_reset a => "reset " ++ print_argument a ++ ";" ++ newline
  end.
Definition print_gop (op : gop) : string :=
  match op with
  | g_uop u => print_uop u
  | g_barrier ids => "barrier " ++ print_idlist ids ++ ";" ++ newline
  end.
Fixpoint print_goplist (gops : goplist) : string :=
  match gops with
  | [] => ""
  | h :: [] => print_gop h
  | h :: t => print_gop h ++ print_goplist t
  end.

Definition print_decl (d : decl) : string :=
  match d with
  | qreg name size => "qreg " ++ name ++ "[" ++ writeNat size ++ "];" ++ newline
  | creg name size => "creg " ++ name ++ "[" ++ writeNat size ++ "];" ++ newline
  end.
Definition print_gatedecl (name:id) (args:option idlist) (names:idlist) (body:goplist)
  : string := "gate " ++ name ++ " (" ++ print_args args ++ ") " ++ print_idlist names
                     ++ " {" ++ newline
                     ++ print_goplist body
                     ++ "}" ++ newline.

Fixpoint print_statement (s : statement) : string :=
  match s with
  | s_decl d => print_decl d
  | s_gatedecl name args names body => print_gatedecl name args names body
  | s_opaque name args names => "opaque " ++ name ++ " (" ++ print_args args ++ ") "
                                          ++ print_idlist names ++ ";" ++ newline
  | s_qop q => print_qop q
  | s_if x n q => "if(" ++ x ++ "==" ++ writeNat n ++ ") " ++ print_qop q
(*
  | s_ifcall bx q => "if(call(" ++ (print_bexp bx) ++ ")) " ++ print_qop q
*)
  | s_barrier args => "barrier " ++ print_anylist args ++ ";" ++ newline
  | s_output args => ""
  | s_error msg => "Compile Error : " ++ msg ++ newline
  end.

Fixpoint printer' (p : program) : string :=
  match p with
  | [] => ""
  | st :: p' => print_statement st ++ printer' p'
  end.

Fixpoint printer (p : program) : string
  := "OPENQASM 2.0;" ++ newline ++ "include ""qelib1.inc"";" ++ newline ++ printer' p.
