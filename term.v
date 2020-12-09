Require Import Arith.

(*{{{1 var
  Define type Var.
*)
Inductive Var : Set :=
    var : nat -> Var
.
(*1}}}*)

(*{{{1 pterm
  Define type pterm.

  pterm is a definition of a pre-term as it includes 'functions' (F)
  that accept wrong arities.

  V : 'Variable' term composed of a Var
  Un : 'Unit' term composed of one pterm
  Pr : 'Pair' term composed of two pterm
  F : 'Function' term composed of a function arity and a pterm
*)
Inductive pterm : Type :=
    V : Var -> pterm
  | Un: pterm -> pterm
  | Pr: pterm -> pterm -> pterm
  | F : nat -> pterm -> pterm
.
(*1}}}*)

(*{{{1 pterm notations
  Defines pterm notations for readability.
*)
Notation "<< A , B >>" := (Pr A B) (at level 71, format " '<<' A ','  B '>>' ").
Notation "#( A )" := (Un A) (at level 71, format "'#(' A ')'").
Notation "$ A" := (V (var A)) (at level 71, format "'$' A").
(*1}}}*)
    
(*{{{1 pterm_eq
  Computes the equality between two pterms.

  @param a (pterm): the first pterm.
  @param b (pterm): the second pterm.

  @return (bool): true if `a` is equal to `b` else false.
*)
Fixpoint pterm_eq (a b: pterm): bool :=
  match a,b with
    V n, V n'              => match n, n' with var a, var b => a =? b end
  | Un t', Un t''          => pterm_eq t' t''
  | Pr t' t'', Pr t1' t1'' => pterm_eq t' t1' && pterm_eq t'' t1''
  | F n t', F n' t''       => (n =? n') && pterm_eq t' t''
  | _, _                   => false
  end.

Notation "A = B" := (pterm_eq A B).

(*{{{2 Example*)
Compute pterm_eq (<<$3, $1>>) (<<$3, $1>>).
Compute ($3) = ($3).
(*2}}}1}}}*)

(*{{{1 eq_nat_rec
  Computes the equality between two nat recursively.

  @param m (nat): the first nat.
  @param n (nat): the second nat.

  @return (bool): true if `m` is equal to `n` else false.
*)
Fixpoint eq_nat_rec (m n:nat) :=
  match m, n with 
  | 0, 0       => true
  | S m0, S n0 => eq_nat_rec m0 n0
  | _, _       => false
  end.   
(*1}}}*)

(*{{{1 nat_eqdec
  Defines equality decidability on nat.
*)
Lemma nat_eqdec: forall (m n: nat), {m = n} + {m <> n}.
Proof.
  decide equality.
Defined.
(*1}}}*)

(*{{{1 eq_var_rec
  Computes the equality between two Var recursively.

  @param a (Var): the first Var.
  @param b (Var): the second Var.

  @return (bool): true if `a` is equal to `b` else false.
*)
Definition eq_var_rec (a b: Var) := 
  match a, b with
    var n, var m => eq_nat_rec n m
   end.
(*1}}}*)

(*{{{1 eq_dec_var
  Defines equality decidability on Var.
*)
Definition eq_dec_var: forall (x y: Var), {x = y} + {x <> y}.
Proof.
  intros. destruct x, y.
  case (nat_eqdec n n0); intros H.
  rewrite H. left; trivial.
  right. intros H0. apply H.
  inversion H0.
  trivial.
Defined.
(*1}}}*)

(*{{{1 eq_dec_pterm
  Defines equality decidability on pterms.

  To be used with ListSet.
*)
Definition eq_dec_pterm: forall (x y: pterm), {x = y} + {x <> y}.
Proof.
  induction x, y; try (right; unfold "<>"; intro H; inversion H; fail).
  - case (eq_dec_var v v0); intros H.
    rewrite H.
    left; trivial.
    right.
    unfold "<>".
    intros.
    unfold "<>" in H.
    apply H.
    inversion H0.
    trivial.
  - decide equality. 
    apply eq_dec_var.
    apply nat_eqdec.
  - decide equality.
    apply eq_dec_var.
    apply nat_eqdec.
  - decide equality.
    apply eq_dec_var.
    apply nat_eqdec.
Defined.
(*1}}}*)
