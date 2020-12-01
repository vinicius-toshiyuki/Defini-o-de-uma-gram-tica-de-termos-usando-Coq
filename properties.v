Require Export term.

(*{{{1 parameter
  Counts the arity of a function.

  parameter counts the arity of the topmost F in a pterm.
  Should not be used directly in pterm's other than F.

  @param t (pterm): the F which parameters are to be counted

  @return (nat): returns a nat which represents the arity of t
*)
Fixpoint parameter (t: pterm): nat :=
  (* Define auxiliar function is_f to stop recursion on inner F's *)
  let is_f (t: pterm): bool :=
    match t with
      F _ _ => true
    | _     => false
    end in
  match t with
    V _       => 1
  | Un t'     => if (is_f t') then 1 else parameter t'
  | Pr t' t'' =>
      (if (is_f t') then 1 else parameter t') +
      (if (is_f t'') then 1 else parameter t'')
  | F n t'    => parameter t'
  end.

(*{{{2 Example
  If an argument has length > 1, then it must
  be a function's return value, otherwise the
  arity and argument list length will not match
*)
Compute parameter (F 3 (Pr (F 1 (V (var 4))) (F 3 (Pr (V (var 2)) (V (var 3)))))).
(*2}}}1}}}*)

(*{{{1 is_F
  Checks if a F is well-formed.

  is_F checks if a F has the correct arity.

  @param t (pterm): the F to be checked

  @return (bool): true if t is well-formed, else otherwise
*)
Fixpoint is_F (t: pterm): bool := 
  match t with
    V _       => true
  | Un t'     => is_F t'
  | Pr t' t'' => is_F t' && is_F t''
  | F n t'    => if (beq_nat n (parameter t')) then is_F t' else false
  end.

(*{{{2 Example*)
Compute is_F (F 3 (Pr (V (var 1)) (F 2 (V (var 3))))).
Compute is_F (F 3 (Pr (V (var 1)) (Pr (V (var 2)) (F 2 (Pr (V (var 1)) (F 2 (V (var 2)))))))).
(*2}}}1}}}*)

(*{{{1 count_var
  Count vars in a pterm.

  @param t (pterm): the pterm.

  @return (nat): the number of vars in `t`.
*)
Fixpoint count_var (t: pterm): nat :=
  match t with
    V _       => 1
  | Un t'     => count_var t'
  | Pr t' t'' => count_var t' + count_var t''
  | F _ t'    => count_var t'
  end.

(*{{{2 Example*)
Compute count_var (F 3 (<<$1, <<$2, F 2 (<<$1, F 2 ($2)>>)>> >>)).
(*2}}}1}}}*)

(*{{{1 ListSet notations*)
Local Notation "'{}'" := (empty_set pterm).
Local Notation "A +> B" := (set_add eq_dec_pterm A B) (right associativity, at level 71).
Local Notation "A + B" := (set_union eq_dec_pterm A B).
(*1}}}*)

(*{{{1 psubterm
  Computes the subterms of a pterm.

  @param t (pterm): the pterm.

  @return (list pterm): a list of the subterms of `t`.
*)
Fixpoint psubterm (t: pterm): list pterm :=
  match t with
    V _       => t +> {}
  | Un t'     => t +> psubterm t'
  | Pr t' t'' => t +> psubterm t' + psubterm t''
  | F _ t'    => t +> psubterm t'
  end.

(*{{{2 Example*)
Compute psubterm (<<#($1), ($1)>>).
Compute psubterm ($3).
(*2}}}1}}}*)

(*{{{1 poccur
  Counts occurences of `i` in `t`.

  @param t (pterm): a pterm.
  @param i (pterm): a pterm to be counted in `t`.

  @return (nat): number of occurences of `i` in `t`.
*)
Fixpoint poccur (t i: pterm): nat :=
  match t with
    V _       => if t = i then 1 else 0
  | Un t'     => (if t = i then 1 else 0) + poccur t' i
  | Pr t' t'' => (if t = i then 1 else 0) + poccur t' i + poccur t'' i
  | F _ t'    => (if t = i then 1 else 0) + poccur t' i
  end.

(*{{{2 Example*)
Compute poccur (<<$2, <<#($2), ($3)>> >>) ($2).
(*2}}}1}}}*)

(*{{{1 plength
  Compute length of a pterm.

  @param t (pterm): the pterm.

  @return (nat): length of `t`.
*)
Fixpoint plength (t: pterm): nat :=
  match t with
    V _       => 1
  | Un t'     => 1 + plength t'
  | Pr t' t'' => 1 + plength t' + plength t''
  | F _ t'    => 1 + plength t'
  end.

(*{{{2 Example*)
Compute plength (F 3 (<<#($3), #($1)>>)).
(*2}}}1}}}*)

(*{{{1 pterm_iarg
  Compute `i`-th argument of a pterm F.

  Indexes start at 0.

  @param t (pterm): base pterm.
  @param i (nat): index of `t`

  @return (option pterm): Some `i`-th argument of `t` if `i` is valid, None otherwise
*)
Fixpoint pterm_iarg (t: pterm) (i: nat): option pterm :=
  (* Define auxiliar function is_f to stop recursion on inner F's *)
  let is_f (t: pterm): bool :=
    match t with
      F _ _ => true
    | _     => false
    end in
  match t with
    V _       => if i =? 0 then Some t else None 
  | Un t'     => if (andb (is_f t') (i =? 0)) then Some t' else pterm_iarg t' i
  | Pr t' t'' => (
     if (andb (is_f t') (i =? 0)) then
       Some t
       else 
         let iterm := pterm_iarg t' i in
         match iterm with
           None => (
              if (andb (is_f t'') (i - (parameter t') =? 0)) then
              Some t''
              else
              pterm_iarg t'' (i - parameter t')
            )
         | Some _ => iterm
         end
     )
  | F n t'    => if n <? i then None else pterm_iarg t' i
  end.

(*{{{2 Example*)
Compute pterm_iarg (F 3 (<< <<#($3), (#($5))>>, #(F 1 ($1))>>)) 2.
(*2}}}1}}}*)

(*{{{1 pterm_ith
  Compute i-th term of a pterm.

  Indexes start at 0.

  @param t (pterm): base pterm.
  @param i (nat): index of `t`

  @return (option pterm): Some `i`-th term of `t` if `i` is valid, None otherwise
*)
Definition pterm_ith (t: pterm) (i: nat): option pterm :=
  (* Auxiliar recursively defined function *)
  let fix pterm_ith_aux (queued: list pterm) (i: nat) {struct i} :=
    (* Recursion on `i` *)
    match i with
      (* If `i` is 0 then return (None if `queued` is empty else the first element) *)
      0   => match queued with nil => None | hd::tl => Some hd end
    | S n =>
      match queued with
        nil    => None
      | hd::tl => (* Breadth-first search *)
        match hd with
          V v       => pterm_ith_aux tl n
        | Un t'     => pterm_ith_aux (tl++(t'::nil)) n
        | Pr t' t'' => pterm_ith_aux (tl++(t'::t''::nil)) n
        | F m t'    => pterm_ith_aux (tl++(t'::nil)) n
        end
      end
   end in
  pterm_ith_aux (t::nil) i.

(*{{{2 Example*)
Compute pterm_ith (F 3 (<< <<#($3), (#($5))>>, #(F 1 ($1))>>)) 10.
(*2}}}1}}}*)

(*{{{1 premove FIXME
  Definir uma função que elimine o i-esimo 
  elemento de um termo
  NOTE: como funciona retirar um par?
*)
Fixpoint premove (t: pterm) (i: nat): option pterm :=
  match t with
    V _       => if i =? 0 then None else Some t
  | Un t'     => if i =? 0 then None else Some t
  | Pr t' t'' => if i =? 0 then None else
                 let rterm := premove t' (i - 1) in
                 match rterm with
                   None   => premove t'' (i - plength t')
                 | Some _ => rterm
                 end
  | F _ t'    => if i =? 0 then None else premove t' (i - 1)
  end.

(*{{{2 Example*)
Compute premove (F 3 (<< <<#($3), #($5)>>, #($1)>>)) 0.
(*2}}}1}}}*)

(*{{{1 term NOTE
  Define type term

  term is a definition of a term. It removes badly-formed F's from pterm.

  t : t in pterm such that t is a well-formed F or not a F
*)
Definition term: Set := {t: pterm | is_true (is_F t)}.
(*1}}}*)

