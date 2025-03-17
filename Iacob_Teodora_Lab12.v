(*Lab 12*) 

(*Exercitiul 1*)

Inductive lambda : Type :=
| variabila : nat -> lambda                 
| aplicatie : lambda -> lambda -> lambda    
| abstractie : lambda -> lambda.       


(*Exercitiul 2*)
Fixpoint shift (d : nat) (t : lambda) : lambda :=
  match t with
  | variabila x => if Nat.ltb x d then variabila x else variabila (x + 1)
  | aplicatie t1 t2 => aplicatie (shift d t1) (shift d t2)
  | abstractie t' => abstractie (shift (d + 1) t')
  end.

Fixpoint subst (t : lambda) (n : nat) (s : lambda) : lambda :=
  match t with
  | variabila x => if Nat.eqb x n then s else variabila x
  | aplicatie t1 t2 => aplicatie (subst t1 n s) (subst t2 n s)
  | abstractie t' => abstractie (subst t' (n + 1) (shift 0 s))
  end.



Eval compute in (subst (aplicatie (variabila 0) (variabila 1)) 0 (abstractie (variabila 1)) ).

(*Exercitiul 3*)
Inductive pas : lambda -> lambda -> Prop :=
| beta : forall t s, pas (aplicatie (abstractie t) s) (subst t 0 s)
| apl : forall t1 t1' t2, pas t1 t1' -> pas (aplicatie t1 t2) (aplicatie t1' t2)
| abs : forall t t', pas t t' -> pas (abstractie t) (abstractie t').


Fixpoint eval_cbn (t : lambda) : lambda :=
  match t with
  | aplicatie (abstractie t1) s => subst t1 0 s
  | aplicatie t1 t2 => aplicatie (eval_cbn t1) t2
  | abstractie t1 => abstractie t1
  | variabila x => variabila x
  end.

(*cbv??*)

