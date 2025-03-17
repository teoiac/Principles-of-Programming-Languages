(*Laborator 5*)
Require Import String.
Open Scope string_scope.
Check "a".
Check "".
Check "abcd".

Inductive AExp :=
|num : nat ->AExp
|var : string ->AExp
|add : AExp -> AExp -> AExp
|sub : AExp -> AExp -> AExp
|div : AExp -> AExp -> AExp.

Notation "A +' B" := (add A B)(left associativity,at level 50).
Notation "A -' B" := (sub A B)(left associativity,at level 50).
Notation "A /' B" := (div A B)(left associativity,at level 40).

Coercion num : nat >-> AExp.
Coercion var : string >-> AExp.

Inductive Cond :=
| base : bool -> Cond
| bnot : Cond -> Cond
| beq  : AExp -> AExp -> Cond
| less : AExp -> AExp -> Cond
| band : Cond -> Cond -> Cond.

Coercion base : bool >-> Cond.

Notation "a <' b" := (less a b) (at level 70, no associativity).
Notation "a =' b" := (beq a b) (at level 70, no associativity).
Notation "! b" := (bnot b) (at level 75, right associativity).
Notation "a &' b" := (band a b) (at level 80, right associativity).
Notation "a >' b" := (band (bnot(less a b)) (bnot(beq a b))) (at level 70, no associativity).
Notation "a <=' b" := (bnot((band (bnot(less a b)) (bnot(beq a b)))))  (at level 70, no associativity).
Notation "a >=' b" := (bnot (less a b)) (at level 70, no associativity).
Notation "a |' b" := (bnot (band (bnot a) (bnot b))) (at level 85, right associativity).


Inductive Stmt :=
| assign : string -> AExp -> Stmt
| ite : Cond -> Stmt -> Stmt -> Stmt
| skip : Stmt
| seq : Stmt -> Stmt -> Stmt
| while : Cond -> Stmt -> Stmt.



Notation "A ::= a" := (assign A a) ( at level 90).
Notation "X ;; Y" :=(seq X Y) (at level 100, right associativity).
(*Notation "'ite' ( c ) ( s1 ) ( s2 )" := (ite c s1 s2) (at level 80, right associativity).
Notation "'while' ( b ) ( s )" := (while b s) (at level 80, right associativity).
*)




(*Laboratorul 5*)
(* Environment *)
Definition Env := string -> nat.

Definition env1 :=
  fun (x : string) => 0.
  
Compute env1 "x".
Compute env1 "y".

Definition env2 :=
  fun y => if y =? "n"
           then 10
           else 0.

Compute env2 "n".
Compute env2 "x".

Definition update
  (env : Env)
  (x : string)
  (v : nat) : Env :=
  fun y => if x =? y
           then v
           else env y.

Compute (update env1 "n" 100) "n".

Compute (update env1 "n" 100) "x".

(*Exercitiul 1*)

Fixpoint aeval (a : AExp) (e : Env) : option nat :=
  match a with
  | num n => Some n
  | var x => Some (e x)
  | add a1 a2 =>
      match aeval a1 e, aeval a2 e with
      | Some n1, Some n2 => Some (n1 + n2)
      | _, _ => None
      end
  | sub a1 a2 =>
      match aeval a1 e, aeval a2 e with
      | Some n1, Some n2 =>
          if Nat.ltb n1 n2 then None else Some (Nat.sub n1 n2)
      | _, _ => None
      end
  | div a1 a2 =>
      match aeval a1 e, aeval a2 e with
      | Some v1, Some v2 =>
          if Nat.eqb v2 0 then None else Some (Nat.div v1 v2)
      | _, _ => None
      end
  end.

Compute aeval (2 +' "n") env2.
Compute aeval (2 -' "n") env2.
Compute aeval (11 -' "n") env2.
Compute aeval (100 /' "n") env2.

(*Exercitiul 2*)

Check true.
Check andb.
Print Cond.
Check negb.


Fixpoint beval (b : Cond) (e : Env) : bool :=
  match b with
  | base b => b
  | bnot b => negb (beval b e)
  | band b1 b2 => andb (beval b1 e) (beval b2 e)
  | less a1 a2 =>
      match aeval a1 e, aeval a2 e with
      | Some n1, Some n2 => Nat.ltb n1 n2
      | _, _ => false
      end
  | beq a1 a2 =>
      match aeval a1 e, aeval a2 e with
      | Some n1, Some n2 => Nat.eqb n1 n2
      | _, _ => false
      end
  end.


Compute beval ("i" <' "n") env2.
Compute beval ("n" <' "i") env2.

Print Stmt. 

Fixpoint eval (s : Stmt) (e : Env) (fuel : nat) : Env :=
  match fuel with
  | O => e
  | S n' =>
      match s with
      | assign x a =>
          match aeval a e with
          | Some v => update e x v 
          | None => e
          end
      | ite b s1 s2 =>
          if (beval b e)
          then (eval s1 e n')
          else (eval s2 e n')
      | skip => e
      | seq s1 s2 => eval s2 (eval s1 e n') n'
      | while b s =>
          if negb (beval b e)
          then e
          else eval (seq s (while b s)) e n'
      end
  end.

Definition cmmdc (a b : string) :=
  while (! a=' b) (
    ite (a >' b)
      (a ::= a -' b)
      (b ::= b -' a)
  );;
  "result" ::= a.

Check cmmdc.

Definition init_env : Env :=
  update (update env1 "a" 16) "b" 36.
Definition result_env := eval (cmmdc "a" "b") init_env 100.
Compute result_env "result".


Definition fibonacci (n : string) :=
  "a" ::= 0 ;;
  "b" ::= 1 ;;
  "i" ::= 2 ;;
  
  while ("i" <' n) (
    "c" ::= "b";;
    "b" ::= "a" +' "b";;
    "a" ::= "c";;
    "i" ::= "i" +' 1
  );;

  "result2" ::= "b".

Definition init2_env : Env := update env1 "n" 5.

Definition result2_env := eval (fibonacci "n") init2_env 100.

Compute result2_env "result2".


(*Exercitiul 3*)

Inductive Logica:=
|vp : string->Logica
|neg : Logica->Logica
|and : Logica->Logica->Logica
|or : Logica-> Logica->Logica
|impl: Logica->Logica-> Logica. 

Definition Env_Logica:= string->bool.
Definition env_logica_1 : Env_Logica := fun _ =>false.
Definition update_logica (env : Env_Logica) (x : string) (v_logica : bool) : Env_Logica :=
  fun y => if String.eqb x y then v_logica else env y.

Compute update_logica env_logica_1 "p" true "p".

Fixpoint eval_logica (e : Env_Logica) (p : Logica) : bool :=
  match p with
  | vp x => e x
  | neg p1 => negb (eval_logica e p1)
  | and p1 p2 => andb (eval_logica e p1) (eval_logica e p2)
  | or p1 p2 => orb (eval_logica e p1) (eval_logica e p2)
  | impl p1 p2 => implb (eval_logica e p1) (eval_logica e p2)
  end.

Definition test1 := and (vp "p") (vp "q").

Definition env2_logica := update_logica (update_logica env_logica_1 "p" true) "q" false.

Compute eval_logica env2_logica test1.





