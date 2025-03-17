Require Import String.
Open Scope string_scope.

Check "asdasf".

(*Exercitiul 1*)
Inductive AExp :=
| num : nat -> AExp
| var : string -> AExp
| add : AExp -> AExp -> AExp
| sub : AExp -> AExp -> AExp
| div : AExp -> AExp -> AExp.

(* Coercions *)
Coercion num : nat >-> AExp.
Coercion var : string >-> AExp.
Notation "A +' B" := (add A B)(left associativity,at level 50).
Notation "A -' B" := (sub A B)(left associativity,at level 50).
Notation "A /' B" := (div A B)(left associativity,at level 40).


(* Environment *)
Definition Env := string -> nat.
Definition env0 :=
  fun (x : string) => 0.
Definition update
  (env : Env)
  (x : string)
  (v : nat) : Env :=
  fun y => if x =? y
           then v
           else env y.



(* <AExp, Env> => <nat> *)

Reserved Notation "A =[ S ]=> V"  (at level 60).

Inductive aeval : AExp -> Env -> nat -> Type := 
| const : forall n sigma, (num n) =[ sigma ]=> n 
| lookup : forall x sigma, (var x) =[ sigma ]=> (sigma x) 
| bs_add : forall a1 a2 sigma i1 i2 n, 
a1 =[ sigma ]=> i1 -> 
a2 =[ sigma ]=> i2 -> 
n = i1 + i2 -> 
a1 +' a2 =[ sigma ]=> n 
| bs_sub : forall a1 a2 sigma i1 i2 n, 
a1 =[ sigma ]=> i1 -> 
a2 =[ sigma ]=> i2 -> 
i1 > i2 ->
n = i1 - i2 -> 
a1 -' a2 =[ sigma ]=> n 
| bs_div : forall a1 a2 sigma i1 i2 n,
 a1 =[ sigma ]=> i1 -> 
a2 =[ sigma ]=> i2 -> 
i2 <> 0 -> 
n = Nat.div i1 i2 -> 
a1 /' a2 =[ sigma ]=> n 
where "A =[ S ]=> V" := (aeval A S V).

Print Nat.
Require Import Lia.

Example e1 : "x" -' 2 =[ update env0 "x" 10 ]=> 8.
Proof.
  apply bs_sub with (i1 := 10) (i2 := 2).
  - apply lookup.
  - apply const.
  - simpl.
    lia.
  -trivial.
Qed.

(*Example e2 : "x" -'3 =[update env0 "x" 1 ] =>
*)

Example e3 : (num 10 /' num 2) =[ fun _ => 0 ]=> 5.
Proof.
  apply bs_div with (i1 := 10) (i2 := 2).
  - apply const.
  - apply const.
  - discriminate. 
  - simpl. reflexivity. 
Qed.

Example e4 : (num 20 /' num 4) =[ fun _ => 0 ]=> 5. 
Proof. apply bs_div with (i1 := 20) (i2 := 4).
 - apply const.
 - apply const.
 - simpl. auto. 
 - simpl. reflexivity.
Qed.


(*Exercitiul 2*)
Inductive Cond :=
| base : bool -> Cond
| bnot : Cond -> Cond
| beq  : AExp -> AExp -> Cond 
| less : AExp -> AExp -> Cond
| bor : Cond -> Cond -> Cond.

Coercion base : bool >-> Cond.

Notation "a <' b" := (less a b) (at level 70, no associativity). 
Notation "a =' b" := (beq a b) (at level 70, no associativity). 
Notation "! b" := (bnot b) (at level 75, right associativity).
Notation "a |' b" := (bor a b) (at level 85, right associativity).

Check Nat.ltb.
Check Nat.eqb.
Reserved Notation "B -[ S ]-> B'"  (at level 80).
Inductive beval : Cond -> Env -> bool -> Type :=
| notTrue : forall b sigma,
  b -[ sigma ]-> true -> 
  ! b -[ sigma ]-> false
| notFalse : forall b sigma,
  b -[ sigma ]-> false -> 
  ! b -[ sigma ]-> true
| blt1 : forall a1 a2 i1 i2 b sigma,
  a1 =[ sigma ]=> i1 ->
  a2 =[ sigma ]=> i2 -> 
  b = Nat.ltb i1 i2 -> 
  a1 <' a2 -[ sigma ]-> b
| beq1 : forall a1 a2 i1 i2 b sigma,
  a1 =[ sigma ]=> i1 ->
  a2 =[ sigma ]=> i2 -> 
  b = Nat.eqb i1 i2 ->
  a1 =' a2 -[ sigma ]->b
| b_or_true : forall b1 b2 sigma,
    b1 -[ sigma ]-> true ->
    (b1 |' b2) -[ sigma ]-> true
| b_or_false : forall b1 b2 sigma bv2,
    b1 -[ sigma ]-> false ->
    b2 -[ sigma ]-> bv2 ->
    (b1 |' b2) -[ sigma ]-> bv2
where "B -[ S ]-> B'" := (beval B S B').
Definition env1 :=
  update
    (update
        (update env0 "i" 10)
        "j" 11)
       "n" 12.

Create HintDb mydb.
Hint Constructors beval : mydb.
Hint Constructors aeval : mydb.
Hint Unfold Nat.ltb : mydb.
Hint Unfold env1 : mydb.
Inductive Stmt :=
| skip : Stmt 
| assign : string -> AExp -> Stmt
| seq : Stmt -> Stmt -> Stmt
| ite : Cond -> Stmt -> Stmt -> Stmt (* if-then-else *)
| it  : Cond -> Stmt -> Stmt (* if-then *)
| dowhile : Stmt -> Cond -> Stmt.


Notation "A ::= a" := (assign A a) ( at level 90).
Notation "X ;; Y" :=(seq X Y) (at level 100, right associativity).


Reserved Notation "S ~[ E ]~> E'" (at level 99).
Inductive eval : Stmt -> Env -> Env -> Type := 
| b_skip : forall sigma, 
 skip ~[ sigma ]~> sigma 
| b_assign : forall x a v sigma sigma',
 a =[ sigma ]=> v -> sigma' = update sigma x v ->
 (x ::= a) ~[ sigma ]~> sigma' 
| b_seq : forall s1 s2 sigma1 sigma2 sigma3,
 s1 ~[ sigma1 ]~> sigma2 ->
 s2 ~[ sigma2 ]~> sigma3 ->
 (s1 ;; s2) ~[ sigma1 ]~> sigma3 
| b_ite_true : forall b  sigma sigma' s1 s2,
 b -[ sigma ]-> true -> s1 ~[ sigma ]~> sigma' ->
 (ite b s1 s2) ~[ sigma ]~> sigma' 
| b_ite_false : forall b s1 s2 sigma sigma', 
  b -[ sigma ]-> false ->
  s2 ~[ sigma ]~> sigma' ->
 (ite b s1 s2) ~[ sigma ]~> sigma' 
| b_it_true : forall b s sigma sigma',
 b -[ sigma ]-> true ->
 s ~[ sigma ]~> sigma' ->
 (it b s) ~[ sigma ]~> sigma' 
| b_it_false : forall b s sigma,
 b -[ sigma ]-> false ->
 (it b s) ~[ sigma ]~> sigma 
| b_dowhile : forall s b sigma sigma' sigma'', 
s ~[ sigma ]~> sigma' ->
 b -[ sigma' ]-> true ->
 (dowhile s b) ~[ sigma' ]~> sigma'' ->
 (dowhile s b) ~[ sigma ]~> sigma'' 
| b_dowhile_end : forall s b sigma sigma', 
s ~[ sigma ]~> sigma' ->
 b -[ sigma' ]-> false ->
 (dowhile s b) ~[ sigma ]~> sigma' 
where "S ~[ E ]~> E'" := (eval S E E').

Hint Constructors eval : mydb.
Hint Unfold env0 : mydb.

Example exemplu_skip : skip ~[ env0 ]~> env0.
Proof.
  apply b_skip.
Qed.

Example blabla:
  ("x" ::= num 5) ~[ env0 ]~> (update env0 "x" 5).
Proof.
  eauto with mydb.
Qed.

Example exemplu_assign : ("x" ::= num 5) ~[ env0 ]~> (update env0 "x" 5).
Proof.
  eauto with mydb.
Qed.


Example exemplu_seq : ("x" ::= num 2 ;; "y" ::= num 3) ~[ env0 ]~> (update (update env0 "x" 2) "y" 3).
Proof.
  eauto with mydb.
Qed.

Example ex_ite_true : (ite (base true) ("x" ::= num 5) ("y" ::= num 10)) ~[ env0 ]~> (update env0 "x" 5). 
Proof.
  eauto with mydb.
Qed.




