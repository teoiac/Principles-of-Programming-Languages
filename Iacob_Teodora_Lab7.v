(*Laboratorul 7*)


Require Import String.
Open Scope string_scope.

Inductive Exp :=
| num : nat -> Exp
| var : string -> Exp
| add : Exp -> Exp -> Exp
| sub : Exp -> Exp -> Exp
| div : Exp -> Exp -> Exp.



(* Coercions *)
Coercion num : nat >-> Exp.
Coercion var : string >-> Exp.
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

Reserved Notation "A -[ S ]-> V"  (at level 60).
Inductive aeval_ss : Exp -> Env -> Exp
                     -> Type :=
| ss_num : forall n sigma,
  num n -[ sigma ]->n
| ss_lookup : forall x sigma,
    (var x) -[ sigma ]-> (sigma x)
| ss_add1 : forall a1 a1' a2 sigma,
  a1 -[ sigma ]-> a1' ->
  (a1 +' a2) -[ sigma ]-> a1' +' a2
| ss_add2 : forall a1 a2 a2' sigma,
  a2 -[ sigma ]-> a2' ->
  (a1 +' a2) -[ sigma ]-> a1 +' a2'
| ss_add : forall (i1 i2 : nat) sigma n,
    n = i1 + i2 -> 
    (i1 +' i2) -[ sigma ]-> n 
| ss_sub1 : forall a1 a1' a2 sigma,
  a1 -[ sigma ]-> a1' ->
 (a1 -' a2) -[ sigma ]-> a1' -' a2
|ss_sub2 : forall a1 a2 a2' sigma,
  a2 -[ sigma ]-> a2'->
  (a1 -' a2) -[ sigma ]-> a1 -' a2' 
|ss_sub : forall (i1 i2 : nat) sigma n,
  i1 > i2 ->n=i1+i2->
  (i1 +' i2) -[ sigma ]-> n
| ss_div1 : forall a1 a1' a2 sigma,
  a1 -[ sigma ]-> a1' ->
 (a1 /' a2) -[ sigma ]-> a1' /' a2
|ss_div2 : forall a1 a2 a2' sigma,
  a2 -[ sigma ]-> a2'->
  (a1 /' a2) -[ sigma ]-> a1 /' a2' 
|ss_div : forall (i1 i2 : nat) sigma n,
  i1 <> i2 -> n=i1+i2->
  (i1 /' i2) -[ sigma ]-> n
where "A -[ S ]-> V" := (aeval_ss A S V).
  

Example e1 : "x" +' 2 -[ update env0 "x" 10 ]->
             10 +' 2.
Proof.
  apply ss_add1.
  apply ss_lookup.
Qed.


Reserved Notation "A -< S >* V"  (at level 61).
Inductive a_clos : Exp -> Env -> Exp
                   -> Type :=
| a_refl : forall a sigma, a -< sigma >* a
| a_tran : forall a1 a2 a3 sigma,
  a1 -[ sigma ]-> a2 ->
  a2 -< sigma >* a3 -> 
  a1 -< sigma >* a3
where "A -< S >* V" := (a_clos A S V).


Inductive Cond :=
| base : bool -> Cond
| bnot : Cond -> Cond
| beq  : Exp -> Exp -> Cond 
| less : Exp -> Exp -> Cond
| bor : Cond -> Cond -> Cond.

Coercion base : bool >-> Cond.

Notation "a <' b" := (less a b) (at level 70, no associativity). 
Notation "a =' b" := (beq a b) (at level 70, no associativity). 
Notation "!' b" := (bnot b) (at level 75, right associativity).
Notation "a |' b" := (bor a b) (at level 85, right associativity).

Reserved Notation "B -{ S }-> B'" (at level 80).

Reserved Notation "B -{ S }-> B'" (at level 80).
Inductive beval : Cond -> Env -> Cond -> Type :=
| b_base : forall b sigma,
    base b -{ sigma }-> base b
| b_bnot1 : forall b b' sigma,
    b -{ sigma }-> b' ->
    !' b -{ sigma }-> !' b'
| b_bnot2 : forall b sigma,
    !' (base b) -{ sigma }-> base (negb b)
| b_beq1 : forall a1 a1' a2 sigma,
    a1 -[ sigma ]-> a1' ->
    (a1 =' a2) -{ sigma }-> (a1' =' a2)
| b_beq2 : forall a1 a2 a2' sigma,
    a2 -[ sigma ]-> a2' ->
    (a1 =' a2) -{ sigma }-> (a1 =' a2')
| b_beq : forall i1 i2 sigma,
    (num i1 =' num i2) -{ sigma }-> base (Nat.eqb i1 i2)
| b_bor1 : forall b1 b1' b2 sigma,
    b1 -{ sigma }-> b1' ->
    (b1 |' b2) -{ sigma }-> (b1' |' b2)
| b_bor2 : forall b1 b2 b2' sigma,
    b2 -{ sigma }-> b2' ->
    (b1 |' b2) -{ sigma }-> (b1 |' b2')
| b_bor : forall b1 b2 sigma,
    (base b1 |' base b2) -{ sigma }-> base (orb b1 b2)
| b_less1 : forall e1 e1' e2 sigma,
    e1 -[ sigma ]-> e1' ->
    (e1 <' e2) -{ sigma }-> (e1' <' e2)
| b_less2 : forall e1 e2 e2' sigma,
    e2 -[ sigma ]-> e2' ->
    (e1 <' e2) -{ sigma }-> (e1 <' e2')
| b_less : forall i1 i2 sigma,
    (num i1 <' num i2) -{ sigma }-> base (Nat.ltb i1 i2)
where "B -{ S }-> B'" := (beval B S B').


Inductive Stmt :=
| skip : Stmt 
| assign : string -> Exp -> Stmt
| seq : Stmt -> Stmt -> Stmt
| ite : Cond -> Stmt -> Stmt -> Stmt (* if-then-else *)
| it  : Cond -> Stmt -> Stmt (* if-then *)
| dowhile : Stmt -> Cond -> Stmt.


Reserved Notation "S ~[ E ]~> S' , E'" (at level 70).

Inductive step : Stmt -> Env -> Stmt -> Env -> Prop :=
| s_assign : forall x e v sigma,
    e -[ sigma ]->num v ->
    assign x e ~[ sigma ]~> skip, (update sigma x v)
| s_seq : forall s1 s2 s1' sigma sigma',
    s1 ~[ sigma ]~> s1', sigma' ->
    seq s1 s2 ~[ sigma ]~> seq s1' s2, sigma'
| s_seq_skip : forall s sigma,
    seq skip s ~[ sigma ]~> s, sigma
| s_ite_true : forall c s1 s2 sigma,
    c -{ sigma }-> base true ->
    ite c s1 s2 ~[ sigma ]~> s1, sigma
| s_ite_false : forall c s1 s2 sigma,
    c -{ sigma }-> base false ->
    ite c s1 s2 ~[ sigma ]~> s2, sigma
| s_while : forall c s sigma,
    dowhile s c ~[ sigma ]~> seq s (ite c (dowhile s c) skip), sigma
where "S ~[ E ]~> S' , E'" := (step S E S' E').


Example test_beval_base_true :
  base true -{ env0 }-> base true.
Proof.
  apply b_base.
Qed.



Inductive Member : Type :=
| member_var : string -> Member
| member_method : string -> list string -> Stmt -> Member.

Inductive Class : Type :=
| class_def : string -> list Member -> Class.

Inductive Object : Type :=
| obj : string -> Class -> Env -> Object.  (* name and class definition *)

Inductive step : Stmt -> Env -> Stmt -> Env -> Prop :=
| s_new : forall c name sigma env',
    (* Assuming we check if class defined and instantiate the object with its environment *)
    obj name c sigma ~[ sigma ]~> skip, env'
| s_method_call : forall obj m args sigma,
    (* Simulate method invocation, we need to define how to resolve a method call *)
    (* This can be expanded with method resolution logic *)
    (* Let's assume we simply execute the corresponding statement in the method *)
    call_method obj m args sigma ~[ sigma ]~> skip, sigma.

(* Example Class *)
Definition my_class := 
  class_def "MyClass" [
    member_var "x";
    member_var "y"; 
    member_method "set_xy" ["new_x"; "new_y"] (seq (assign "x" (var "new_x")) (assign "y" (var "new_y")))
  ].

(* Example for creating an object and calling a method *)
Example test_obj :
  let obj_instance := obj "instance" my_class env0 in
  obj_instance ~[ env0 ]~> call_method obj_instance "set_xy" [num 10; num 20], env'. 
Proof.
  (* The proof will depend on the implementations of the method resolution and environment *)
Admitted.

Definition car_class :=
  class_def "Car" [
    member_var "speed";
    member_method "set_speed" ["s"] (assign "speed" (var "s"));
    member_method "get_speed" [] (assign "result" (var "speed"))
  ].

let car_instance := obj "myCar" car_class env0 in
car_instance ~[ env0 ]~> call_method car_instance "set_speed" [num 100], env'.
car_instance ~[ env0 ]~> call_method car_instance "get_speed" [], env'.
