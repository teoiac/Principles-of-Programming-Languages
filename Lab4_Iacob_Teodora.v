(*Laborator 1*)

(*Exercitiul 1*)

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

Coercion num : nat >-> AExp.
Coercion var : string >-> AExp.

Notation "A +' B" := (add A B)(left associativity,at level 50).
Notation "A -' B" := (sub A B)(left associativity,at level 50).
Notation "A /' B" := (div A B)(left associativity,at level 40).

Check (add (num 2) (add (var "x") (div (num 2) (var "y")))).
Check (add 2 (add "x" (div 2 "y"))).
Set Printing Coercions.
Check (add 2 (add "x" (div 2 "y"))).
Unset Printing Coercions.

Check 2 +' ("x" +' 2 /' "y").
Set Printing All.
Check 2 -' ("x" +' 2 /' "y").
Check 2 -' "x" /' "y".
Check "x" /' "y" +' 2.
Check "x" /' "y" /' "z".
Unset Printing All.

(*Exercitiul 2*)

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

Check "x" <' "y".
Check "x" =' "y".
Check ! "x" =' "y".
Check "x" <' "y" &' "x" =' "y".
Check "x" <' "y" |' "x" =' "y".
Check "x" >' "y" |' "x" =' "y".
Check "x" >' "y".
Check 2 >' "y".
Check 3 >' "y".
Check "x" <=' "y".
Check 3 <=' "y".
Check 2 <=' "y".
Check "x" >=' "y".
Check 2 >=' "y".
Check 1 >=' "y".
Check ! "a" =' "b".
Check !(! "x" <' "y" &' ! "x" =' "y").
Check ("x" <' "y" |' "x" =' "y") .

(*Exercitiul 3*)

Inductive Stmt :=
| skip : Stmt
| assign : string -> AExp -> Stmt
| seq : Stmt -> Stmt -> Stmt
| ite : Cond-> Stmt -> Stmt -> Stmt
| while : Cond -> Stmt -> Stmt.

(*Exercitiul 4*)

(*Coercion deja definit : Coercion var: string>->AExp*)

Notation "A ::= a" := (assign A a) ( at level 90).
Notation "X ;; Y" :=(seq X Y) (at level 100, right associativity).
Notation "'ite' ( c ) ( s1 ) ( s2 )" := (ite c s1 s2) (at level 80, right associativity).
Notation "'while' ( b ) ( s )" := (while b s) (at level 80, right associativity).

Definition compute_modulo (x y : string) :=
  "m" ::= 0 ;;
   while (x >' y) (
      x ::= x -' y
   );;
   ite (x =' y) ("m" ::= 0) ("m" ::= x) ;;
   "result" ::= "m".

Definition is_even (x : string) :=
  ite (x /' 2 =' 0) ("is_even" ::= 1) ("is_even" ::= 0).

(*EXercitiul 5*)

Definition cmmdc (a b : string) :=
  while (! a=' b) (
    ite (a >' b)
      (a ::= a -' b)
      (b ::= b -' a)
  );;
  "result" ::= a.

  

(*Exercitiul 6*)
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

  "result" ::= "b".