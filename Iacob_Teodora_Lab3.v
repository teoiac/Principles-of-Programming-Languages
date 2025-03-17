Inductive Nat := O : Nat | S : Nat -> Nat.

Definition one := S O.
Definition two := S one.
Definition three := S two.
Definition four := S three.
Definition five := S four.

Fixpoint eq_Nat (n m : Nat) :=
  match n, m with
  | O, O       => true
  | O, S _     => false
  | S _, O     => false 
  | S n', S m' => eq_Nat n' m'
  end.

Compute eq_Nat O O.
Compute eq_Nat one O.
Compute eq_Nat one one.
Compute eq_Nat one four.
Compute eq_Nat five four.
Compute eq_Nat five five.

Fixpoint add (m n : Nat) : Nat :=
  match m with
  | O => n
  | S m' => S (add m' n)
  end.


Compute add one one.
Compute add one five.
Compute add five one.
Compute add five O.
Compute add O five.


Fixpoint max (m n : Nat) : Nat :=
  match m with
  | O => n
  | S m' => match n with
            | O => m
            | S n' => S (max m' n')
            end
  end.

Compute max one two.
Compute max O one.
Compute max one O.
Compute max four five.
Compute max five four.

(*Exercitiul 1*)

Fixpoint le_Nat (m n : Nat) : bool :=
  match m, n with
  | O, _       => true         
  | S _, O     => false        
  | S m', S n' => le_Nat m' n' 
  end.

Compute le_Nat O O. (* true *)
Compute le_Nat O one. (* true *)
Compute le_Nat one O. (* false *)
Compute le_Nat one one. (* true *)
Compute le_Nat one five. (* true *)
Compute le_Nat five one. (* false *)
Compute le_Nat five four. (* false *)
Compute le_Nat five five. (* true *)


(*Exercitiul 2*)
Lemma le_then_O :
  forall n,
    le_Nat n O = true -> n = O.
Proof.
  intros n H. 
  induction n as [| n' IH]. 
  -reflexivity.        
  -simpl in H.         
   inversion H.        
Qed.

(*Exercitiul 3*)

Lemma le_refl:
  forall x,
    le_Nat x x = true.
Proof.
    intros x.
    induction x as [| x' IH].
    -reflexivity.
    -simpl.
    apply IH.    
Qed.


Lemma le_Trans:
forall m n p,
  le_Nat m n = true ->
  le_Nat n p = true ->
  le_Nat m p = true.
Proof.
(*intros m n p H1 H2.*)
induction m.
- simpl. reflexivity.
- intros n p H1 H2.
  simpl.
  destruct p.
  + simpl in *.
  destruct n.
  assumption.
  simpl in H2.
  assumption.
  + simpl in H1.
  destruct n.
    ++ inversion H1.
    ++ simpl in H2.
      apply IHm with (n := n).
      exact H1.
      exact H2.
Qed.

(*Exercitiul 4*)
Lemma le_add : forall x y,
  le_Nat x (add x y) = true.
Proof.
  intros x y.
  induction x as [| x' IH]. 
  - 
    simpl. 
    reflexivity.
  - 
    simpl.
    apply IH.
    
Qed.

(*Exercitiul 5*)
Lemma le_2_add : forall x y z,
  le_Nat x y = true ->
  le_Nat x (add y z) = true.
Proof.
  intro x.
  induction x as [| x' IH].
  - simpl. 
    reflexivity.
  - intros y z Hxy.
    simpl in Hxy.
    destruct y as [| y'].
    + inversion Hxy.
    + simpl. 
    destruct z as [| z'].
      * 
        apply IH. 
        assumption.
      *simpl.
      apply IH.
      assumption.  
Qed.

(*Exercitiul 6*)
Lemma le_xy_max_y : forall x y,
  le_Nat x y = true ->
  max x y = y.
Proof.
  induction x as [| x' IH]; intros.
  -simpl. reflexivity.
  -simpl. destruct y as [| y'].
    +simpl in H. 
     inversion H.
    +simpl in H. 
    apply IH in H. 
    rewrite H. 
    reflexivity.
Qed.

(*Exercitiul 7*)

Lemma nle_x_y_max_x : forall x y,
    le_Nat x y = false ->
    max x y = x.
Proof.
  induction x as [|x' IH];
  intros.
-simpl.
 inversion H.
-simpl.
 destruct y as [|y'].
 +reflexivity.
 +simpl in H.
  inversion H.
  apply IH in H.
  rewrite H.
  reflexivity.
Qed.

   





