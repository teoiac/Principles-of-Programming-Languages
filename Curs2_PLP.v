(*
      .
-------------(zero)
0 in Nat


   n in Nat
-------------(succ)
S n in Nat

*)

Inductive Nat:=
|O : Nat (*zero*)
|S : Nat -> Nat  (*succ*).

Check O.
Check (S O).
Check S (S O).
(*Gresit : Check S S.*)

(*
    O + m = m
    S n + m = S(n+m)

*)

(*ADUNARE - functie recursiva*)

Fixpoint plus (n m : Nat) : Nat :=
  match n with 
   | O => m
   | S k => S (plus k m)
  end.

Compute plus O (S O).
Compute plus (S O) (S O).

Compute plus (S(S O)) (S O).

Lemma plus_0_m_is_m :
  forall m,
    plus O m = m.
Proof.
  (*proof script - lista de tactici care permit manipularea demonstratiei*)
    intro m.
    simpl.
    reflexivity.
Qed.
  
Lemma plus_eq : 
  forall m n, m=n ->
              plus O m = plus O n.
Proof.
  intros m n H.
  rewrite H.  
  reflexivity.
Qed.

Theorem plus_c_a:
  forall k,
    plus k (S O) <> O.
Proof.
  intros k.
  unfold not.
  intro H.
  destruct k as [ |k'];simpl in H;inversion H.
Qed.

Print Nat_ind.

Lemma plus_n_0_is_n:
  forall n,
    plus n O = n.
Proof.
    induction n.
    -simpl.
     reflexivity.
    -simpl.
      rewrite IHn.
      reflexivity.
Qed.

Theorem plus_comm:
  forall m n,
    plus m n = plus n m.
Proof.
  induction m.
  -intro n.
  rewrite plus_n_0_is_n.  
  rewrite plus_0_m_is_m.
  reflexivity.
  -induction n.
    +rewrite plus_n_0_is_n.
     simpl.
     reflexivity.
     +simpl.
      rewrite <-IHn.
      simpl.
      rewrite IHm.
      simpl.
      rewrite IHm.
      reflexivity.
Qed.

Lemma plus_assoc:
  forall m n p,
    plus m (plus n p) = 
      plus ( plus m n) p.
Proof.
induction m.
-simpl. reflexivity.
-intros n p.
simpl.
rewrite IHm.
reflexivity.
Qed.









