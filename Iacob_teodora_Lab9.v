(*Exercitiul 1*)
Require Import String.


(*Exercitiul 1*)
Inductive Exp :=
|O : Exp
|S : Exp -> Exp
|isZero : Exp -> Exp
|T : Exp
|F : Exp
|ite : Exp -> Exp -> Exp -> Exp.


Inductive SS_exp : Exp -> Exp -> Prop :=
|SS_IsZeroO : SS_exp (isZero O) T
|SS_IsZeroS : forall e, SS_exp (isZero (S e)) F
|SS_IteT : forall e1 e2, SS_exp (ite T e1 e2) e1
|SS_IteF : forall e1 e2, SS_exp (ite F e1 e2) e2
|SS_Ite : forall e1 e1' e2 e3,
      SS_exp e1 e1' -> SS_exp (ite e1 e2 e3) (ite e1' e2 e3)
|SS_S : forall e e',
      SS_exp e e' -> SS_exp (S e) (S e')
|SS_IsZero : forall e e',
      SS_exp e e' -> SS_exp (isZero e) (isZero e').

(*Exeercitiul 2*)

(*
            .
TZero -------------
         O : Nat

        e : Nat
TSucc ---------------
        S e : Nat

            e : Nat
TisZero ---------------
        isZero e  : Bool

             .
TTrue ------------------
          T : Bool

             .
TFalse ------------
        F : Bool



        e1 : Bool     e2 : T     e3 : T
Tite-----------------------------------------
               ite e1 e2 e3 : T

*)

Inductive Tip :=
|Nat : Tip
|Bool : Tip.

Inductive tipizare : Exp -> Tip ->Prop:=
|TZero : tipizare O Nat
|TSucc : forall e, tipizare e Nat -> tipizare (S e) Nat
|TIsZero : forall e, tipizare e Nat ->tipizare (isZero e) Bool
|TTrue : tipizare T Bool
|TFalse : tipizare F Bool
|Tite : forall e1 e2 e3 T, tipizare e1 Bool -> tipizare e2 T -> tipizare e3 T -> tipizare (ite e1 e2 e3) T.


Example ex1 : tipizare (ite T (S O) O) Nat.
Proof.
  apply Tite.
  - apply TTrue.
  - apply TSucc. apply TZero.
  - apply TZero.
Qed.


Theorem preservation : forall e e' T,
  tipizare e T ->
  SS_exp e e' ->
  tipizare e' T.
Proof.
  intros e e' T HT Hstep.
  generalize dependent T.
  induction Hstep; intros T HT; inversion HT; subst.
  -constructor.
  - constructor.
  - assumption.
  -assumption.
  - apply Tite.
    + apply IHHstep. assumption.
    + assumption.
    + assumption.
  -apply TSucc. apply IHHstep. assumption.
  - apply TIsZero. apply IHHstep. assumption.
Qed.



