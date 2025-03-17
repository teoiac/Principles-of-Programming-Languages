(*Lab10*)
Require Import String.
Require Import List.
Import ListNotations.

Inductive B :=
| T : B
| F : B
| neg : B -> B
| and : B -> B -> B
| or  : B -> B -> B.

(*Exercitiul 1 - Interpreter*)
Fixpoint interpret(b : B) : bool :=
match b with
|T  => true
|F  => false
|neg b' => negb (interpret b')
| and b1 b2 => andb (interpret b1)(interpret b2)
|or b1 b2 => orb (interpret b1)(interpret  b2)
end.
 
Compute interpret ( neg T).
Compute interpret (neg F).
Compute interpret (and T F).
Compute interpret ( or T F).

(*Exercitiul 2*)
Inductive Instruction :=
| push : nat -> Instruction
| inv : Instruction
| add : Instruction
| mul : Instruction.



Definition run_instruction (i : Instruction) (stack : list nat) : list nat :=
 match i with 
| push n => match n with 
            | O => O :: stack 
            | S O => (S O) :: stack 
            | _ => stack
           end 
| inv => match stack with 
          | x :: rest =>
            match x with
            | O => (S O) :: rest 
            | (S O) => O :: rest 
            | _ => rest
            end
          |_ =>stack
        end
| add => match stack with 
            | O :: O :: rest => O :: rest 
            | O :: (S O) :: rest => (S O) :: rest 
            | (S O) :: O :: rest => (S O) :: rest 
            | (S O) :: (S O) :: rest => O :: (S O) :: rest
            | _ => stack end 
| mul => match stack with 
            | O :: _ :: rest => O :: rest 
            | _ :: O :: rest => O :: rest 
            | (S O) :: (S O) :: rest => (S O) :: rest 
            | _ => stack end 
end.

Definition exp_stack := [O; S O; O].
Compute run_instruction (push O) exp_stack.
Compute run_instruction inv exp_stack.
Compute run_instruction add exp_stack. 
Compute run_instruction mul exp_stack.

(*Exercitiul 3*)

Fixpoint run_instructions (stpgm : list Instruction) (stack : list nat) : list nat :=
  match stpgm with
  | [] => stack
  | i :: rest => run_instructions rest (run_instruction i stack)
  end.

Definition example_instructions := [push (S O); push O; add; inv; push O; mul].

Compute run_instructions example_instructions [].


(*Exercitiul 4*)
Fixpoint compile (b : B) : list Instruction :=
  match b with
|T => [push (S O)]
|F => [push O]
|neg b' => compile b' ++ [inv]
|and b1 b2 => compile b1 ++ compile b2 ++ [mul]
|or b1 b2 => compile b1 ++ compile b2 ++ [add] 
  end.

Compute compile F.
Compute compile (neg F).
Compute compile (or T F).

(*Exercitiul 5*)
Definition to_nat (b : bool) : nat :=
  if b then 1 else 0.

Lemma soundness_helper:
  forall b instrs stack,
    run_instructions ((compile b) ++ instrs) stack =
    run_instructions instrs (to_nat (interpret b) :: stack).
Proof.
  induction b; intros instrs stack.
  - simpl. reflexivity.
  - simpl. reflexivity.
  - simpl.
    rewrite <- app_assoc.
    rewrite IHb.
    simpl.
    destruct (interpret b); simpl; reflexivity.
  - simpl.
    rewrite <- app_assoc.
    rewrite IHb1.
    rewrite <- app_assoc.
    rewrite IHb2.
    simpl.
    destruct (interpret b1), (interpret b2); simpl; reflexivity.
  - simpl.
    rewrite <- app_assoc.
    rewrite IHb1.
    rewrite <- app_assoc.
    rewrite IHb2.
    simpl.
    destruct (interpret b1),(interpret b2);simpl;
    reflexivity.
(*???????????????????????????????????????????nu merge nu stiu de ce*)
Qed.





