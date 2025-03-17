(*PARSER PENTRU IMP*)
Require Import Coq.Strings.String.
Require Import Coq.Strings.Ascii.
Require Import Coq.Lists.List.
Require Import Arith.
Require Import Init.Nat.
Require Import EqNat.
Require Import List. Import ListNotations.
Require Import Coq.Bool.Bool.

Import ListNotations.

Inductive AExp :=
| avar : string -> AExp
| anum : nat -> AExp
| aplus : AExp -> AExp -> AExp
| amul : AExp -> AExp -> AExp.

Coercion anum : nat >-> AExp.
Coercion avar : string >-> AExp.

Inductive BExp :=
| btrue : BExp
| bfalse : BExp
| bnot : BExp -> BExp
| band : BExp -> BExp -> BExp
| blessthan : AExp -> AExp -> BExp
| bgreaterthan : AExp -> AExp -> BExp.

Inductive Stmt :=
| skip : Stmt
| seq : Stmt -> Stmt -> Stmt
| assign : string -> AExp -> Stmt
| if_then_else : BExp -> Stmt -> Stmt -> Stmt
| while_do : BExp -> Stmt -> Stmt.

Definition token := string.
Inductive optionE (X : Type) : Type :=
| SomeE (x : X)
| NoneE (err : string).

Arguments SomeE {X}.
Arguments NoneE {X}.

Notation "' p <- e1 ;; e2" :=
  (match e1 with
   | SomeE p => e2
   | NoneE err => NoneE err
   end)
  (right associativity, at level 60).

Definition parser (T : Type) := list token -> optionE (T * list token).

Definition list_of_string (s : string) : list ascii :=
  let fix aux n :=
      match n with
      | 0 => []
      | S n' => match String.get n' s with
                | None => []
                | Some c => c :: aux n'
                end
      end
  in aux (String.length s).

Definition parseAExp (tokens : list token) : optionE (AExp * list token) := 
  match tokens with 
  | [] => NoneE "Expected arithmetic expression"
  | t :: ts => 
      let digit_check (c: ascii) := 
        let n := nat_of_ascii c in 
        (nat_of_ascii "0" <=? n) && (n <=? nat_of_ascii "9") 
      in
      if forallb digit_check (list_of_string t) 
      then 
        let parse_digit (d: ascii) := nat_of_ascii d - nat_of_ascii "0" in
        let digit_list := list_of_string t in
        SomeE (anum (fold_left (fun acc d => acc * 10 + parse_digit d) (rev digit_list) 0), ts)
      else 
        SomeE (avar t, ts)
  end.

Open Scope string_scope.

Fixpoint parseBExp (tokens : list token) : optionE (BExp * list token) :=
  match tokens with
  | [] => NoneE "Expected boolean expression"
  | "true" :: ts => SomeE (btrue, ts)
  | "false" :: ts => SomeE (bfalse, ts)
  | "~" :: ts =>
    match parseBExp ts with
    | SomeE (e, rest) => SomeE (bnot e, rest)
    | NoneE err => NoneE err
    end
  | t1 :: "<" :: ts =>
    match parseAExp (t1 :: ts) with
    | SomeE (a1, rest1) =>
      match parseAExp rest1 with
      | SomeE (a2, rest2) => SomeE (blessthan a1 a2, rest2)
      | NoneE err => NoneE err
      end
    | NoneE err => NoneE err
    end
  | t1 :: ">" :: ts =>
    match parseAExp (t1 :: ts) with
    | SomeE (a1, rest1) =>
      match parseAExp rest1 with
      | SomeE (a2, rest2) => SomeE (bgreaterthan a1 a2, rest2)
      | NoneE err => NoneE err
      end
    | NoneE err => NoneE err
    end
  | _ => NoneE "Invalid boolean expression"
  end.


Fixpoint parseStmt (fuel: nat) (tokens: list token) : optionE (Stmt * list token) :=
  match fuel with
  | 0 => NoneE "Out of fuel"
  | S fuel' =>
    match tokens with
    | [] => NoneE "Expected statement"

    (* kip statement *)
    | "skip" :: rest => SomeE (skip, rest)

    (* assignment: var := aexp *)
    | var :: ":=" :: rest =>
      match parseAExp rest with
      | SomeE (aexp, rest') => SomeE (assign var aexp, rest')
      | NoneE err => NoneE err
      end

    (* if-then-else statement *)
    | "if" :: rest =>
      match parseBExp rest with
      | SomeE (bexp, rest') =>
        match rest' with
        | "then" :: rest'' =>
          match parseStmt fuel' rest'' with
          | SomeE (stmt1, rest''') =>
            match rest''' with
            | "else" :: rest'''' =>
              match parseStmt fuel' rest'''' with
              | SomeE (stmt2, rest''''') => SomeE (if_then_else bexp stmt1 stmt2, rest''''')
              | NoneE err => NoneE err
              end
            | _ => NoneE "Expected else"
            end
          | NoneE err => NoneE err
          end
        | _ => NoneE "Expected then"
        end
      | NoneE err => NoneE err
      end

    (* while-do statement *)
    | "while" :: rest =>
      match parseBExp rest with
      | SomeE (bexp, rest') =>
        match rest' with
        | "do" :: rest'' =>
          match parseStmt fuel' rest'' with
          | SomeE (stmt, rest''') => SomeE (while_do bexp stmt, rest''')
          | NoneE err => NoneE err
          end
        | _ => NoneE "Expected do"
        end
      | NoneE err => NoneE err
      end

    (* Invalid statement *)
    | _ => NoneE "Invalid statement"
    end
  end.

Fixpoint parseSeq (fuel: nat) (tokens: list token) : optionE (Stmt * list token) :=
  match fuel with
  | 0 => NoneE "Out of fuel"
  | S fuel' =>
    match parseStmt fuel' tokens with
    | SomeE (stmt, rest) =>
      match rest with
      | ";" :: ts =>
        match parseSeq fuel' ts with
        | SomeE (next, rest') => SomeE (seq stmt next, rest')
        | NoneE err => NoneE err
        end
      | _ => SomeE (stmt, rest)
      end
    | NoneE err => NoneE err
    end
  end.


 
Definition parseProgram (fuel: nat) (tokens: list token) : optionE Stmt :=
  match parseSeq fuel tokens with
  | SomeE (stmt, []) => SomeE stmt
  | SomeE (_, t :: _) => NoneE ("Unexpected token: " ++ t)
  | NoneE err => NoneE err
  end.


Eval compute in parseAExp ["123"].
Eval compute in parseStmt 10 ["skip"].
Eval compute in parseStmt 10 ["x"; ":="; "42"].
Eval compute in parseStmt 10 ["if"; "true"; "then"; "skip"; "else"; "skip"].
Eval compute in parseSeq 10 ["x"; ":="; "42"; ";"; "skip"; ";"; "if"; "true"; "then"; "skip"; "else"; "skip"].
Eval compute in parseStmt 10 ["while"; "x"; "<"; "10"; "do"; "x"; ":="; "10"; "+"; "1"].







