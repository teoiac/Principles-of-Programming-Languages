Require Import String.
Require Import Ascii.
Require Import Bool.
Open Scope string_scope.

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
| assign : string -> string -> Stmt
| if_then_else : string -> Stmt -> Stmt -> Stmt
| while_do : string -> Stmt -> Stmt.

Definition is_digit (c : ascii) : bool :=
  match c with
  | "0"%char | "1"%char | "2"%char | "3"%char | "4"%char
  | "5"%char | "6"%char | "7"%char | "8"%char | "9"%char => true
  | _ => false
  end.

Fixpoint string_to_nat_aux (s : string) (acc : nat) : option nat :=
  match s with
  | EmptyString => Some acc
  | String c s' =>
    if is_digit c then
      let digit := nat_of_ascii c - nat_of_ascii "0"%char in
      string_to_nat_aux s' (acc * 10 + digit)
    else None
  end.
Definition is_alpha (c : ascii) : bool :=
  match c with
  | "a"%char | "b"%char | "c"%char | "d"%char | "e"%char | "f"%char | "g"%char
  | "h"%char | "i"%char | "j"%char | "k"%char | "l"%char | "m"%char | "n"%char
  | "o"%char | "p"%char | "q"%char | "r"%char | "s"%char | "t"%char | "u"%char
  | "v"%char | "w"%char | "x"%char | "y"%char | "z"%char
  | "A"%char | "B"%char | "C"%char | "D"%char | "E"%char | "F"%char | "G"%char
  | "H"%char | "I"%char | "J"%char | "K"%char | "L"%char | "M"%char | "N"%char
  | "O"%char | "P"%char | "Q"%char | "R"%char | "S"%char | "T"%char | "U"%char
  | "V"%char | "W"%char | "X"%char | "Y"%char | "Z"%char => true
  | _ => false
  end.

Definition string_to_nat (s : string) : option nat :=
  string_to_nat_aux s 0.

Definition string_tail (s : string) : string :=
  match s with
  | EmptyString => EmptyString
  | String _ rest => rest
  end.

Fixpoint parse_aexp_aux (fuel : nat) (s : string) : option (AExp * string) :=
  match fuel with
  | 0 => None
  | S fuel' =>
      match s with
      | EmptyString => None
      | String c s' =>
          (* If the character is a digit, parse the number *)
          if is_digit c then
              match string_to_nat (String c s') with
              | Some (n, rest) => Some (anum n, rest)  (* Correct usage of anum n *)
              | None => None
              end
          (* If the character is an alphabet, it's a variable *)
          else if is_alpha c then
            Some (avar (String c EmptyString), s')
          (* Otherwise, we check for '(' to start an expression *)
          else match s with
               | String "(" rest =>
                   match parse_aexp_aux fuel' rest with
                   | Some (e1, String "+" rest1) =>
                       (* Parse for addition *)
                       match parse_aexp_aux fuel' rest1 with
                       | Some (e2, String ")" rest2) =>
                           Some (aplus e1 e2, rest2)
                       | _ => None
                       end
                   | Some (e1, String "*" rest1) =>
                       (* Parse for multiplication *)
                       match parse_aexp_aux fuel' rest1 with
                       | Some (e2, String ")" rest2) =>
                           Some (amul e1 e2, rest2)
                       | _ => None
                       end
                   | _ => None
                   end
               | _ => None
               end
      end
  end.

Definition parse_aexp (s : string) : option (AExp * string) :=
  parse_aexp_aux (String.length s) s.


Fixpoint parse_bexp (fuel : nat) (s : string) : option (BExp * string) :=
  match fuel with
  | 0 => None (* Dacă rămânem fără combustibil, ne oprim. *)
  | S fuel' =>
      match s with
      | "" => None
      | String "!"%char rest =>
          match parse_bexp fuel' rest with
          | Some (b, rest') => Some (bnot b, rest')
          | None => None
          end
      | String "t"%char (String "r"%char (String "u"%char (String "e"%char rest))) =>
          Some (btrue, rest)
      | String "f"%char (String "a"%char (String "l"%char (String "s"%char (String "e"%char rest)))) =>
          Some (bfalse, rest)
      | String "(" s' =>
          match parse_bexp fuel' s' with
          | Some (b1, String "&"%char rest) =>
              match parse_bexp fuel' rest with
              | Some (b2, String ")"%char rest') => Some (band b1 b2, rest')
              | _ => None
              end
          | _ => None
          end
      | _ => None
      end
  end.


Fixpoint parse_stmt (fuel : nat) (s : string) : option (Stmt * string) :=
  match fuel with
  | 0 => None (* Out of fuel, stop recursion *)
  | S fuel' =>
      match s with
      | "" => None
      | String "s"%char (String "k"%char (String "i"%char (String "p"%char rest))) =>
          Some (skip, rest)
      | String "(" s' =>
          match parse_stmt fuel' s' with
          | Some (stmt1, String ";"%char rest1) =>
              match parse_stmt fuel' rest1 with
              | Some (stmt2, String ")"%char rest2) =>
                  Some (seq stmt1 stmt2, rest2)
              | _ => None
              end
          | _ => None
          end
      | String "i"%char (String "f"%char rest) =>
          (* Placeholder for "if-then-else" parsing logic *)
          None
      | String "w"%char (String "h"%char (String "i"%char (String "l"%char rest))) =>
          (* Placeholder for "while-do" parsing logic *)
          None
      | _ => None
      end
  end.


Check anum 123.

Compute parse_aexp "123". 
Compute parse_aexp "x".   
Compute parse_aexp "(1+2)". 
Compute parse_aexp "(x*5)". 
Compute parse_aexp "(1+(2*3))". 


Compute parse_bexp 10 "true". 
Compute parse_bexp 10 "false". 
Compute parse_bexp 10 "!(true)". 
Compute parse_bexp 10 "(true&false)". 
Compute parse_bexp 10 "!(x<5)". 

Compute parse_stmt 10 "skip". 
Compute parse_stmt 10 "(skip;skip)". 
Compute parse_stmt 10 "while(x)skip". 
Compute parse_stmt 10 "if(x)skip;skip". 
