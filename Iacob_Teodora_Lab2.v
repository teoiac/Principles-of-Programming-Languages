(*Laboratorul 1*)

(*Exercitiul 1 - Definiți un tip de date algebric pentru zilele săptămânii.*)
Inductive Day :=
|Monday
|Tuesday
|Wednesday
|Thursday
|Friday
|Saturday
|Sunday.

(*Exercitiul 2 - Definiti o functie de egalitate peste acest tip de date*)

Definition eq_day (d1 d2 : Day) : bool :=
  match d1, d2 with
    |Monday,Monday => true
    |Tuesday,Tuesday => true
    |Wednesday, Wednesday => true
    |Thursday, Thursday => true
    |Friday, Friday =>true
    |Saturday, Saturday => true
    |Sunday, Sunday => true
    |_,_ => false
end.

Compute eq_day Monday Tuesday.
Compute eq_day Monday Monday.


(*Exercitiul 3 - Definiti o functie care returneaza ziua urmatoare*)

Definition next_day(d: Day) : Day :=
  match d with
    |Monday => Tuesday
    |Tuesday=>Wednesday
    |Wednesday=>Thursday
    |Thursday=>Friday
    |Friday=>Saturday
    |Saturday =>Sunday
    |Sunday=>Monday
end.

Compute next_day Wednesday.

(*Exercitiul 4 - Definiti tipul de date boolean*)

Inductive boolean:=
  |adevarat
  |fals.

(*Exercitiul 5  -  Definiti functiile negatie, conj, disjunctie*)
Definition negatie (b : boolean) : boolean :=
  match b with 
  | adevarat=>fals
  | fals=>adevarat
end.

Compute negatie adevarat.

Definition conjunctie (b1 b2 : boolean) : boolean :=
  match b1, b2 with
  | adevarat, adevarat => adevarat
  | _,_ =>fals
end.

Definition disjunctie (b1 b2 : boolean) : boolean :=
  match b1,b2 with 
  |fals, fals => fals
  |_,_ => adevarat
end.
  
Compute conjunctie fals fals.
Compute disjunctie adevarat fals.
Compute conjunctie fals adevarat.
Compute disjunctie fals fals.

(*Laboratorul 2*)

Inductive Nat := O : Nat 
| S : Nat -> Nat.
Definition one := S O.
Definition two := S one.
Definition three := S two.
Definition four := S three.
Definition five := S four.

Compute five.


(*Exercitiul 7 - Scrieti o functie de egalitate  a doua elemente de tip nat*)

Fixpoint eq_Nat (n m : Nat) :=
 match n, m with
  |O,O =>true
  |S n', S m' => eq_Nat n' m'
  |_,_=>false
end.

Compute eq_Nat O O.
Compute eq_Nat one O.
Compute eq_Nat one one.
Compute eq_Nat one four.
Compute eq_Nat five four.
Compute eq_Nat five five.


(*Exercitiul 8 -  Scrieti o functie recursiva de adunare  peste nat*)

Fixpoint add (m n : Nat) : Nat := 
  match m with 
   | O =>n
   | S k => S (add k n)
  end.

Compute add one one.
Compute add one five.
Compute add five one.
Compute add five O.
Compute add O five.


(*Exercitiul 9 - Scrieti o functie max care returneaza maximul dintre doua elemente de tip Nat*)

Fixpoint max (m n : Nat) : Nat :=
  match m,n with
    |O,_=> n
    |_,O => m
    |S m', S n' => S(max m' n')
end.

Compute max one two.
Compute max O one.
Compute max one O.
Compute max four five.
Compute max five four.











