(** * XLib: Library, some copied from book Software Foundations *)
(* Andriy LIN, for CS565 Programming Language project *)

(* ---------------------------------------------------------------- *)

(** * From the Coq Standard Library *)

Require Omega.   (* needed for using the [omega] tactic *)
Require Export Bool.
Require Export List.
Export ListNotations.
Require Export Arith.
Require Export Arith.EqNat.  (* Contains [beq_nat], among other things *)

(* ---------------------------------------------------------------- *)
(* Notations, Tactics and Proof techniques *)

Definition admit {T: Type} : T.  Admitted.

Require String. Open Scope string_scope.

Ltac move_to_top x :=
  match reverse goal with
  | H : _ |- _ => try move x after H
  end.

Tactic Notation "assert_eq" ident(x) constr(v) :=
  let H := fresh in
  assert (x = v) as H by reflexivity;
  clear H.

Tactic Notation "Case_aux" ident(x) constr(name) :=
  first [
    set (x := name); move_to_top x
  | assert_eq x name; move_to_top x
  | fail 1 "because we are working on a different case" ].

Tactic Notation "Case" constr(name) := Case_aux Case name.
Tactic Notation "SCase" constr(name) := Case_aux SCase name.
Tactic Notation "SSCase" constr(name) := Case_aux SSCase name.
Tactic Notation "SSSCase" constr(name) := Case_aux SSSCase name.
Tactic Notation "SSSSCase" constr(name) := Case_aux SSSSCase name.
Tactic Notation "SSSSSCase" constr(name) := Case_aux SSSSSCase name.
Tactic Notation "SSSSSSCase" constr(name) := Case_aux SSSSSSCase name.
Tactic Notation "SSSSSSSCase" constr(name) := Case_aux SSSSSSSCase name.


Tactic Notation "solve_by_inversion_step" tactic(t) :=  
  match goal with  
  | H : _ |- _ => solve [ inversion H; subst; t ] 
  end
  || fail "because the goal is not solvable by inversion.".

Tactic Notation "solve" "by" "inversion" "1" :=
  solve_by_inversion_step idtac.
Tactic Notation "solve" "by" "inversion" "2" :=
  solve_by_inversion_step (solve by inversion 1).
Tactic Notation "solve" "by" "inversion" "3" :=
  solve_by_inversion_step (solve by inversion 2).
Tactic Notation "solve" "by" "inversion" :=
  solve by inversion 1.


(* This additional tactic is just to inversion those that are apparently false *)
Ltac invf H := inversion H; subst; clear H.

Ltac inv H := inversion H; subst; clear H.
Ltac rwinv H1 H2 := rewrite H1 in H2; inv H2.
Ltac find_rwinv :=
  match goal with
      H1: ?E = true, H2: ?E = false |- _ => rwinv H1 H2
  end.


Theorem ex_falso_quodlibet:
  forall (P:Prop), False -> P.
Proof.
  intros.
  inversion H.
Qed.


Axiom functional_extensionality :
  forall {X Y: Type} {f g : X -> Y},
    (forall (x: X), f x = g x) -> f = g.

Hint Resolve functional_extensionality.

(* The following axioms are copied from Logic.v in SF book. They might be useful. *)
Axiom double_negation : forall P : Prop, ~~P -> P.
(* Coq complains: double_negation cannot be used as a hint.
Hint Resolve double_negation.
*)

Axiom excluded_middle : forall P : Prop, P \/ ~P.
Hint Resolve excluded_middle.

Axiom de_morgan_not_and_not : forall P Q : Prop, ~(~P /\ ~Q) -> P \/ Q.
Hint Resolve de_morgan_not_and_not.

Axiom implies_to_or : forall P Q : Prop, (P->Q) -> (~P\/Q).
Hint Resolve implies_to_or.


(* ---------------------------------------------------------------- *)
(* For arithmatic & boolean operations *)
Fixpoint ble_nat (n m : nat) : bool :=
  match n with
    | O => true
    | S n' => match m with
                | O => false
                | S m' => ble_nat n' m'
              end
  end.


(* ---------------------------------------------------------------- *)
(* For write buffer & trace *)
Definition hd {X} (l : list X) : option X :=
  match l with
    | nil => None
    | hd :: _ => Some hd
  end.

Fixpoint append {X} (l : list X) (v : X) : list X :=
  match l with
    | nil => [v]
    | h :: t => h :: append t v
  end.

