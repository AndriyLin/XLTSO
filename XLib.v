(** * XLib: Library, mostly copied from book Software Foundations *)
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
(* For write buffer *)
Definition hd {X} (l : list X) : option X :=
  match l with
    | nil => None
    | hd :: _ => Some hd
  end.


(* ---------------------------------------------------------------- *)
(* For small step semantics *)
Definition relation (X:Type) := X -> X -> Prop.

Definition deterministic {X: Type} (R: relation X) :=
  forall x y1 y2 : X, R x y1 -> R x y2 -> y1 = y2.

Hint Unfold deterministic.

Inductive multi (X:Type) (R: relation X) : X -> X -> Prop :=
| multi_refl  : forall (x : X),
                  multi X R x x
| multi_step : forall (x y z : X),
                 R x y ->
                 multi X R y z ->
                 multi X R x z.

Implicit Arguments multi [[X]].

Hint Constructors multi.

Tactic Notation "multi_cases" tactic(first) ident(c) :=
  first;
  [ Case_aux c "multi_refl" | Case_aux c "multi_step" ].

Theorem multi_R : forall (X:Type) (R:relation X) (x y : X),
                    R x y -> multi R x y.
Proof. eauto. Qed.

Hint Resolve multi_R.

Theorem multi_trans :
  forall (X:Type) (R: relation X) (x y z : X),
      multi R x y  ->
      multi R y z ->
      multi R x z.
Proof.
  intros X R x y z Hxy Hyz.
  multi_cases (induction Hxy) Case;
    simpl; eauto.
Qed.

Hint Resolve multi_trans.

