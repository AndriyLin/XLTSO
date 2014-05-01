(**

This is for the final project of CS565 Programming Languages in
Purdue.

Write a simple programming language that exposes relaxed memory
semantics (e.g. TSO). Prove that data race free programs have SC
semantics.

Written in Coq, mechanically formalized and verified.

Contraints:
* It is only a simple language, so the only possible value is nat.
* If var is not in memory, it will return 0 as default value, rather
  than None.

Xuankang LIN
Last updated: 05/01/2014


Structure:
* Variable
* Memory
* Thread ID
* Locks
* Write Buffer
* Event
* Arithmatic Expression
* Boolean Expression
* Commands & State (uni-thread)
* Threads & Configuration (multi-threads)
* Proof of TSO Semantics
* Sequential Consistency Semantics
* Data-Race-Free
* DRF Guarantee Property
* TODO.. More?
*)

Require Import Coq.Lists.ListSet.
Require Export XLib.


(* ---------------- Var ---------------- *)
(* The variables are all "global" *)
Inductive var : Type :=
| Var : nat -> var.

Hint Constructors var.

Theorem eq_var_dec : forall v1 v2 : var, {v1 = v2} + {v1 <> v2}.
Proof with auto.
  intros.
  destruct v1 as [n1].
  destruct v2 as [n2].
  destruct (eq_nat_dec n1 n2).
  Case "n1 = n2".
    left...
  Case "n2 <> n2".
    right.
    intros Hf.
    apply n.
    inversion Hf...
Defined.

Hint Resolve eq_var_dec.

Lemma eq_var : forall (T : Type) (x : var) (p q : T),
                 (if eq_var_dec x x then p else q) = p.
Proof with auto.
  intros.
  destruct (eq_var_dec x x); try reflexivity.
  apply ex_falso_quodlibet...
Qed.

Hint Resolve eq_var.

Lemma neq_var : forall (T : Type) (x y : var) (p q : T),
                  x <> y -> (if eq_var_dec x y then p else q) = q.
Proof with auto.
  intros.
  destruct (eq_var_dec x y)...
  Case "x = y".
    apply H in e.
    inversion e.
Qed.

Hint Resolve neq_var.

Definition X : var := Var 0.
Definition Y : var := Var 1.
Definition Z : var := Var 2.

Hint Unfold X.
Hint Unfold Y.
Hint Unfold Z.
(* ---------------- end of Var ---------------- *)


(* ---------------- Memory ---------------- *)
Definition memory : Type := var -> nat.

Definition empty_memory : memory := fun _ => 0.

Definition update (mem : memory) (x : var) (n : nat) : memory :=
  fun x' => if eq_var_dec x x' then n else mem x'.

Hint Unfold update.

Theorem update_eq :
  forall n x mem, (update mem x n) x = n.
Proof with auto.
  intros.
  unfold update...
Qed.

Hint Resolve update_eq.

Theorem update_neq :
  forall x2 x1 n mem,
    x2 <> x1 -> (update mem x2 n) x1 = (mem x1).
Proof with auto.
  intros.
  unfold update...
Qed.

Hint Resolve update_neq.

(* Due to most recent assignment, previous assignments are shadowed. *)
Theorem update_shadow :
  forall n1 n2 x1 x2 (mem : memory),
    (update (update mem x2 n1) x2 n2) x1 = (update mem x2 n2) x1.
Proof with auto.
  intros.
  unfold update...
  destruct (eq_var_dec x2 x1)...
Qed.

Hint Resolve update_shadow.

(* Update a variable to its current value won't "actually" change the state *)
Theorem update_same : forall n1 x1 x2 (mem : memory),
                        mem x1 = n1 ->
                        (update mem x1 n1) x2 = mem x2.
Proof with auto.
  intros.
  unfold update...
  destruct (eq_var_dec x1 x2);
    subst...
Qed.

Hint Resolve update_same.

(* The order of update doesn't matter *)
Theorem update_permute :
  forall n1 n2 x1 x2 x3 mem,
    x2 <> x1 -> 
    (update (update mem x2 n1) x1 n2) x3 = (update (update mem x1 n2) x2 n1) x3.
Proof with auto.
  intros.
  unfold update...
  destruct (eq_var_dec x1 x3)...
  Case "x1 = x3".
    destruct (eq_var_dec x2 x3); subst...
    apply ex_falso_quodlibet...
Qed.

Hint Resolve update_permute.
(* ---------------- end of Memory ---------------- *)


(* ---------------- Thread ID ---------------- *)
Inductive tid : Type :=
| TID : nat -> tid.

Hint Constructors tid.

Theorem eq_tid_dec : forall t1 t2 : tid, {t1 = t2} + {t1 <> t2}.
Proof with eauto.
  intros...
  destruct t1 as [n1].
  destruct t2 as [n2].
  destruct (eq_nat_dec n1 n2).
  Case "n1 = n2".
    left...
  Case "n1 <> n2".
    right.
    intros Hf.
    apply n.
    inversion Hf...
Defined.

Hint Resolve eq_tid_dec.

Lemma eq_tid : forall (T : Type) (t : tid) (p q : T),
                 (if eq_tid_dec t t then p else q) = p.
Proof with auto.
  intros.
  destruct (eq_tid_dec t t); try reflexivity.
  apply ex_falso_quodlibet...
Qed.

Hint Resolve eq_tid.

Lemma neq_tid : forall (T : Type) (t1 t2 : tid) (p q : T),
                  t1 <> t2 -> (if eq_tid_dec t1 t2 then p else q) = q.
Proof with auto.
  intros.
  destruct (eq_tid_dec t1 t2)...
  Case "x = y".
    apply H in e.
    inversion e.
Qed.

Hint Resolve neq_tid.

Definition T0 : tid := TID 0.
Definition T1 : tid := TID 1.
Definition T2 : tid := TID 2.

Hint Unfold T0.
Hint Unfold T1.
Hint Unfold T2.


(* The following is to define a set that contains tids of all current threads *)
Definition empty_tids := empty_set tid.

Definition size_tids (tids : set tid) : nat :=
  length tids.

Definition in_tids : tid -> set tid -> bool :=
  set_mem eq_tid_dec.

Definition add_tid : tid -> set tid -> set tid :=
  set_add eq_tid_dec.

Definition remove_tid : tid -> set tid -> set tid :=
  set_remove eq_tid_dec.
(* ---------------- end of Thread ID ---------------- *)


(* ---------------- Lock ---------------- *)
Inductive lid : Type :=
| LockID : nat -> lid.

Hint Constructors lid.

Theorem eq_lid_dec : forall l1 l2 : lid, {l1 = l2} + {l1 <> l2}.
Proof with auto.
  intros.
  destruct l1 as [n1].
  destruct l2 as [n2].
  destruct (eq_nat_dec n1 n2).
  Case "n1 = n2".
    left...
  Case "n2 <> n2".
    right.
    intros Hf.
    apply n.
    inversion Hf...
Defined.

Hint Resolve eq_lid_dec.

Lemma eq_lid : forall (T : Type) (x : lid) (p q : T),
                 (if eq_lid_dec x x then p else q) = p.
Proof with auto.
  intros.
  destruct (eq_lid_dec x x); try reflexivity.
  apply ex_falso_quodlibet...
Qed.

Hint Resolve eq_lid.

Lemma neq_lid : forall (T : Type) (x y : lid) (p q : T),
                  x <> y -> (if eq_lid_dec x y then p else q) = q.
Proof with auto.
  intros.
  destruct (eq_lid_dec x y)...
  Case "x = y".
    apply H in e.
    inversion e.
Qed.

Hint Resolve neq_lid.

Definition L0 : lid := LockID 0.
Definition L1 : lid := LockID 1 .
Definition L2 : lid := LockID 2.

Hint Unfold L0.
Hint Unfold L1.
Hint Unfold L2.


Definition lock_status := lid -> option tid.

Definition empty_locks : lock_status :=
  fun _ => None.

(* Checking of validity is left to semantics, not done here *)
Definition lock (st : lock_status) (t : tid) (l : lid) : lock_status :=
  fun l' => if eq_lid_dec l l' then Some t else st l'.

Hint Unfold lock.

(* Checking of validity is left to semantics, not done here *)
Definition unlock (st : lock_status) (t : tid) (l : lid) : lock_status :=
  fun l' => if eq_lid_dec l l' then None else st l'.

Hint Unfold unlock.


Module TestLocks.

Theorem test_lock_correctness:
  forall st t l, (lock st t l) l = Some t.
Proof with auto.
  intros.
  unfold lock...
Qed.

Theorem test_unlock_correctness:
  forall st t l, st l = Some t -> (unlock st t l) l = None.
Proof with auto.
  intros.
  unfold unlock...
Qed.

End TestLocks.
(* ---------------- end of Lock ---------------- *)


(* ---------------- Write Buffer ---------------- *)
(* In the buffer: [old ... new], new writes are appended to the right *)
Definition buffer : Type := list (var * nat).

(* Add a new write to the end of buffer *)
Definition write (b : buffer) (x : var) (n : nat) : buffer :=
  append b (x, n).

(* get the oldest write in the buffer *)
Definition oldest (b : buffer) : option (var * nat) :=
  hd b.

Hint Unfold oldest.

(* remove the oldest one in the buffer *)
Definition flushone (b : buffer) : buffer :=
  tl b.

Hint Unfold flushone.


(* Get the latest value of some variable in the buffer, if any.
The accumulator version is not useful in proof *)
Fixpoint get (b : buffer) (x : var) : option nat :=
  match b with
    | nil => None
    | (k, v) :: t => match get t x with
                       | None => if eq_var_dec x k
                                 then Some v
                                 else None
                       | r => r
                     end
  end.

Theorem get_deterministic:
  forall b x r1 r2, get b x = r1 ->
                    get b x = r2 ->
                    r1 = r2.
Proof with auto.
  intros b.
  induction b as [ | h t];
    intros.
  Case "b = nil".
    inv H...
  Case "b = h :: t".
    destruct (get t x) eqn:Ht;
      simpl in *.
    destruct h; subst...
    destruct h; subst...
Qed.

Hint Resolve get_deterministic.

Module TestWriteBuffer.

Theorem test_get_correctness:
  forall b x n1 n2, get (write (write b x n1) x n2)  x = Some n2.
Proof with auto.
  intros.
  induction b as [ | h t];
    simpl.
  Case "b = nil".
    rewrite -> eq_var...
  Case "b = h :: t".
    unfold write in IHt.
    rewrite -> IHt.
    destruct h...
Qed.

End TestWriteBuffer.
(* ---------------- end of Write Buffer ---------------- *)


(* ---------------- Event ---------------- *)
(* Events records the "important" actions while moving forward using
small-step semantics *)
Inductive event : Type :=
| EV_Read (x : var)
| EV_Write (x : var) (n : nat)
| EV_Lock (l : lid)
| EV_Unlock (l : lid).

Hint Constructors event.

Tactic Notation "event_cases" tactic(first) ident(c) :=
  first;
  [ Case_aux c "EV_Read" | Case_aux c "EV_Write"
  | Case_aux c "EV_Lock" | Case_aux c "EV_Unlock" ].


Definition trace : Type := list (tid * event).

(* TODO: I currently add event to the beginning, is that the best choice? *)
Definition add_event (tr : trace) (t : tid) (oe : option event) : trace :=
  match oe with
    | Some e => append tr (t, e)
    | None => tr
  end.
(* ---------------- end of Event ---------------- *)


(* ---------------- Arithmatic Expressions ---------------- *)
Inductive aexp : Type :=
| ANum : nat -> aexp
| APlus : aexp -> aexp -> aexp
| AMinus : aexp -> aexp -> aexp
| AMult : aexp -> aexp -> aexp
| AVar : var -> aexp
.

Hint Constructors aexp.

Tactic Notation "aexp_cases" tactic(first) ident(c) :=
  first;
  [ Case_aux c "ANum" | Case_aux c "APlus"
  | Case_aux c "AMinus" | Case_aux c "AMult"
  | Case_aux c "AVar" ].


Inductive avalue : aexp -> Prop :=
| AV_Num : forall n, avalue (ANum n).

Hint Constructors avalue.

(* Note: here the "evt" represents whether this step would incur an event *)
Reserved Notation "a1 '/-' b '~' m '==A>' a2 '[[' evt ']]'" (at level 80).

Inductive astep : buffer -> memory -> aexp -> aexp -> option event -> Prop :=
| AS_Plus : forall b m n1 n2,
              (APlus (ANum n1) (ANum n2)) /- b ~ m ==A> ANum (n1 + n2) [[None]]
| AS_Plus1 : forall b m a1 a1' a2 evt,
               a1 /- b ~ m ==A> a1' [[evt]] ->
               (APlus a1 a2) /- b ~ m ==A> (APlus a1' a2) [[evt]]
| AS_Plus2 : forall b m a1 a2 a2' evt,
               avalue a1 ->
               a2 /- b ~ m ==A> a2' [[evt]] ->
               (APlus a1 a2) /- b ~ m ==A> (APlus a1 a2') [[evt]]

| AS_Minus : forall b m n1 n2,
               AMinus (ANum n1) (ANum n2) /- b ~ m ==A> ANum (n1 - n2) [[None]]
| AS_Minus1 : forall b m a1 a1' a2 evt,
                a1 /- b ~ m ==A> a1' [[evt]] ->
                (AMinus a1 a2) /- b ~ m ==A> (AMinus a1' a2) [[evt]]
| AS_Minus2 : forall b m a1 a2 a2' evt,
                avalue a1 ->
                a2 /- b ~ m ==A> a2' [[evt]] ->
                (AMinus a1 a2) /- b ~ m ==A> (AMinus a1 a2') [[evt]]

| AS_Mult : forall b m n1 n2,
              AMult (ANum n1) (ANum n2) /- b ~ m ==A> ANum (n1 * n2) [[None]]
| AS_Mult1 : forall b m a1 a1' a2 evt,
               a1 /- b ~ m ==A> a1' [[evt]] ->
               (AMult a1 a2) /- b ~ m ==A> (AMult a1' a2) [[evt]]
| AS_Mult2 : forall b m a1 a2 a2' evt,
               avalue a1 ->
               a2 /- b ~ m ==A> a2' [[evt]] ->
               (AMult a1 a2) /- b ~ m ==A> (AMult a1 a2') [[evt]]

| AS_VarBuf : forall b m x n,
                get b x = Some n ->
                (AVar x) /- b ~ m ==A> (ANum n) [[Some (EV_Read x)]]
| AS_VarMem : forall b m x,
                get b x = None ->
                (AVar x) /- b ~ m ==A> ANum (m x) [[Some (EV_Read x)]]

where "a1 '/-' b '~' m '==A>' a2 '[[' evt ']]'" := (astep b m a1 a2 evt).

Hint Constructors astep.

Tactic Notation "astep_cases" tactic(first) ident(c) :=
  first;
  [ Case_aux c "AS_Plus" | Case_aux c "AS_Plus1" | Case_aux c "AS_Plus2"
  | Case_aux c "AS_Minus" | Case_aux c "AS_Minus1" | Case_aux c "AS_Minus2"
  | Case_aux c "AS_Mult" | Case_aux c "AS_Mult1" | Case_aux c "AS_Mult2"
  | Case_aux c "AS_VarBuf" | Case_aux c "AS_VarMem" ].

Theorem strong_progress_a :
  forall a b m, avalue a \/ (exists a' evt, a /- b ~ m ==A> a' [[evt]]).
Proof with eauto.
  intros.
  aexp_cases (induction a) Case;
    simpl...
  Case "APlus".
    right; destruct IHa1...
    destruct IHa2...
    inv H; inv H0...
    inv H0; inv H1...
    inv H; inv H0...
  Case "AMinus".
    right; destruct IHa1...
    destruct IHa2...
    inv H; inv H0...
    inv H0; inv H1...
    inv H; inv H0...
  Case "AMult".
    right; destruct IHa1...
    destruct IHa2...
    inv H; inv H0...
    inv H0; inv H1...
    inv H; inv H0...
  Case "AVar".
    right.
    destruct (get b v) eqn:Hb...
Qed.


Ltac find_astep_contradiction1 :=
  match goal with
      H1: ANum ?n /- ?b ~ ?m ==A> ?ae [[?ev]] |- _ => inversion H1
  end.

Ltac find_astep_contradiction2 :=
  match goal with
      H1: avalue ?a, H2: ?a /- ?b ~ ?m ==A> ?a2 [[?ev]] |- _ => inv H1; invf H2
  end.

Tactic Notation "helper_astep" tactic(t) :=
  inv t; auto;
  try find_astep_contradiction1;
  try find_astep_contradiction2.

Theorem astep_deterministic: forall b m a a1 a2 evt1 evt2,
                               a /- b ~ m ==A> a1 [[evt1]] ->
                               a /- b ~ m ==A> a2 [[evt2]] ->
                               a1 = a2 /\ evt1 = evt2.
Proof with auto.
  intros.
  generalize dependent evt2.
  generalize dependent a2.
  astep_cases (induction H) Case;
    intros.
  Case "AS_Plus".
    helper_astep H0.
  Case "AS_Plus1".
    helper_astep H0.
    destruct (IHastep a1'0 evt2); subst...
  Case "AS_Plus2".
    helper_astep H1.
    destruct (IHastep a2'0 evt2); subst...
  Case "AS_Minus".
    helper_astep H0.
  Case "AS_Minus1".
    helper_astep H0.
    destruct (IHastep a1'0 evt2); subst...
  Case "AS_Minus2".
    helper_astep H1.
    destruct (IHastep a2'0 evt2); subst...
  Case "AS_Mult".
    helper_astep H0.
  Case "AS_Mult1".
    helper_astep H0.
    destruct (IHastep a1'0 evt2); subst...
  Case "AS_Mult2".
    helper_astep H1.
    destruct (IHastep a2'0 evt2); subst...
  Case "AS_VarBuf".
    inv H0.
    assert (Some n = Some n0).
      apply get_deterministic with b x...
    inv H0...
    rewrite -> H in H4; invf H4.
  Case "AS_VarMem".
    inv H0...
    rewrite -> H in H4; invf H4.
Qed.

Hint Resolve astep_deterministic.
(* ---------------- end of Arithmatic Expressions ---------------- *)


(* ---------------- Boolean Expressions ---------------- *)
Inductive bexp : Type :=
| BBool : bool -> bexp
| BNot : bexp -> bexp
| BAnd : bexp -> bexp -> bexp
| BEq : aexp -> aexp -> bexp
| BLe : aexp -> aexp -> bexp
.

Hint Constructors bexp.

Tactic Notation "bexp_cases" tactic(first) ident(c) :=
  first;
  [ Case_aux c "BBool"
  | Case_aux c "BNot" | Case_aux c "BAnd"
  | Case_aux c "BEq" | Case_aux c "BLe" ].


Inductive bvalue : bexp -> Prop :=
| BV_Bool : forall b : bool, bvalue (BBool b).

Hint Constructors bvalue.

(* Note: here the "evt" represents whether this step would incur an event *)
Reserved Notation "b1 '/-' buf '~' mem '==B>' b2 '[[' evt ']]'" (at level 80).

Inductive bstep : buffer -> memory -> bexp -> bexp -> option event -> Prop :=
| BS_Not : forall buf mem b,
             BNot (BBool b) /- buf ~ mem ==B> BBool (negb b) [[None]]
| BS_Not1 : forall buf mem b b' evt,
              b /- buf ~ mem ==B> b' [[evt]] ->
              (BNot b) /- buf ~ mem ==B> BNot b' [[evt]]

| BS_And : forall buf mem b1 b2,
             (BAnd (BBool b1) (BBool b2)) /- buf ~ mem ==B> BBool (andb b1 b2) [[None]]
| BS_And1 : forall buf mem be1 be1' be2 evt,
              be1 /- buf ~ mem ==B> be1' [[evt]] ->
              (BAnd be1 be2) /- buf ~ mem ==B> BAnd be1' be2 [[evt]]
| BS_And2 : forall buf mem be1 be2 be2' evt,
              bvalue be1 ->
              be2 /- buf ~ mem ==B> be2' [[evt]] ->
              (BAnd be1 be2) /- buf ~ mem ==B> BAnd be1 be2' [[evt]]

| BS_Eq : forall buf mem n1 n2,
            (BEq (ANum n1) (ANum n2)) /- buf ~ mem ==B> BBool (beq_nat n1 n2) [[None]]
| BS_Eq1 : forall buf mem a1 a1' a2 evt,
             a1 /- buf ~ mem ==A> a1' [[evt]] ->
             (BEq a1 a2) /- buf ~ mem ==B> BEq a1' a2 [[evt]]
| BS_Eq2 : forall buf mem a1 a2 a2' evt,
             avalue a1 ->
             a2 /- buf ~ mem ==A> a2' [[evt]] ->
             (BEq a1 a2) /- buf ~ mem ==B> BEq a1 a2' [[evt]]

| BS_Le : forall buf mem n1 n2,
            (BLe (ANum n1) (ANum n2)) /- buf ~ mem ==B> BBool (ble_nat n1 n2) [[None]]
| BS_Le1 : forall buf mem a1 a1' a2 evt,
             a1 /- buf ~ mem ==A> a1' [[evt]] ->
             (BLe a1 a2) /- buf ~ mem ==B> BLe a1' a2 [[evt]]
| BS_Le2 : forall buf mem a1 a2 a2' evt,
             avalue a1 ->
             a2 /- buf ~ mem ==A> a2' [[evt]] ->
             (BLe a1 a2) /- buf ~ mem ==B> BLe a1 a2' [[evt]]

where "b1 '/-' buf '~' mem '==B>' b2 '[[' evt ']]'" := (bstep buf mem b1 b2 evt).

Hint Constructors bstep.

Tactic Notation "bstep_cases" tactic(first) ident(c) :=
  first;
  [ Case_aux c "BS_Not" | Case_aux c "BS_Not1"
  | Case_aux c "BS_And" | Case_aux c "BS_And1" | Case_aux c "BS_And2"
  | Case_aux c "BS_Eq" | Case_aux c "BS_Eq1" | Case_aux c "BS_Eq2"
  | Case_aux c "BS_Le" | Case_aux c "BS_Le1" | Case_aux c "BS_Le2" ].

Theorem strong_progress_b :
  forall b buf mem, bvalue b \/ (exists b' evt, b /- buf ~ mem ==B> b' [[evt]]).
Proof with eauto.
  intros.
  bexp_cases (induction b) Case;
    simpl...
  Case "BNot".
    right; destruct IHb.
    inv H...
    inv H; inv H0...
  Case "BAnd".
    right; destruct IHb1.
    destruct IHb2.
    inv H; inv H0...
    inv H0; inv H...
    inv H1...
    inv H; inv H0...
  Case "BEq".
    right; rename a into a1; rename a0 into a2.
    destruct (strong_progress_a a1 buf mem).
    SCase "avalue a1".
      destruct (strong_progress_a a2 buf mem).
      inv H; inv H0...
      inv H0; inv H1...
    SCase "a1 ==A> a1'".
      inv H; inv H0...
  Case "BLe".
    right; rename a into a1; rename a0 into a2.
    destruct (strong_progress_a a1 buf mem).
    SCase "avalue a1".
      destruct (strong_progress_a a2 buf mem).
      inv H; inv H0...
      inv H0; inv H1...
    SCase "a1 ==A> a1'".
      inv H; inv H0...
Qed.


Ltac find_bstep_contradiction1 :=
  match goal with
      H1: BBool ?n /- ?b ~ ?m ==B> ?be [[?ev]] |- _ => inversion H1
  end.

Ltac find_bstep_contradiction2 :=
  match goal with
      H1: bvalue ?b, H2: ?b /- ?buf ~ ?mem ==B> ?b2 [[?ev]] |- _ => inv H1; invf H2
  end.

Tactic Notation "helper_bstep" tactic(t) :=
  inv t; auto;
  try find_astep_contradiction1;
  try find_astep_contradiction2;
  try find_bstep_contradiction1;
  try find_bstep_contradiction2.

Theorem bstep_deterministic:
  forall buf mem b b1 b2 evt1 evt2,
    b /- buf ~ mem ==B> b1 [[evt1]] ->
    b /- buf ~ mem ==B> b2 [[evt2]] ->
    b1 = b2 /\ evt1 = evt2.
Proof with auto.
  intros.
  generalize dependent evt2.
  generalize dependent b2.
  bstep_cases (induction H) Case;
    intros.
  Case "BS_Not".
    helper_bstep H0.
  Case "BS_Not1".
    helper_bstep H0.
    destruct (IHbstep b'0 evt2); subst...
  Case "BS_And".
    helper_bstep H0.
  Case "BS_And1".
    helper_bstep H0.
    destruct (IHbstep be1'0 evt2); subst...
  Case "BS_And2".
    helper_bstep H1.
    destruct (IHbstep be2'0 evt2); subst...
  Case "BS_Eq".
    helper_bstep H0.
  Case "BS_Eq1".
    helper_bstep H0.
    assert (a1' = a1'0 /\ evt = evt2) by eauto.
    inv H0...
  Case "BS_Eq2".
    helper_bstep H1.
    assert (a2' = a2'0 /\ evt = evt2) by eauto.
    inv H1...
  Case "BS_Le".
    helper_bstep H0.
  Case "BS_Le1".
    helper_bstep H0.
    assert (a1' = a1'0 /\ evt = evt2) by eauto.
    inv H0...
  Case "BS_Le2".
    helper_bstep H1.
    assert (a2' = a2'0 /\ evt = evt2) by eauto.
    inv H1...
Qed.

Hint Resolve bstep_deterministic.
(* ---------------- end of Boolean Expressions ---------------- *)


(* ---------------- Command & State (uni) ---------------- *)
Inductive cmd : Type :=
| CSkip : cmd
| CAss : var -> aexp -> cmd
| CSeq : cmd -> cmd -> cmd
| CIf : bexp -> cmd -> cmd -> cmd
| CWhile : bexp -> cmd -> cmd
| CLock : lid -> cmd
| CUnlock : lid -> cmd
.

Hint Constructors cmd.

Tactic Notation "cmd_cases" tactic(first) ident(c) :=
  first;
  [ Case_aux c "SKIP" | Case_aux c "::=" | Case_aux c ";;"
  | Case_aux c "IFB" | Case_aux c "WHILE"
  | Case_aux c "LOCK" | Case_aux c "UNLOCK"
  ].

Notation "'SKIP'" :=
  CSkip.
Notation "x '::=' a" :=
  (CAss x a) (at level 60).
Notation "c1 ;; c2" :=
  (CSeq c1 c2) (at level 80, right associativity).
Notation "'IFB' b 'THEN' c1 'ELSE' c2 'FI'" :=
  (CIf b c1 c2) (at level 80, right associativity).
Notation "'WHILE' b 'DO' c 'END'" :=
  (CWhile b c) (at level 80, right associativity).
Notation "'LOCK' l" :=
  (CLock l) (at level 80).
Notation "'UNLOCK' l" :=
  (CUnlock l) (at level 80).


(* state contains all those ONE single thread can change *)
Record state := ST {
  st_cmd : cmd;
  st_buf : buffer;
  st_mem : memory;
  st_lks : lock_status
}.

Hint Constructors state.


Inductive waiting : tid -> state -> Prop :=
| WaitingLock : forall t t' lks l mem,
                lks l = Some t' ->
                t <> t' ->
                waiting t (ST (LOCK l) nil mem lks)
| WaitingSeq : forall t buf mem lks c1 c2,
               waiting t (ST c1 buf mem lks) ->
               waiting t (ST (c1 ;; c2) buf mem lks)
.

Hint Constructors waiting.

Inductive st_normal_form : tid -> state -> Prop :=
| STV_End : forall t mem lks,
              st_normal_form t (ST SKIP nil mem lks)
| STV_Stuck : forall t st,
                waiting t st ->
                st_normal_form t st
.

Hint Constructors st_normal_form.

(* Note: evt is the event incurred by this step of evaluation *)
Reserved Notation "t '@' st1 '==>' st2 '[[' evt ']]'" (at level 80).

Inductive ststep : tid -> state -> state -> option event -> Prop :=
| ST_Ass : forall t x n buf mem lks,
             t @ (ST (x ::= ANum n) buf mem lks) ==>
               (ST SKIP (write buf x n) mem lks) [[Some (EV_Write x n)]]
| ST_AssStep : forall t x a a' buf mem lks evt,
                 a /- buf ~ mem ==A> a' [[evt]] ->
                 t @ (ST (x ::= a) buf mem lks) ==> (ST (x ::= a') buf mem lks) [[evt]]

| ST_Seq : forall t c2 buf mem lks,
             t @ (ST (SKIP ;; c2) buf mem lks) ==> (ST c2 buf mem lks) [[None]]
| ST_SeqStep : forall t c1 c1' c2 buf mem lks buf' mem' lks' evt,
                 t @ (ST c1 buf mem lks) ==> (ST c1' buf' mem' lks') [[evt]] ->
                 t @ (ST (c1 ;; c2) buf mem lks) ==> (ST (c1' ;; c2) buf' mem' lks') [[evt]]

| ST_IfTrue : forall t c1 c2 buf mem lks,
                t @ (ST (IFB (BBool true) THEN c1 ELSE c2 FI) buf mem lks) ==>
                  (ST c1 buf mem lks) [[None]]
| ST_IfFalse : forall t c1 c2 buf mem lks,
                 t @ (ST (IFB (BBool false) THEN c1 ELSE c2 FI) buf mem lks) ==>
                   (ST c2 buf mem lks) [[None]]
| ST_IfStep : forall t c1 c2 be be' buf mem lks evt,
                be /- buf ~ mem ==B> be' [[evt]] ->
                t @ (ST (IFB be THEN c1 ELSE c2 FI) buf mem lks) ==>
                  (ST (IFB be' THEN c1 ELSE c2 FI) buf mem lks) [[evt]]

| ST_While : forall t b c buf mem lks,
               t @ (ST (WHILE b DO c END) buf mem lks) ==>
                 (ST (IFB b THEN (c ;; (WHILE b DO c END)) ELSE SKIP FI) buf mem lks) [[None]]

| ST_FlushOne : forall t buf mem lks x n c,
                  (* Here it's defined as "it can flush no matter blocked or not" *)
                  oldest buf = Some (x, n) ->
                  t @ (ST c buf mem lks) ==> (ST c (flushone buf) (update mem x n) lks)
                    [[None]]

(* to LOCK, buffer must be empty *)
| ST_Lock : forall t mem lks lk,
              lks lk = None ->
              t @ (ST (LOCK lk) nil mem lks) ==>
                (ST SKIP nil mem (lock lks t lk)) [[Some (EV_Lock lk)]]
| ST_LockAgain : forall t mem lks lk,
                   lks lk = Some t ->
                   t @ (ST (LOCK lk) nil mem lks) ==> (ST SKIP nil mem lks) [[None]]

(* to UNLOCK, buffer must be empty *)
| ST_Unlock : forall t mem lks lk,
                lks lk = Some t ->
                t @ (ST (UNLOCK lk) nil mem lks) ==>
                  (ST SKIP nil mem (unlock lks t lk)) [[Some (EV_Unlock lk)]]
| ST_UnlockNil : forall t mem lks lk,
                   lks lk = None ->
                   t @ (ST (UNLOCK lk) nil mem lks) ==> (ST SKIP nil mem lks) [[None]]
| ST_UnlockOthers : forall t t' mem lks lk,
                      lks lk = Some t' ->
                      t <> t' ->
                      t @ (ST (UNLOCK lk) nil mem lks) ==> (ST SKIP nil mem lks) [[None]]


where "t1 '@' st1 '==>' st2 '[[' evt ']]'" := (ststep t1 st1 st2 evt).

Hint Constructors ststep.

Tactic Notation "ststep_cases" tactic(first) ident(c) :=
  first;
  [ Case_aux c "ST_Ass" | Case_aux c "ST_AssStep"
  | Case_aux c "ST_Seq" | Case_aux c "ST_SeqStep"
  | Case_aux c "ST_IfTrue" | Case_aux c "ST_IfFalse"
  | Case_aux c "ST_IfStep" | Case_aux c "ST_While"
  | Case_aux c "ST_FlushOne" | Case_aux c "ST_Lock"
  | Case_aux c "ST_LockAgain" | Case_aux c "ST_Unlock"
  | Case_aux c "ST_UnlockNil" | Case_aux c "ST_UnlockOthers"
  ].


Theorem strong_progress_st :
  forall c buf mem lks t,
    st_normal_form t (ST c buf mem lks) \/
    (exists st' evt, t @ (ST c buf mem lks) ==> st' [[evt]]).
Proof with eauto.
  intros c.
  cmd_cases (induction c) Case;
    intros; simpl...
  Case "SKIP".
    destruct buf...
    right.
    destruct p.
    exists (ST SKIP buf (update mem v n) lks); exists None...
    apply ST_FlushOne...
  Case "::=".
    right; destruct (strong_progress_a a buf mem)...
    inv H...
    inv H; inv H0...
  Case ";;".
    destruct (IHc1 buf mem lks t).
    inv H...
    right; inv H; inv H0...
    destruct x...
  Case "IFB".
    right; destruct (strong_progress_b b buf mem)...
    inv H; destruct b0...
    inv H; inv H0...
  Case "LOCK".
    destruct buf.
    SCase "empty buffer".
      destruct (lks l) eqn:Hl.
      destruct (eq_tid_dec t t0); subst...
      right...
    SCase "non-empty buffer".
      right; destruct p.
      eexists; eexists.
      apply ST_FlushOne.
      simpl...
  Case "UNLOCK".
    destruct buf...
    SCase "empty buffer".
      right; destruct (lks l) eqn:Hl...
      destruct (eq_tid_dec t t0); subst...
    SCase "non-empty buffer".
      right; destruct p.
      eexists; eexists.
      apply ST_FlushOne...
      simpl...
Qed.


(* When a thread get stuck, it can resume when that lock is released *)
Theorem thread_stuck_resume:
  forall t l buf mem lks lks',
    st_normal_form t (ST (LOCK l) buf mem lks) ->
    lks' l = None \/ lks' l = Some t ->
    exists st' evt, t @ (ST (LOCK l) buf mem lks') ==> st' [[evt]].
Proof.
  intros.
  inv H.
  inv H1.
  inv H0.
  Case "no one holding the lock".
    eexists; eexists.
    apply ST_Lock; assumption.
  Case "self holding the lock".
    eexists; eexists.
    apply ST_LockAgain; assumption.
Qed.


(* ststep is no longer deterministic, one state may execute one
command, it may also flush one unit of its write buffer to memory *)
Theorem ststep_not_deterministic:
  ~ (forall t st st1 st2 evt1 evt2,
       t @ st ==> st1 [[evt1]] ->
       t @ st ==> st2 [[evt2]] ->
       st1 = st2 /\ evt1 = evt2).
Proof with auto.
  intros Hf.
  remember (SKIP ;; SKIP) as c.
  remember ([(X, 100)]) as buf.
  remember (ST c buf empty_memory empty_locks) as st.
  remember (ST SKIP buf empty_memory empty_locks) as st1.
  remember (ST c nil (update empty_memory X 100) empty_locks) as st2.
  remember (None : option event) as evt1.
  remember (None : option event) as evt2.
  assert (T0 @ st ==> st1 [[evt1]]).
    subst...
  assert (T0 @ st ==> st2 [[evt2]]).
    subst.
    apply ST_FlushOne.
    simpl...
  assert (st1 = st2).
    eapply Hf.
    apply H.
    apply H0.
  subst.
  clear H H0.
  inv H1.
Qed.
(* ---------------- end of Command & State (uni) ---------------- *)


(* ---------------- Threads & Configuration ---------------- *)
(* Only Command and Write Buffer is thread private *)
Definition threads := tid -> (cmd * buffer).

Definition empty_threads : threads :=
  fun _ => (SKIP, nil).

Hint Unfold empty_threads.

Definition override (ts: threads) (t : tid) (c : cmd) (b : buffer) :=
  fun t' => if eq_tid_dec t t'
            then (c, b)
            else ts t'.

Hint Unfold override.


(* configuration contains everything that may be modified, for all threads *)
Record configuration := CFG {
  cfg_tids : set tid;
  cfg_thds : threads;
  cfg_mem : memory;
  cfg_lks : lock_status;
  cfg_evts : trace
}.

Hint Constructors configuration.

Definition empty_configuration :=
  CFG empty_tids empty_threads empty_memory empty_locks nil.


Inductive cfg_normal_form : configuration -> Prop :=
(* All threads finish *)
| CFGV_End : forall thds mem lks evts,
               cfg_normal_form (CFG empty_tids thds mem lks evts)
(* Deadlock *)
| CFGV_Deadlock: forall tids thds mem lks evts,
                   (forall t c b, in_tids t tids = true ->
                                  thds t = (c, b) ->
                                  waiting t (ST c b mem lks)) ->
                   cfg_normal_form (CFG tids thds mem lks evts)
.

Hint Constructors cfg_normal_form.

Reserved Notation "cfg1 '-->' cfg2" (at level 60).

Inductive cfgstep : configuration -> configuration -> Prop :=
(* One thread already ends its job, thus remove it *)
| CFGS_Done : forall t tids thds mem lks evts,
                in_tids t tids = true ->
                thds t = (SKIP, nil) ->
                (CFG tids thds mem lks evts) --> (CFG (remove_tid t tids) thds mem lks evts)

(* One thread can move one step forward, in terms of "state" *)
| CFGS_One : forall t tids thds c c' b b' mem mem' lks lks' evt trace,
               in_tids t tids = true ->
               thds t = (c, b) ->
               t @ (ST c b mem lks) ==> (ST c' b' mem' lks') [[evt]] ->
               (CFG tids thds mem lks trace) -->
                 (CFG tids (override thds t c' b') mem' lks' (add_event trace t evt))

where "cfg1 '-->' cfg2" := (cfgstep cfg1 cfg2).

Hint Constructors cfgstep.

Tactic Notation "cfgstep_cases" tactic(first) ident(c) :=
  first;
  [ Case_aux c "CFGS_Done" | Case_aux c "CFGS_One" ].


(* used in init_cfg() *)
Fixpoint _init_cfg (lc : list cmd) (n : nat) (accu : configuration) : configuration :=
  match lc with
    | nil => accu
    | h :: tlc =>
      match accu with
        | CFG tids thds mem lks trace =>
          let t := TID n in
          let accu' := CFG (add_tid t tids) (override thds t h nil) mem lks trace in
          _init_cfg tlc (S n) accu'
      end
  end.

(* init_cfg is a function used to generate the initial configuration
from a list of commands *)
Definition init_cfg (lc : list cmd) : configuration :=
  _init_cfg lc 0 empty_configuration.

Hint Unfold init_cfg.


Definition multicfgstep := multi cfgstep.
Notation "cfg1 '-->*' cfg2" := (multicfgstep cfg1 cfg2) (at level 40).

(* All above are the definitions for the parallel language *)
(* ---------------- end of Threads & Configuration ---------------- *)


(* ---------------- Proof of having TSO Semantics ---------------- *)
Module TsoSemanticsProof.

(* Below is the example in P393 of paper "A Better x86 Memory Model: x86-TSO":

  n6:
          |      proc0      |      proc1
  poi: 0  |  MOV [X] <- $1  |  MOV [Y] <- $2
  poi: 1  |  MOV EAX <- [X] |  MOV [X] <- $2
  poi: 2  |  MOV EBX <- [Y] |

  Final: EAX = 1 /\ EBX = 0 /\ [X] = 1

  TSO allows this final result, so proving that the final situation is
  reachable should prove that the language exposes TSO semantics.
*)
Definition EAX : var := Var 100.
Definition EBX : var := Var 101.

Definition proc0 : cmd :=
  X ::= ANum 1 ;;
  EAX ::= AVar X ;;
  EBX ::= AVar Y.

Definition proc1 : cmd :=
  Y ::= ANum 2 ;;
  X ::= ANum 2.

Definition codes : list cmd :=
  proc0 :: proc1 :: nil.

(* The following is to prove that the init_cfg function works as expected *)
Example preprocess:
  forall tids thds mem lks trace,
    init_cfg codes = (CFG tids thds mem lks trace) ->
    size_tids tids = 2 /\ in_tids T0 tids = true /\ in_tids T1 tids = true
    /\ thds T0 = (proc0, nil) /\ thds T1 = (proc1, nil) /\ trace = nil.
Proof.
  intros.
  unfold codes, proc0, proc1, init_cfg in *.
  inv H.
  split; auto.
Qed.

(* The following is to prove that the final state is actually
reachable by the language and semantics I defined above *)
Theorem tso_semantics:
  exists thds mem lks trace,
    init_cfg codes -->* (CFG empty_tids thds mem lks trace) /\
    cfg_normal_form (CFG empty_tids thds mem lks trace) /\ (* final state *)
    mem EAX = 1 /\ mem EBX = 0 /\ mem X = 1.
Proof with eauto.
  eexists.
  eexists.
  eexists.
  eexists.
  split.

  (* proc1: write of Y := 2 is buffered *)
  eapply multi_step.
  apply CFGS_One with (t := T1) (c := proc1) (b := nil)...
  unfold proc1...
  eapply multi_step.
  apply CFGS_One with (t := T1) (c := (SKIP;; X ::= (ANum 2))) (b := [(Y, 2)])...

  (* proc0: write of X := 1 is buffered *)
  eapply multi_step.
  apply CFGS_One with (t := T0) (c := proc0) (b := nil)...
  unfold proc0...
  eapply multi_step.
  apply CFGS_One with (t := T0) (c := (SKIP;; EAX ::= (AVar X) ;; (EBX ::= (AVar Y)))) (b := [(X, 1)])...

  (* proc0: read EAX := X from write buffer *)
  eapply multi_step.
  apply CFGS_One with (t := T0) (c := (EAX ::= (AVar X) ;; (EBX ::= (AVar Y)))) (b := [(X, 1)])...
  constructor.
  constructor.
  constructor.
  reflexivity.
  eapply multi_step.
  apply CFGS_One with (t := T0) (c := (EAX ::= (ANum 1);; (EBX ::= (AVar Y)))) (b := [(X, 1)])...
  eapply multi_step.
  apply CFGS_One with (t := T0) (c := (SKIP;; (EBX ::= (AVar Y)))) (b := [(X, 1); (EAX, 1)])...

  (* proc0: read EBX := Y from memory *)
  eapply multi_step.
  apply CFGS_One with (t := T0) (c := (EBX ::= (AVar Y))) (b := [(X, 1); (EAX, 1)])...
  eapply multi_step.
  apply CFGS_One with (t := T0) (c := (EBX ::= (ANum 0))) (b := [(X, 1); (EAX, 1)])...
  (* after this, proc0: c := SKIP, b := (X, 1) :: (EAX, 1) :: (EBX, 0) :: nil *)

  (* proc1: write of X := 2 buffered *)
  eapply multi_step.
  apply CFGS_One with (t := T1) (c := (X ::= (ANum 2))) (b := [(Y, 2)])...
  (* after this, proc1: c := SKIP, b := (Y, 2) :: (X, 2) :: nil *)

  (* proc1: flushes write Y := 2 to memory *)
  eapply multi_step.
  apply CFGS_One with (t := T1) (c := SKIP) (b := [(Y, 2); (X, 2)])...
  constructor.
  simpl...

  (* proc1: flushes write X := 2 to memory *)
  eapply multi_step.
  apply CFGS_One with (t := T1) (c := SKIP) (b := [(X, 2)])...
  constructor.
  simpl...

  (* proc1: done *)
  eapply multi_step.
  apply CFGS_Done with (t := T1)...

  (* proc0: flushes write X := 1 to memory *)
  eapply multi_step.
  apply CFGS_One with (t := T0) (c := SKIP) (b := [(X, 1); (EAX, 1); (EBX, 0)])...
  constructor.
  simpl...

  (* proc0: flushes all else in the write buffer to memory *)
  eapply multi_step.
  apply CFGS_One with (t := T0) (c := SKIP) (b := [(EAX, 1); (EBX, 0)])...
  constructor.
  simpl...
  eapply multi_step.
  apply CFGS_One with (t := T0) (c := SKIP) (b := [(EBX, 0)])...
  constructor.
  simpl...

  (* proc0: done *)
  eapply multi_step.
  apply CFGS_Done with (t := T0)...

  (* DONE, now the final state is: EAX = 1 /\ EBX = 0 /\ X = 1 *)
  apply multi_refl.
  simpl in *.
  auto.
Qed.

End TsoSemanticsProof.
(* ---------------- end of Proof of having TSO Semantics ---------------- *)


(* ---------------- Sequential Consistency Semantics ---------------- *)
(* Note: The following is the sequential semantics (without write
buffers).  Buffer is still declared in state for consistency with TSO,
but is as always nil in semantics. *)
Reserved Notation "t '@' st1 '==SC>' st2 '[[' evt ']]'" (at level 80).

Inductive sc : tid -> state -> state -> option event -> Prop :=
| SC_Ass : forall t x n mem lks,
             t @ (ST (x ::= ANum n) nil mem lks) ==SC>
                 (ST SKIP nil (update mem x n) lks) [[Some (EV_Write x n)]]
| SC_AssStep : forall t x a a' mem lks evt,
                 a /- nil ~ mem ==A> a' [[evt]] ->
                 t @ (ST (x ::= a) nil mem lks) ==SC> (ST (x ::= a') nil mem lks) [[evt]]

| SC_Seq : forall t c2 mem lks,
             t @ (ST (SKIP ;; c2) nil mem lks) ==SC> (ST c2 nil mem lks) [[None]]
| SC_SeqStep : forall t c1 c1' c2 mem lks mem' lks' evt,
                 t @ (ST c1 nil mem lks) ==SC> (ST c1' nil mem' lks') [[evt]] ->
                 t @ (ST (c1 ;; c2) nil mem lks) ==SC> (ST (c1' ;; c2) nil mem' lks') [[evt]]

| SC_IfTrue : forall t c1 c2 mem lks,
                t @ (ST (IFB (BBool true) THEN c1 ELSE c2 FI) nil mem lks) ==SC>
                    (ST c1 nil mem lks) [[None]]
| SC_IfFalse : forall t c1 c2 mem lks,
                 t @ (ST (IFB (BBool false) THEN c1 ELSE c2 FI) nil mem lks) ==SC>
                     (ST c2 nil mem lks) [[None]]
| SC_IfStep : forall t c1 c2 be be' mem lks evt,
                be /- nil ~ mem ==B> be' [[evt]] ->
                t @ (ST (IFB be THEN c1 ELSE c2 FI) nil mem lks) ==SC>
                    (ST (IFB be' THEN c1 ELSE c2 FI) nil mem lks) [[evt]]

| SC_While : forall t b c mem lks,
               t @ (ST (WHILE b DO c END) nil mem lks) ==SC>
                   (ST (IFB b THEN (c ;; (WHILE b DO c END)) ELSE SKIP FI)
                       nil mem lks) [[None]]

(* The following rules are the same as TSO *)
| SC_Lock : forall t mem lks lk,
              lks lk = None ->
              t @ (ST (LOCK lk) nil mem lks) ==SC>
                (ST SKIP nil mem (lock lks t lk)) [[Some (EV_Lock lk)]]
| SC_LockAgain : forall t mem lks lk,
                   lks lk = Some t ->
                   t @ (ST (LOCK lk) nil mem lks) ==SC> (ST SKIP nil mem lks) [[None]]

| SC_Unlock : forall t mem lks lk,
                lks lk = Some t ->
                t @ (ST (UNLOCK lk) nil mem lks) ==SC>
                  (ST SKIP nil mem (unlock lks t lk)) [[Some (EV_Unlock lk)]]
| SC_UnlockNil : forall t mem lks lk,
                   lks lk = None ->
                   t @ (ST (UNLOCK lk) nil mem lks) ==SC> (ST SKIP nil mem lks) [[None]]
| SC_UnlockOthers : forall t t' mem lks lk,
                      lks lk = Some t' ->
                      t <> t' ->
                      t @ (ST (UNLOCK lk) nil mem lks) ==SC> (ST SKIP nil mem lks) [[None]]


where "t1 '@' st1 '==SC>' st2 '[[' evt ']]'" := (sc t1 st1 st2 evt).

Hint Constructors sc.

Tactic Notation "sc_cases" tactic(first) ident(c) :=
  first;
  [ Case_aux c "SC_Ass" | Case_aux c "SC_AssStep"
  | Case_aux c "SC_Seq" | Case_aux c "SC_SeqStep"
  | Case_aux c "SC_IfTrue" | Case_aux c "SC_IfFalse"
  | Case_aux c "SC_IfStep" | Case_aux c "SC_While"
  | Case_aux c "SC_Lock" | Case_aux c "SC_LockAgain"
  | Case_aux c "SC_Unlock" | Case_aux c "SC_UnlockNil" | Case_aux c "SC_UnlockOthers"
  ].


Lemma sc_no_buffer : forall t c c' buf' mem mem' lks lks' evt,
                       t @ (ST c nil mem lks) ==SC> (ST c' buf' mem' lks') [[evt]] ->
                       buf' = nil.
Proof with eauto.
  intros.
  inv H...
Qed.

Hint Resolve sc_no_buffer.

Theorem strong_progress_sc :
  forall c mem lks t,
    st_normal_form t (ST c nil mem lks) \/
    (exists st' evt, t @ (ST c nil mem lks) ==SC> st' [[evt]]).
Proof with eauto.
  intros c.
  cmd_cases (induction c) Case;
    intros; simpl...
  Case "::=".
    right; destruct (strong_progress_a a nil mem)...
    inv H...
    inv H; inv H0...
  Case ";;".
    destruct (IHc1 mem lks t).
    inv H...
    right; inv H; inv H0...
    destruct x as [c1' buf' mem' lks'].
    assert (buf' = nil) by eauto.
    subst...
  Case "IFB".
    right; destruct (strong_progress_b b nil mem)...
    inv H; destruct b0...
    inv H; inv H0...
  Case "LOCK".
    destruct (lks l) eqn:Hl.
    destruct (eq_tid_dec t t0); subst...
    right...
  Case "UNLOCK".
    right; destruct (lks l) eqn:Hl...
    destruct (eq_tid_dec t t0); subst...
Qed.


(* Unlike TSO, SC (without write buffers) should be deterministic *)
Theorem sc_deterministic:
  forall t st st1 st2 evt1 evt2,
    t @ st ==SC> st1 [[evt1]] ->
    t @ st ==SC> st2 [[evt2]] ->
    st1 = st2 /\ evt1 = evt2.
Proof with eauto.
  intros.
  generalize dependent evt2.
  generalize dependent st2.
  sc_cases (induction H) Case;
    intros st2 evt2 H2.
  Case "SC_Ass".
    helper_astep H2.
  Case "SC_AssStep".
    (* use helper_bstep just because it contains all tactics I have defined.. *)
    helper_bstep H2.
    assert (a' = a'0 /\ evt = evt2) by eauto.
    inv H0...
  Case "SC_Seq".
    helper_bstep H2...
    inv H7.
  Case "SC_SeqStep".
    helper_bstep H2.
    inv H.
    apply IHsc in H8.
    inv H8...
    inv H0...
  Case "SC_IfTrue".
    helper_bstep H2.
  Case "SC_IfFalse".
    helper_bstep H2.
  Case "SC_IfStep".
    helper_bstep H2.
    assert (be' = be'0 /\ evt = evt2) by eauto.
    inv H0...
  Case "SC_While".
    inv H2...
  Case "SC_Lock".
    inv H2...
    rewrite -> H in H7; invf H7.
  Case "SC_LockAgain".
    inv H2...
    rewrite -> H in H7; invf H7.
  Case "SC_Unlock".
    inv H2...
    rewrite -> H in H7; invf H7.
    rewrite -> H in H7; invf H7.
    assert (t' = t') as Hf by auto; apply H8 in Hf; invf Hf.
  Case "SC_UnlockNil".
    inv H2...
    rewrite -> H in H7; invf H7.
  Case "SC_UnlockOthers".
    inv H2...
    rewrite -> H in H8; invf H8.
    assert (t = t) as Hf by auto; apply H0 in Hf; invf Hf.
Qed.


Reserved Notation "cfg1 '--SC>' cfg2" (at level 60).

Inductive cfgsc : configuration -> configuration -> Prop :=
(* One thread already ends its job, thus remove it *)
| CFGSC_Done : forall t tids thds mem lks evts,
                 in_tids t tids = true ->
                 thds t = (SKIP, nil) ->
                 (CFG tids thds mem lks evts) --SC> (CFG (remove_tid t tids) thds mem lks evts)

(* One thread can move one step forward, in terms of "state" *)
| CFGSC_One : forall t tids thds c c' mem mem' lks lks' evt trace,
                in_tids t tids = true ->
                thds t = (c, nil) ->
                t @ (ST c nil mem lks) ==SC> (ST c' nil mem' lks') [[evt]] ->
                (CFG tids thds mem lks trace) --SC>
                  (CFG tids (override thds t c' nil) mem' lks' (add_event trace t evt))

where "cfg1 '--SC>' cfg2" := (cfgsc cfg1 cfg2).

Hint Constructors cfgsc.

Tactic Notation "cfgsc_cases" tactic(first) ident(c) :=
  first;
  [ Case_aux c "CFGSC_Done" | Case_aux c "CFGSC_One" ].

Definition multicfgsc := multi cfgsc.
Notation "cfg1 '--SC>*' cfg2" := (multicfgsc cfg1 cfg2) (at level 40).
(* ---------------- end of Sequential Consistency Semantics ---------------- *)


(* ---------------- Data-Race-Free ---------------- *)
(* The command determines whether "writes c x" is provable, so just
assign the most basic context. *)
Inductive writes : cmd -> var -> Prop :=
| Writes : forall c st' x n,
             T0 @ (ST c nil empty_memory empty_locks) ==SC> st' [[Some (EV_Write x n)]] ->
             writes c x
.

Hint Constructors writes.


(* The command determines whether "reads c x" is provable, so just
assign the most basic context. *)
Inductive reads : cmd -> var -> Prop :=
| Reads : forall c st' x,
            T0 @ (ST c nil empty_memory empty_locks) ==SC> st' [[Some (EV_Read x)]] ->
            reads c x
.

Hint Constructors reads.


Module TestWritesReads.

Example test_writes1 : writes (X ::= ANum 10) X.
Proof. eauto. Qed.

Example test_writes2 : ~ writes (SKIP ;; X ::= ANum 10) X.
Proof.
  intros Hf.
  inv Hf.
  inv H.
  inv H7.
Qed.

Example test_read1 : reads (IFB (BEq (ANum 10) (AVar X)) THEN SKIP ELSE SKIP FI) X.
Proof. eauto. Qed.

Example test_read2 : ~ reads (IFB (BEq (AVar Y) (AVar X)) THEN SKIP ELSE SKIP FI) X.
Proof.
  intros Hf.
  inv Hf.
  inv H.
  inv H8.
  inv H5.
  inv H6.
  inv H2.
  inv H3.
Qed.

End TestWritesReads.


Definition uses (c : cmd) (x : var) : Prop :=
  writes c x \/ reads c x.

Hint Unfold uses.


Inductive datarace : cmd -> cmd -> Prop :=
| DataRaceL : forall c1 c2 x,
                writes c1 x ->
                uses c2 x ->
                datarace c1 c2
| DataRaceR : forall c1 c2 x,
                writes c2 x ->
                uses c1 x ->
                datarace c1 c2
.

Hint Constructors datarace.

(* Note: DRF must be under SC semantics *)
Definition data_race_free (cfg : configuration) : Prop :=
  ~ (exists tids thds mem lks t1 t2 trc,
       cfg --SC>* (CFG tids thds mem lks trc)
       /\ in_tids t1 tids = true
       /\ in_tids t2 tids = true
       /\ t1 <> t2
       /\ datarace (fst (thds t1)) (fst (thds t2))
    ).


Theorem drf_preservation :
  forall cfg1 cfg2, data_race_free cfg1 ->
                    cfg1 --SC>* cfg2 ->
                    data_race_free cfg2.
Proof with eauto.
  intros cfg1 cfg2 Hdrf H.
  multi_cases (induction H) Case...
  Case "multi_step".
  apply IHmulti.
  intros Hf.
  apply Hdrf.
  inversion Hf as [tids]; clear Hf.
  inversion H1 as [thds]; clear H1.
  inversion H2 as [mem]; clear H2.
  inversion H1 as [lks]; clear H1.
  inversion H2 as [t1]; clear H2.
  inversion H1 as [t2]; clear H1.
  inversion H2 as [trc]; clear H2.
  inv H1.

  exists tids; exists thds; exists mem; exists lks;
  exists t1; exists t2; exists trc.
  split...

  apply multi_step with y...
Qed.

Hint Resolve drf_preservation.
(* ---------------- end of Data-Race-Free ---------------- *)


(* ---------------- DRF Guarantee Property ---------------- *)
(* This section is to prove that "data race free programs have SC semantics" *)

(* I find it hard to write down the theorems using my current data structures,
so I have to refine my definitions first. *)

(* data-race is defined on 2 commands. Because events must have a
order between them, so conflicts should be defined in terms of
events. but has the same meaning as data-race.  *)

(* TODO:
1. change "Some EVENT" to "EVENT" which also contains an event NONE
2. each configuration smallstep returns (tid * event)
3. configuration multi-step collects such (tid * event) into a list
*)

Theorem diamond :
  cfg0 --> cfg1 with t1 ~ evt1 ->
  cfg1 --> cfg2 with t2 ~ evt2 ->
  t1 <> t2 ->
  no conflict(data-race) between evt1 and evt2 ->
  exists cfg1', cfg0 --> cfg1' with t2 ~ evt2 /\
                cfg1' --> cfg2 with t1 ~ evt1.


Theorem drf_must_have_unlock :
  cfg -->* cfg' with a list of evts ->
  in that list, (t1, evt1) < (t2, evt2) ->
  evt1 and evt2 have data-race ->
  exists (t1, unlock) between (t1, evt1) and (t2, evt2) in the list.
(* Gustavo didn't prove this, so he's not sure about the difficulty,
if hard, make this an axiom. *)


Inductive flattening : configuration -> configuration -> Prop :=
(* flush out all buffers *)
.

Inductive simulation : configuration -> configuration -> configuration -> Prop :=
| Simulation : forall c0 ctso csc,
                 c0 -->* ctso ->
                 c0 --SC>* csc ->
                 flattening ctso csc ->
                 simulation c0 ctso csc
.

Theorem drf_guarantee :
  forall c0 ctso,
    data_race_free c0 ->
    c0 -->* ctso ->
    exists csc, simulation c0 ctso csc.

(* ---------------- end of DRF Guarantee Property ---------------- *)

