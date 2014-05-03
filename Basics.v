(* Basics.v defines basic data structures and related theorems for
further definitions and proofs.

Table of Contents:
1. Var
2. Memory
3. Thread ID
4. Lock
5. Write Buffer
6. Event
7. Arithmatic Expression
8. Boolean Expression
9. Command & Threads
10. State & Configuration
*)

Require Import Coq.Lists.ListSet.
Require Import XLib.

(* ---------------- 1. Var ---------------- *)
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
(* ---------------- end of 1. Var ---------------- *)


(* ---------------- 2. Memory ---------------- *)
Definition memory : Type := var -> nat.

Definition empty_memory : memory := fun _ => 0.

Definition mem_update (mem : memory) (x : var) (n : nat) : memory :=
  fun x' => if eq_var_dec x x' then n else mem x'.

Hint Unfold mem_update.

Theorem mem_update_eq :
  forall n x mem, (mem_update mem x n) x = n.
Proof with auto.
  intros.
  unfold mem_update...
Qed.

Hint Resolve mem_update_eq.

Theorem mem_update_neq :
  forall x2 x1 n mem,
    x2 <> x1 -> (mem_update mem x2 n) x1 = (mem x1).
Proof with auto.
  intros.
  unfold mem_update...
Qed.

Hint Resolve mem_update_neq.

(* Due to most recent assignment, previous assignments are shadowed. *)
Theorem mem_update_shadow :
  forall n1 n2 x1 x2 (mem : memory),
    (mem_update (mem_update mem x2 n1) x2 n2) x1 = (mem_update mem x2 n2) x1.
Proof with auto.
  intros.
  unfold mem_update...
  destruct (eq_var_dec x2 x1)...
Qed.

Hint Resolve mem_update_shadow.

(* Update a variable to its current value won't "actually" change the state *)
Theorem mem_update_same :
  forall n1 x1 x2 (mem : memory),
    mem x1 = n1 ->
    (mem_update mem x1 n1) x2 = mem x2.
Proof with auto.
  intros.
  unfold mem_update...
  destruct (eq_var_dec x1 x2);
    subst...
Qed.

Hint Resolve mem_update_same.

(* The order of update doesn't matter *)
Theorem mem_update_permute :
  forall n1 n2 x1 x2 mem,
    x2 <> x1 -> 
    (mem_update (mem_update mem x2 n1) x1 n2) =
    (mem_update (mem_update mem x1 n2) x2 n1).
Proof with auto.
  intros.
  apply functional_extensionality.
  intros.
  unfold mem_update...
  destruct (eq_var_dec x1 x)...
  Case "x1 = x3".
    destruct (eq_var_dec x2 x); subst...
    apply ex_falso_quodlibet...
Qed.

Hint Resolve mem_update_permute.
(* ---------------- end of 2. Memory ---------------- *)


(* ---------------- 3. Thread ID ---------------- *)
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
(* ---------------- end of 3. Thread ID ---------------- *)


(* ---------------- 4. Lock ---------------- *)
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

Definition lks_update (st : lock_status) (l : lid) (v : option tid) : lock_status :=
  fun l' => if eq_lid_dec l l' then v else st l'.

Theorem lks_update_eq :
  forall l v lks,
    lks_update lks l v l = v.
Proof with auto.
  intros.
  unfold lks_update...
Qed.

Hint Resolve lks_update_eq.

Theorem lks_update_neq :
  forall l1 l2 v lks,
    l2 <> l1 -> (lks_update lks l2 v) l1 = (lks l1).
Proof with auto.
  intros.
  unfold lks_update...
Qed.

Hint Resolve lks_update_neq.


Theorem lks_update_permute :
  forall st l1 l2 v1 v2,
    l1 <> l2 ->
    lks_update (lks_update st l1 v1) l2 v2 =
    lks_update (lks_update st l2 v2) l1 v1.
Proof with auto.
  intros.
  apply functional_extensionality.
  intros.
  unfold lks_update.
  destruct (eq_lid_dec l2 x)...
  destruct (eq_lid_dec l1 x); subst...
  assert (x = x) by auto.
  apply H in H0; invf H0.
Qed.

Hint Resolve lks_update_permute.

(* Checking of validity is left to semantics, not done here *)
Definition lock (st : lock_status) (t : tid) (l : lid) : lock_status :=
  lks_update st l (Some t).

Hint Unfold lock.

(* Checking of validity is left to semantics, not done here *)
Definition unlock (st : lock_status) (l : lid) : lock_status :=
  lks_update st l None.

Hint Unfold unlock.


Module TestLocks.

Theorem test_lock_correctness:
  forall st t l, (lock st t l) l = Some t.
Proof with auto.
  intros.
  unfold lock; unfold lks_update...
Qed.

Theorem test_unlock_correctness:
  forall st t l, st l = Some t -> (unlock st l) l = None.
Proof with auto.
  intros.
  unfold unlock, lks_update...
Qed.

End TestLocks.
(* ---------------- end of 4. Lock ---------------- *)


(* ---------------- 5. Write Buffer ---------------- *)
(* In the buffer: [old ... new], new writes are appended to the right *)
Definition buffer : Type := list (var * nat).

(* Add a new write to the end of buffer *)
Definition write (b : buffer) (x : var) (n : nat) : buffer :=
  append b (x, n).

Hint Unfold write.

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


Definition buffer_status := tid -> buffer.

Definition empty_buffers : buffer_status :=
  fun _ => [].

Definition bufs_update (bufs : buffer_status) (t : tid) (b : buffer) : buffer_status :=
  fun t' => if eq_tid_dec t t' then b else bufs t'.

Hint Unfold bufs_update.


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
(* ---------------- end of 5. Write Buffer ---------------- *)


(* ---------------- 6. Event ---------------- *)
(* Events records the "important" actions while moving forward using
small-step semantics *)
Inductive event : Type :=
| EV_Read (x : var)
| EV_Write (x : var) (n : nat)
| EV_Lock (l : lid)
| EV_Unlock (l : lid)
| EV_None. (* Nothing significant happened, but moved one step anyway *)

Hint Constructors event.

Tactic Notation "event_cases" tactic(first) ident(c) :=
  first;
  [ Case_aux c "EV_Read" | Case_aux c "EV_Write"
  | Case_aux c "EV_Lock" | Case_aux c "EV_Unlock"
  | Case_aux c "EV_None"
  ].


Definition trace : Type := list (tid * event).
(* ---------------- end of 6. Event ---------------- *)


(* ---------------- 7. Arithmatic Expressions ---------------- *)
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

Inductive astep : buffer -> memory -> aexp -> aexp -> event -> Prop :=
| AS_Plus : forall b m n1 n2,
              (APlus (ANum n1) (ANum n2)) /- b ~ m ==A> ANum (n1 + n2) [[EV_None]]
| AS_Plus1 : forall b m a1 a1' a2 evt,
               a1 /- b ~ m ==A> a1' [[evt]] ->
               (APlus a1 a2) /- b ~ m ==A> (APlus a1' a2) [[evt]]
| AS_Plus2 : forall b m a1 a2 a2' evt,
               avalue a1 ->
               a2 /- b ~ m ==A> a2' [[evt]] ->
               (APlus a1 a2) /- b ~ m ==A> (APlus a1 a2') [[evt]]

| AS_Minus : forall b m n1 n2,
               AMinus (ANum n1) (ANum n2) /- b ~ m ==A> ANum (n1 - n2) [[EV_None]]
| AS_Minus1 : forall b m a1 a1' a2 evt,
                a1 /- b ~ m ==A> a1' [[evt]] ->
                (AMinus a1 a2) /- b ~ m ==A> (AMinus a1' a2) [[evt]]
| AS_Minus2 : forall b m a1 a2 a2' evt,
                avalue a1 ->
                a2 /- b ~ m ==A> a2' [[evt]] ->
                (AMinus a1 a2) /- b ~ m ==A> (AMinus a1 a2') [[evt]]

| AS_Mult : forall b m n1 n2,
              AMult (ANum n1) (ANum n2) /- b ~ m ==A> ANum (n1 * n2) [[EV_None]]
| AS_Mult1 : forall b m a1 a1' a2 evt,
               a1 /- b ~ m ==A> a1' [[evt]] ->
               (AMult a1 a2) /- b ~ m ==A> (AMult a1' a2) [[evt]]
| AS_Mult2 : forall b m a1 a2 a2' evt,
               avalue a1 ->
               a2 /- b ~ m ==A> a2' [[evt]] ->
               (AMult a1 a2) /- b ~ m ==A> (AMult a1 a2') [[evt]]

| AS_VarBuf : forall b m x n,
                get b x = Some n ->
                (AVar x) /- b ~ m ==A> (ANum n) [[EV_Read x]]
| AS_VarMem : forall b m x,
                get b x = None ->
                (AVar x) /- b ~ m ==A> ANum (m x) [[EV_Read x]]

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
(* ---------------- end of 7. Arithmatic Expressions ---------------- *)


(* ---------------- 8. Boolean Expressions ---------------- *)
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

Inductive bstep : buffer -> memory -> bexp -> bexp -> event -> Prop :=
| BS_Not : forall buf mem b,
             BNot (BBool b) /- buf ~ mem ==B> BBool (negb b) [[EV_None]]
| BS_Not1 : forall buf mem b b' evt,
              b /- buf ~ mem ==B> b' [[evt]] ->
              (BNot b) /- buf ~ mem ==B> BNot b' [[evt]]

| BS_And : forall buf mem b1 b2,
             (BAnd (BBool b1) (BBool b2)) /- buf ~ mem ==B> BBool (andb b1 b2) [[EV_None]]
| BS_And1 : forall buf mem be1 be1' be2 evt,
              be1 /- buf ~ mem ==B> be1' [[evt]] ->
              (BAnd be1 be2) /- buf ~ mem ==B> BAnd be1' be2 [[evt]]
| BS_And2 : forall buf mem be1 be2 be2' evt,
              bvalue be1 ->
              be2 /- buf ~ mem ==B> be2' [[evt]] ->
              (BAnd be1 be2) /- buf ~ mem ==B> BAnd be1 be2' [[evt]]

| BS_Eq : forall buf mem n1 n2,
            (BEq (ANum n1) (ANum n2)) /- buf ~ mem ==B> BBool (beq_nat n1 n2) [[EV_None]]
| BS_Eq1 : forall buf mem a1 a1' a2 evt,
             a1 /- buf ~ mem ==A> a1' [[evt]] ->
             (BEq a1 a2) /- buf ~ mem ==B> BEq a1' a2 [[evt]]
| BS_Eq2 : forall buf mem a1 a2 a2' evt,
             avalue a1 ->
             a2 /- buf ~ mem ==A> a2' [[evt]] ->
             (BEq a1 a2) /- buf ~ mem ==B> BEq a1 a2' [[evt]]

| BS_Le : forall buf mem n1 n2,
            (BLe (ANum n1) (ANum n2)) /- buf ~ mem ==B> BBool (ble_nat n1 n2) [[EV_None]]
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
(* ---------------- end of 8. Boolean Expressions ---------------- *)


(* ---------------- 9. Command & Threads ---------------- *)
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


(* command map *)
Definition threads := tid -> cmd.

Definition empty_threads : threads :=
  fun _ => SKIP.

Hint Unfold empty_threads.

Definition thds_update (thds : threads) (t : tid) (c : cmd) :=
  fun t' => if eq_tid_dec t t' then c else thds t'.

Hint Unfold thds_update.

Theorem thds_update_neq :
  forall t2 t1 c thds,
    t2 <> t1 -> (thds_update thds t2 c) t1 = thds t1.
Proof with auto.
  intros.
  unfold thds_update...
Qed.

Hint Resolve thds_update_neq.

Theorem thds_update_permute :
  forall ts t1 c1 t2 c2,
    t1 <> t2 ->
    thds_update (thds_update ts t1 c1) t2 c2 =
    thds_update (thds_update ts t2 c2) t1 c1.
Proof with auto.
  intros.
  apply functional_extensionality.
  intros t.
  unfold thds_update.
  destruct (eq_tid_dec t2 t)...
  destruct (eq_tid_dec t1 t)...
  subst.
  assert (t = t) by auto.
  apply H in H0; invf H0.
Qed.

Hint Resolve thds_update_permute.
(* ---------------- end of 9. Command & Threads ---------------- *)


(* ---------------- 10. State & Configuration ---------------- *)
(* state contains all those ONE single thread can change *)
Record state := ST {
  st_cmd : cmd;
  st_buf : buffer;
  st_mem : memory;
  st_lks : lock_status
}.

Hint Constructors state.


Inductive waiting : tid -> state -> Prop :=
| WT_Lock :
    forall t t' lks l mem,
      lks l = Some t' ->
      (* At first, I require t <> t', but for simplicity, one thread
      cannot acquire one lock twice! *)
      waiting t (ST (LOCK l) nil mem lks)
| WT_UnlockNone :
    forall t lks l mem,
      lks l = None ->
      waiting t (ST (UNLOCK l) nil mem lks)
| WT_UnlockOthers :
    forall t1 t2 lks l mem,
      lks l = Some t2 ->
      t1 <> t2 ->
      waiting t1 (ST (UNLOCK l) nil mem lks)
| WaitingSeq :
    forall t buf mem lks c1 c2,
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


(* configuration contains everything that may be modified, for all threads *)
Record configuration := CFG {
  cfg_tids : set tid;
  cfg_thds : threads;
  cfg_bufs : buffer_status;
  cfg_mem : memory;
  cfg_lks : lock_status
}.

Hint Constructors configuration.

Definition empty_configuration :=
  CFG empty_tids empty_threads empty_buffers empty_memory empty_locks.


Inductive cfg_normal_form : configuration -> Prop :=
(* Every thread is in normal_form *)
| CFGNF_Each : forall tids thds bufs mem lks,
                 (forall t, in_tids t tids = true ->
                            st_normal_form t (ST (thds t) (bufs t) mem lks)) ->
                 cfg_normal_form (CFG tids thds bufs mem lks).

Hint Constructors cfg_normal_form.


(* used in init_cfg() *)
Fixpoint _init_cfg (lc : list cmd) (n : nat) (accu : configuration) : configuration :=
  match lc with
    | nil => accu
    | h :: tlc =>
      match accu with
        | CFG tids thds bufs mem lks =>
          let t := TID n in
          let accu' := CFG (add_tid t tids) (thds_update thds t h) bufs mem lks in
          _init_cfg tlc (S n) accu'
      end
  end.

(* init_cfg is a function used to generate the initial configuration
from a list of commands *)
Definition init_cfg (lc : list cmd) : configuration :=
  _init_cfg lc 0 empty_configuration.

Hint Unfold init_cfg.


(* multi tso smallstep / multi sc smallstep *)
Definition relation (X:Type) := X -> X -> (tid * event) -> Prop.

Inductive multi {X:Type} (R: relation X) : X -> X -> trace -> Prop :=
| multi_refl  : forall x,
                  multi R x x []
| multi_step : forall x y z tevt trc,
                 R x y tevt ->
                 multi R y z trc ->
                 multi R x z (tevt :: trc).

Hint Constructors multi.

Tactic Notation "multi_cases" tactic(first) ident(c) :=
  first;
  [ Case_aux c "multi_refl" | Case_aux c "multi_step" ].

Theorem multi_R : forall (X:Type) (R:relation X) (x y : X) tevt,
                    R x y tevt -> multi R x y [tevt].
Proof. eauto. Qed.

Hint Resolve multi_R.

Theorem multi_trans :
  forall (X:Type) (R: relation X) (x y z : X) trc1 trc2,
      multi R x y trc1 ->
      multi R y z trc2 ->
      multi R x z (trc1 ++ trc2).
Proof.
  intros X R x y z trc1 trc2 Hxy Hyz.
  multi_cases (induction Hxy) Case;
    simpl; eauto.
Qed.

Hint Resolve multi_trans.
(* ---------------- end of 10. State & Configuration ---------------- *)

