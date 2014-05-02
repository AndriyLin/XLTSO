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
Last updated: 05/02/2014


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
* Diamond Lemma
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

Definition lks_update (st : lock_status) (l : lid) (v : option tid) : lock_status :=
  fun l' => if eq_lid_dec l l' then v else st l'.


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
(* ---------------- end of Lock ---------------- *)


(* ---------------- Write Buffer ---------------- *)
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
(* ---------------- end of Write Buffer ---------------- *)


(* ---------------- Event ---------------- *)
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

Inductive ststep : tid -> state -> state -> event -> Prop :=
| ST_Ass : forall t x n buf mem lks,
             t @ (ST (x ::= ANum n) buf mem lks) ==>
               (ST SKIP (write buf x n) mem lks) [[EV_Write x n]]
| ST_AssStep : forall t x a a' buf mem lks evt,
                 a /- buf ~ mem ==A> a' [[evt]] ->
                 t @ (ST (x ::= a) buf mem lks) ==> (ST (x ::= a') buf mem lks) [[evt]]

| ST_Seq : forall t c2 buf mem lks,
             t @ (ST (SKIP ;; c2) buf mem lks) ==> (ST c2 buf mem lks) [[EV_None]]
| ST_SeqStep : forall t c1 c1' c2 buf mem lks buf' mem' lks' evt,
                 t @ (ST c1 buf mem lks) ==> (ST c1' buf' mem' lks') [[evt]] ->
                 t @ (ST (c1 ;; c2) buf mem lks) ==> (ST (c1' ;; c2) buf' mem' lks') [[evt]]

| ST_IfTrue : forall t c1 c2 buf mem lks,
                t @ (ST (IFB (BBool true) THEN c1 ELSE c2 FI) buf mem lks) ==>
                  (ST c1 buf mem lks) [[EV_None]]
| ST_IfFalse : forall t c1 c2 buf mem lks,
                 t @ (ST (IFB (BBool false) THEN c1 ELSE c2 FI) buf mem lks) ==>
                   (ST c2 buf mem lks) [[EV_None]]
| ST_IfStep : forall t c1 c2 be be' buf mem lks evt,
                be /- buf ~ mem ==B> be' [[evt]] ->
                t @ (ST (IFB be THEN c1 ELSE c2 FI) buf mem lks) ==>
                  (ST (IFB be' THEN c1 ELSE c2 FI) buf mem lks) [[evt]]

| ST_While : forall t b c buf mem lks,
               t @ (ST (WHILE b DO c END) buf mem lks) ==>
                 (ST (IFB b THEN (c ;; (WHILE b DO c END)) ELSE SKIP FI) buf mem lks)
                 [[EV_None]]

| ST_FlushOne : forall t buf mem lks x n c,
                  (* Here it's defined as "it can flush no matter blocked or not" *)
                  oldest buf = Some (x, n) ->
                  t @ (ST c buf mem lks) ==> (ST c (flushone buf) (mem_update mem x n) lks)
                    [[EV_None]]

(* to LOCK, buffer must be empty *)
| ST_Lock : forall t mem lks lk,
              lks lk = None ->
              t @ (ST (LOCK lk) nil mem lks) ==>
                (ST SKIP nil mem (lock lks t lk)) [[EV_Lock lk]]
| ST_LockAgain : forall t mem lks lk,
                   lks lk = Some t ->
                   t @ (ST (LOCK lk) nil mem lks) ==> (ST SKIP nil mem lks) [[EV_None]]

(* to UNLOCK, buffer must be empty *)
| ST_Unlock : forall t mem lks lk,
                lks lk = Some t ->
                t @ (ST (UNLOCK lk) nil mem lks) ==>
                  (ST SKIP nil mem (unlock lks lk)) [[EV_Unlock lk]]
| ST_UnlockNil : forall t mem lks lk,
                   lks lk = None ->
                   t @ (ST (UNLOCK lk) nil mem lks) ==> (ST SKIP nil mem lks) [[EV_None]]
| ST_UnlockOthers : forall t t' mem lks lk,
                      lks lk = Some t' ->
                      t <> t' ->
                      t @ (ST (UNLOCK lk) nil mem lks) ==> (ST SKIP nil mem lks) [[EV_None]]


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
    exists (ST SKIP buf (mem_update mem v n) lks); exists EV_None...
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
  remember (ST c nil (mem_update empty_memory X 100) empty_locks) as st2.
  remember EV_None as evt1.
  remember EV_None as evt2.
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
(* All threads finish *)
| CFGV_End : forall thds bufs mem lks,
               cfg_normal_form (CFG empty_tids thds bufs mem lks)
(* Deadlock *)
| CFGV_Deadlock: forall tids thds bufs mem lks,
                   (forall t c b, in_tids t tids = true ->
                                  thds t = c ->
                                  bufs t = b ->
                                  waiting t (ST c b mem lks)) ->
                   cfg_normal_form (CFG tids thds bufs mem lks)
.

Hint Constructors cfg_normal_form.

Reserved Notation "cfg1 '-->' cfg2 '[[' tevt ']]'" (at level 60).

Inductive cfgstep : configuration -> configuration -> (tid * event) -> Prop :=
(* One thread already ends its job, thus remove it *)
| CFGS_Done : forall t tids thds bufs mem lks,
                in_tids t tids = true ->
                thds t = SKIP ->
                bufs t = nil ->
                (CFG tids thds bufs mem lks) --> (CFG (remove_tid t tids) thds bufs mem lks)
                                             [[(t, EV_None)]]

(* One thread can move one step forward, in terms of "state" *)
| CFGS_One : forall t tids thds bufs c c' b b' mem mem' lks lks' evt,
               in_tids t tids = true ->
               thds t = c ->
               bufs t = b ->
               t @ (ST c b mem lks) ==> (ST c' b' mem' lks') [[evt]] ->
               (CFG tids thds bufs mem lks) -->
                 (CFG tids (thds_update thds t c') (bufs_update bufs t b') mem' lks')
                 [[(t, evt)]]

where "cfg1 '-->' cfg2 '[[' tevt ']]'" := (cfgstep cfg1 cfg2 tevt).

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


Definition multicfgstep := multi cfgstep.
Notation "cfg1 '-->*' cfg2 '[[' tevts ']]'" := (multicfgstep cfg1 cfg2 tevts) (at level 40).

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
  forall tids thds bufs mem lks,
    init_cfg codes = (CFG tids thds bufs mem lks) ->
    size_tids tids = 2 /\ in_tids T0 tids = true /\ in_tids T1 tids = true
    /\ thds T0 = proc0 /\ thds T1 = proc1.
Proof.
  intros.
  unfold codes, proc0, proc1, init_cfg in *.
  inv H.
  split; auto.
Qed.

(* The following is to prove that the final state is actually
reachable by the language and semantics defined above. *)
Theorem tso_semantics:
  exists thds bufs mem lks trc,
    init_cfg codes -->* (CFG empty_tids thds bufs mem lks) [[trc]] /\
    cfg_normal_form (CFG empty_tids thds bufs mem lks) /\ (* final state *)
    mem EAX = 1 /\ mem EBX = 0 /\ mem X = 1.
Proof with eauto.
  eexists.
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

Inductive sc : tid -> state -> state -> event -> Prop :=
| SC_Ass : forall t x n mem lks,
             t @ (ST (x ::= ANum n) nil mem lks) ==SC>
                 (ST SKIP nil (mem_update mem x n) lks) [[EV_Write x n]]
| SC_AssStep : forall t x a a' mem lks evt,
                 a /- nil ~ mem ==A> a' [[evt]] ->
                 t @ (ST (x ::= a) nil mem lks) ==SC> (ST (x ::= a') nil mem lks) [[evt]]

| SC_Seq : forall t c2 mem lks,
             t @ (ST (SKIP ;; c2) nil mem lks) ==SC> (ST c2 nil mem lks) [[EV_None]]
| SC_SeqStep : forall t c1 c1' c2 mem lks mem' lks' evt,
                 t @ (ST c1 nil mem lks) ==SC> (ST c1' nil mem' lks') [[evt]] ->
                 t @ (ST (c1 ;; c2) nil mem lks) ==SC> (ST (c1' ;; c2) nil mem' lks') [[evt]]

| SC_IfTrue : forall t c1 c2 mem lks,
                t @ (ST (IFB (BBool true) THEN c1 ELSE c2 FI) nil mem lks) ==SC>
                    (ST c1 nil mem lks) [[EV_None]]
| SC_IfFalse : forall t c1 c2 mem lks,
                 t @ (ST (IFB (BBool false) THEN c1 ELSE c2 FI) nil mem lks) ==SC>
                     (ST c2 nil mem lks) [[EV_None]]
| SC_IfStep : forall t c1 c2 be be' mem lks evt,
                be /- nil ~ mem ==B> be' [[evt]] ->
                t @ (ST (IFB be THEN c1 ELSE c2 FI) nil mem lks) ==SC>
                    (ST (IFB be' THEN c1 ELSE c2 FI) nil mem lks) [[evt]]

| SC_While : forall t b c mem lks,
               t @ (ST (WHILE b DO c END) nil mem lks) ==SC>
                   (ST (IFB b THEN (c ;; (WHILE b DO c END)) ELSE SKIP FI)
                       nil mem lks) [[EV_None]]

(* The following rules are the same as TSO *)
| SC_Lock : forall t mem lks lk,
              lks lk = None ->
              t @ (ST (LOCK lk) nil mem lks) ==SC>
                (ST SKIP nil mem (lock lks t lk)) [[EV_Lock lk]]
| SC_LockAgain : forall t mem lks lk,
                   lks lk = Some t ->
                   t @ (ST (LOCK lk) nil mem lks) ==SC> (ST SKIP nil mem lks) [[EV_None]]

| SC_Unlock : forall t mem lks lk,
                lks lk = Some t ->
                t @ (ST (UNLOCK lk) nil mem lks) ==SC>
                  (ST SKIP nil mem (unlock lks lk)) [[EV_Unlock lk]]
| SC_UnlockNil : forall t mem lks lk,
                   lks lk = None ->
                   t @ (ST (UNLOCK lk) nil mem lks) ==SC> (ST SKIP nil mem lks) [[EV_None]]
| SC_UnlockOthers : forall t t' mem lks lk,
                      lks lk = Some t' ->
                      t <> t' ->
                      t @ (ST (UNLOCK lk) nil mem lks) ==SC> (ST SKIP nil mem lks) [[EV_None]]


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


Reserved Notation "cfg1 '--SC>' cfg2 '[[' tevt ']]'" (at level 60).

Inductive cfgsc : configuration -> configuration -> (tid * event) -> Prop :=
(* One thread already ends its job, thus remove it *)
| CFGSC_Done : forall t tids thds bufs mem lks,
                 in_tids t tids = true ->
                 thds t = SKIP ->
                 bufs t = nil ->
                 (CFG tids thds bufs mem lks) --SC> (CFG (remove_tid t tids) thds bufs mem lks)
                                                      [[(t, EV_None)]]

(* One thread can move one step forward, in terms of "state" *)
| CFGSC_One : forall t tids thds bufs c c' mem mem' lks lks' evt,
                in_tids t tids = true ->
                thds t = c ->
                bufs t = nil ->
                t @ (ST c nil mem lks) ==SC> (ST c' nil mem' lks') [[evt]] ->
                (CFG tids thds bufs mem lks) --SC>
                  (CFG tids (thds_update thds t c') bufs mem' lks') [[(t, evt)]]

where "cfg1 '--SC>' cfg2 '[[' tevt ']]'" := (cfgsc cfg1 cfg2 tevt).

Hint Constructors cfgsc.

Tactic Notation "cfgsc_cases" tactic(first) ident(c) :=
  first;
  [ Case_aux c "CFGSC_Done" | Case_aux c "CFGSC_One" ].

Definition multicfgsc := multi cfgsc.
Notation "cfg1 '--SC>*' cfg2 '[[' tevts ']]'" := (multicfgsc cfg1 cfg2 tevts) (at level 40).
(* ---------------- end of Sequential Consistency Semantics ---------------- *)


(* ---------------- Data-Race-Free ---------------- *)
(* The command determines whether "writes c x" is provable, so just
assign the most basic context. *)
Inductive writes : cmd -> var -> Prop :=
| Writes : forall c st' x n,
             T0 @ (ST c nil empty_memory empty_locks) ==SC> st' [[EV_Write x n]] ->
             writes c x
.

Hint Constructors writes.

(* The command determines whether "reads c x" is provable, so just
assign the most basic context. *)
Inductive reads : cmd -> var -> Prop :=
| Reads : forall c st' x,
            T0 @ (ST c nil empty_memory empty_locks) ==SC> st' [[EV_Read x]] ->
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
  ~ (exists tids thds bufs mem lks t1 t2 trc,
       cfg --SC>* (CFG tids thds bufs mem lks) [[trc]]
       /\ in_tids t1 tids = true
       /\ in_tids t2 tids = true
       /\ t1 <> t2
       /\ datarace (thds t1) (thds t2)
    ).


Theorem drf_preservation :
  forall cfg1 cfg2 trc, data_race_free cfg1 ->
                    cfg1 --SC>* cfg2 [[trc]] ->
                    data_race_free cfg2.
Proof with eauto.
  intros cfg1 cfg2 trc Hdrf H.
  multi_cases (induction H) Case...
  Case "multi_step".
  apply IHmulti.
  intros Hf.
  apply Hdrf.
  inversion Hf as [tids]; clear Hf.
  inversion H1 as [thds]; clear H1.
  inversion H2 as [bufs]; clear H2.
  inversion H1 as [mem]; clear H1.
  inversion H2 as [lks]; clear H2.
  inversion H1 as [t1]; clear H1.
  inversion H2 as [t2]; clear H2.
  inversion H1 as [trc']; clear H1.
  inv H2.

  exists tids; exists thds; exists bufs; exists mem; exists lks;
  exists t1; exists t2; exists (tevt :: trc').
  split...

  apply multi_step with y...
Qed.

Hint Resolve drf_preservation.
(* ---------------- end of Data-Race-Free ---------------- *)


(* ---------------- Diamond Lemma ---------------- *)
(* Whether 2 consecutive events of different tids in a trace can not
be simply swapped.  LOCK & UNLOCK are considered to be "write"
operations. *)
Inductive conflict : event -> event -> Prop :=
| CFL_WrWr : forall x n1 n2,
               conflict (EV_Write x n1) (EV_Write x n2)
| CFL_WrRd : forall x n,
               conflict (EV_Write x n) (EV_Read x)
| CFL_RdWr : forall x n,
               conflict (EV_Read x) (EV_Write x n)
| CFL_LkLk : forall l,
               conflict (EV_Lock l) (EV_Lock l)
| CFL_LkUn : forall l,
               conflict (EV_Lock l) (EV_Unlock l)
| CFL_UnLk : forall l,
               conflict (EV_Unlock l) (EV_Lock l)
| CFL_UnUn : forall l,
               conflict (EV_Unlock l) (EV_Unlock l)
.

Hint Constructors conflict.

Tactic Notation "conflict_cases" tactic(first) ident(c) :=
  first;
  [ Case_aux c "CFL_WrWr" | Case_aux c "CFL_WrRd"
  | Case_aux c "CFL_RdWr"
  | Case_aux c "CFL_LkLk" | Case_aux c "CFL_LkUn"
  | Case_aux c "CFL_UnLk" | Case_aux c "CFL_UnUn"
  ].

(* ---------------------------------------------------------------- *)

(* The following several lemmas are for the Diamond Theorem when at
least one step is by ending a thread *)

(* When removing 2 tids, it doesn't matter which one is removed first. *)
Lemma remove_order_independent :
  forall tids t1 t2,
    remove_tid t2 (remove_tid t1 tids) = remove_tid t1 (remove_tid t2 tids).
Proof with auto.
  intros tids.
  induction tids as [ | hd tl];
    intros; simpl...
  Case "tids = hd :: tl".
  destruct (eq_tid_dec t1 hd) eqn:Ht1hd; subst.
  SCase "t1 = hd".
    destruct (eq_tid_dec t2 hd) eqn:Ht2hd; subst...
    SSCase "t2 <> hd".
    simpl; rewrite -> eq_tid...
  SCase "t1 <> hd".
    destruct (eq_tid_dec t2 hd) eqn:Ht2hd; subst...
    SSCase "t2 = hd".
      simpl; rewrite -> eq_tid...
    SSCase "t2 <> hd".
      simpl; rewrite -> Ht1hd; rewrite -> Ht2hd.
      rewrite -> IHtl...
Qed.

Hint Resolve remove_order_independent.

(* Removing a tid won't affect the result of in_tids t' when t <> t' *)
Lemma remove_irrelevant :
  forall tids t1 t2,
    t1 <> t2 ->
    in_tids t2 tids = in_tids t2 (remove_tid t1 tids).
Proof with auto.
  intros.
  induction tids as [ | hd tl]...
  simpl.
  destruct (eq_tid_dec t2 hd) eqn:Ht2hd;
    destruct (eq_tid_dec t1 hd) eqn:Ht1hd; subst...
  apply ex_falso_quodlibet; apply H...
  simpl; rewrite -> eq_tid...
  simpl; rewrite -> Ht2hd...
Qed.

Hint Resolve remove_irrelevant.

(* I really don't forsee that this theorem needs to be proved explicitly!! *)
Lemma list_neq :
  forall (ts : list tid) (t : tid), ts <> t :: ts.
Proof with auto.
  intros ts.
  induction ts; intros.
  intros Hf; inversion Hf.
  intros Hf.
  inversion Hf.
  apply IHts in H1.
  inversion H1.
Qed.

Hint Resolve list_neq.

(* once something is actually removed from a set, the set is no longer the same as before *)
Lemma remove_then_neq :
  forall tids t,
    in_tids t tids = true ->
    remove_tid t tids <> tids.
Proof with auto.
  intros tids.
  induction tids as [ | hd tl];
    intros.
  Case "tids = nil".
    inversion H.
  Case "tids = hd :: tl".
    simpl.
    destruct (eq_tid_dec t hd) eqn:Hthd; subst.
    apply list_neq.
    intros Hf.
    inversion Hf.
    apply IHtl in H1...
    simpl in H.
    rewrite -> Hthd in H...
Qed.

Hint Resolve remove_then_neq.

(* TODO: I used Axiom here because I failed to prove it as a theorem.
 This will be used in lemma tids_irrelevant! *)
Axiom thds_update_exact_equiv :
  forall thds t1 c1 t2 c2,
    thds_update thds t1 c1 = thds_update thds t2 c2 ->
    t1 = t2 /\ c1 = c2.

(* Changing to another tid set won't affect the result when the
executied thread is still in that set *)
Lemma tids_irrelevant :
  forall tids tids' thds bufs mem lks t c' mem' lks' evt,
    (CFG tids thds bufs mem lks) --SC>
      (CFG tids (thds_update thds t c') bufs mem' lks') [[(t, evt)]] ->
    in_tids t tids' = true ->
    (CFG tids' thds bufs mem lks) --SC>
      (CFG tids' (thds_update thds t c') bufs mem' lks') [[(t, evt)]].
Proof with eauto.
  intros.
  generalize dependent tids'.
  remember (CFG tids thds bufs mem lks) as cfg.
  remember (CFG tids (thds_update thds t c') bufs mem' lks') as cfg'.
  generalize dependent lks; generalize dependent mem.
  generalize dependent thds; generalize dependent tids.
  generalize dependent c'; generalize dependent mem';
  generalize dependent lks'.
  cfgsc_cases (induction H) Case;
    intros; inversion Heqcfg; subst; clear Heqcfg; inversion Heqcfg'.
  Case "CFGSC_Done".
    assert (remove_tid t0 tids0 <> tids0) by eauto.
    apply H3 in H4; inversion H4.
  Case "CFGSC_One".
    clear Heqcfg'; subst.
    apply thds_update_exact_equiv in H4.
    inv H4...
Qed.

Hint Resolve tids_irrelevant.

(* end of all lemmas for the Diamond Theorem when at least one step is
by ending a thread *)

(* ---------------------------------------------------------------- *)

(* The following several lemmas are for the Diamond Theorem when both
steps are by executing a thread:

  What it means for a smallstep to generate a EV_XX event?
*)
Lemma astep_event_read_or_none:
  forall a1 a2 buf mem evt,
    a1 /- buf ~ mem ==A> a2 [[evt]] ->
    exists x, evt = EV_Read x \/ evt = EV_None.
Proof with auto.
  intros.
  astep_cases (induction H) Case;
    auto.
  Case "AS_Plus".
  (* Here name X just for proof requirements, it can also be Y *)
    exists X; right...
  Case "AS_Minus".
    exists X; right...
  Case "AS_Mult".
    exists X; right...
  Case "AS_VarBuf".
    exists x; left...
  Case "AS_VarMem".
    exists x; left...
Qed.

Hint Resolve astep_event_read_or_none.

Lemma bstep_event_read_or_none:
  forall b1 b2 buf mem evt,
    b1 /- buf ~ mem ==B> b2 [[evt]] ->
    exists x, evt = EV_Read x \/ evt = EV_None.
Proof with auto.
  intros.
  bstep_cases (induction H) Case;
    auto.
  Case "BS_Not".
  (* Here name X just for proof requirements, it can also be Y *)
    exists X; right...
  Case "BS_And".
    exists X; right...
  Case "BS_Eq".
    exists X; right...
  Case "BS_Eq1".
    apply astep_event_read_or_none in H...
  Case "BS_Eq2".
    apply astep_event_read_or_none in H0...
  Case "BS_Le".
    exists X; right...
  Case "BS_Le1".
    apply astep_event_read_or_none in H...
  Case "BS_Le2".
    apply astep_event_read_or_none in H0...
Qed.

Lemma sc_event_read :
  forall t c c' mem lks mem' lks' x,
    t @ (ST c nil mem lks) ==SC> (ST c' nil mem' lks') [[EV_Read x]] ->
    mem = mem' /\ lks = lks'.
Proof with eauto.
  intros.
  remember (ST c nil mem lks) as st1.
  remember (ST c' nil mem' lks') as st2.
  remember (EV_Read x) as evt.
  generalize dependent x;
  generalize dependent c; generalize dependent c';
  generalize dependent mem; generalize dependent mem';
  generalize dependent lks; generalize dependent lks'.
  sc_cases (induction H) Case;
    intros; inversion Heqevt;
    inversion Heqst1; inversion Heqst2; subst...
Qed.

Lemma sc_event_write :
  forall t c c' mem lks mem' lks' x n,
    t @ (ST c nil mem lks) ==SC> (ST c' nil mem' lks') [[EV_Write x n]] ->
    mem' = mem_update mem x n /\ lks = lks'.
Proof with eauto.
  intros.
  remember (ST c nil mem lks) as st1.
  remember (ST c' nil mem' lks') as st2.
  remember (EV_Write x n) as evt.
  generalize dependent n; generalize dependent x;
  generalize dependent c; generalize dependent c';
  generalize dependent mem; generalize dependent mem';
  generalize dependent lks; generalize dependent lks'.
  sc_cases (induction H) Case;
    intros; inversion Heqevt; subst;
    inv Heqst1; inv Heqst2...
  Case "SC_AssStep".
    apply astep_event_read_or_none in H.
    inv H.
    inv H1; invf H.
  Case "SC_IfStep".
    apply bstep_event_read_or_none in H.
    inv H.
    inv H1; inv H.
Qed.

Lemma sc_event_lock :
  forall t c c' mem lks mem' lks' lk,
    t @ (ST c nil mem lks) ==SC> (ST c' nil mem' lks') [[EV_Lock lk]] ->
    mem = mem' /\ lks' = lock lks t lk.
Proof with eauto.
  intros.
  remember (ST c nil mem lks) as st1.
  remember (ST c' nil mem' lks') as st2.
  remember (EV_Lock lk) as evt.
  generalize dependent lk;
  generalize dependent c; generalize dependent c';
  generalize dependent mem; generalize dependent mem';
  generalize dependent lks; generalize dependent lks'.
  sc_cases (induction H) Case;
    intros; inversion Heqevt; subst;
    inv Heqst1; inv Heqst2...
  Case "SC_AssStep".
    apply astep_event_read_or_none in H.
    inv H.
    inv H1; invf H.
  Case "SC_IfStep".
    apply bstep_event_read_or_none in H.
    inv H.
    inv H1; inv H.
Qed.

Lemma sc_event_unlock :
  forall t c c' mem lks mem' lks' lk,
    t @ (ST c nil mem lks) ==SC> (ST c' nil mem' lks') [[EV_Unlock lk]] ->
    mem = mem' /\ lks' = unlock lks lk.
Proof with eauto.
  intros.
  remember (ST c nil mem lks) as st1.
  remember (ST c' nil mem' lks') as st2.
  remember (EV_Unlock lk) as evt.
  generalize dependent lk;
  generalize dependent c; generalize dependent c';
  generalize dependent mem; generalize dependent mem';
  generalize dependent lks; generalize dependent lks'.
  sc_cases (induction H) Case;
    intros; inversion Heqevt; subst;
    inv Heqst1; inv Heqst2...
  Case "SC_AssStep".
    apply astep_event_read_or_none in H.
    inv H.
    inv H1; invf H.
  Case "SC_IfStep".
    apply bstep_event_read_or_none in H.
    inv H.
    inv H1; inv H.
Qed.

Lemma sc_event_none :
  forall t c c' mem lks mem' lks',
    t @ (ST c nil mem lks) ==SC> (ST c' nil mem' lks') [[EV_None]] ->
    mem = mem' /\ lks = lks'.
Proof with eauto.
  intros.
  remember (ST c nil mem lks) as st1.
  remember (ST c' nil mem' lks') as st2.
  remember (EV_None) as evt.
  generalize dependent c; generalize dependent c';
  generalize dependent mem; generalize dependent mem';
  generalize dependent lks; generalize dependent lks'.
  sc_cases (induction H) Case;
    intros; inversion Heqevt; subst;
    inv Heqst1; inv Heqst2...
Qed.


(* end of all lemmas for:
     What it means for a smallstep to generate a EV_XX event?
*)

(* ---------------------------------------------------------------- *)

(* The following several lemmas are for the Diamond Theorem when both
steps are by executing a thread:

  If a smallstep generates an event EV_XXX, then it will also generate
  this event in a slightly different context.
*)

Lemma astep_context_invariance_more :
  forall a a' x1 x2 n buf mem,
    x1 <> x2 ->
    a /- buf ~ mem ==A> a' [[EV_Read x1]] ->
    a /- buf ~ (mem_update mem x2 n) ==A> a' [[EV_Read x1]].
Proof with eauto.
  intros.
  remember (EV_Read x1) as evt.
  generalize dependent x1;
  generalize dependent n; generalize dependent x2.
  astep_cases (induction H0) Case;
    intros; inversion Heqevt; subst; eauto.
  Case "AS_VarMem".
    replace (m x1) with (mem_update m x2 n x1)...
Qed.

Hint Resolve astep_context_invariance_more.

Lemma astep_context_invariance_less :
  forall a a' x1 x2 n buf mem,
    x1 <> x2 ->
    a /- buf ~ (mem_update mem x2 n) ==A> a' [[EV_Read x1]] ->
    a /- buf ~ mem ==A> a' [[EV_Read x1]].
Proof with eauto.
  intros.
  remember (mem_update mem x2 n) as mem'.
  remember (EV_Read x1) as evt.
  generalize dependent x1; generalize dependent mem;
  generalize dependent n; generalize dependent x2.
  astep_cases (induction H0) Case;
    intros; inversion Heqevt; subst; eauto.
  Case "AS_VarMem".
    replace (mem_update mem x2 n x1) with (mem x1)...
    rewrite -> mem_update_neq...
Qed.

Hint Resolve astep_context_invariance_less.

Lemma bstep_context_invariance_more :
  forall b b' x1 x2 n buf mem,
    x1 <> x2 ->
    b /- buf ~ mem ==B> b' [[EV_Read x1]] ->
    b /- buf ~ (mem_update mem x2 n) ==B> b' [[EV_Read x1]].
Proof with eauto.
  intros.
  remember (EV_Read x1) as evt.
  generalize dependent x1;
  generalize dependent n; generalize dependent x2.
  bstep_cases (induction H0) Case;
    intros; inversion Heqevt; subst; eauto.
Qed.

Hint Resolve bstep_context_invariance_more.

Lemma bstep_context_invariance_less :
  forall b b' x1 x2 n buf mem,
    x1 <> x2 ->
    b /- buf ~ (mem_update mem x2 n) ==B> b' [[EV_Read x1]] ->
    b /- buf ~ mem ==B> b' [[EV_Read x1]].
Proof with eauto.
  intros.
  remember (EV_Read x1) as evt.
  remember (mem_update mem x2 n) as mem'.
  generalize dependent x1; generalize dependent mem;
  generalize dependent n; generalize dependent x2.
  bstep_cases (induction H0) Case;
    intros; inversion Heqevt; subst; eauto.
Qed.

Hint Resolve bstep_context_invariance_less.


(* If thread is about to read variable x, then change another value in
the memory won't affect this read *)
Lemma read_context_invariance_mem_more :
  forall t c mem lks c' x1 x2 n,
    x1 <> x2 ->
    t @ (ST c [] mem lks) ==SC> (ST c' [] mem lks) [[EV_Read x1]] ->
    t @ (ST c [] (mem_update mem x2 n) lks) ==SC>
        (ST c' [] (mem_update mem x2 n) lks) [[EV_Read x1]].
Proof with eauto.
  intros.
  remember (ST c [] mem lks) as st1.
  remember (ST c' [] mem lks) as st2.
  remember (EV_Read x1) as evt.
  generalize dependent x1;
  generalize dependent n; generalize dependent x2;
  generalize dependent lks; generalize dependent mem;
  generalize dependent c'; generalize dependent c.
  sc_cases (induction H0) Case;
    intros; inversion Heqevt; inv Heqst1; inv Heqst2.
  Case "SC_AssStep".
    constructor.
    apply astep_context_invariance_more...
  Case "SC_SeqStep".
    constructor.
    apply IHsc with x1...
  Case "SC_IfStep".
    constructor.
    apply bstep_context_invariance_more...
Qed.

Hint Resolve read_context_invariance_mem_more.

Lemma read_context_invariance_mem_less :
  forall t c mem lks c' x1 x2 n,
    x1 <> x2 ->
    t @ (ST c [] (mem_update mem x2 n) lks) ==SC>
        (ST c' [] (mem_update mem x2 n) lks) [[EV_Read x1]] ->
    t @ (ST c [] mem lks) ==SC> (ST c' [] mem lks) [[EV_Read x1]].
Proof with eauto.
  intros.
  remember (ST c [] (mem_update mem x2 n) lks) as st1.
  remember (ST c' [] (mem_update mem x2 n) lks) as st2.
  remember (EV_Read x1) as evt.
  generalize dependent x1;
  generalize dependent n; generalize dependent x2;
  generalize dependent lks; generalize dependent mem;
  generalize dependent c'; generalize dependent c.
  sc_cases (induction H0) Case;
    intros; inversion Heqevt; inv Heqst1; inv Heqst2.
  Case "SC_AssStep".
    constructor.
    eapply astep_context_invariance_less...
  Case "SC_SeqStep".
    constructor.
    eapply IHsc...
  Case "SC_IfStep".
    constructor.
    eapply bstep_context_invariance_less...
Qed.

Hint Resolve read_context_invariance_mem_less.

(* If thread 1 is just about to read a value, it doesn't matter what
 the current lock_status is *)
Lemma read_context_invariance_lks :
  forall t c c' mem lks lks' x,
    t @ (ST c [] mem lks) ==SC> (ST c' [] mem lks) [[EV_Read x]] ->
    t @ (ST c [] mem lks') ==SC> (ST c' [] mem lks') [[EV_Read x]].
Proof with eauto.
  intros.
  remember (ST c [] mem lks) as st1.
  remember (ST c' [] mem lks) as st2.
  remember (EV_Read x) as evt.
  generalize dependent x;
  generalize dependent lks; generalize dependent mem;
  generalize dependent c'; generalize dependent c.
  sc_cases (induction H) Case;
    intros; inversion Heqevt; inv Heqst1; inv Heqst2.
  Case "SC_AssStep".
    constructor...
  Case "SC_SeqStep".
    constructor...
  Case "SC_IfStep".
    constructor...
Qed.


Lemma write_context_invariance :
  forall t c c' mem mem' lks lks' x n,
    t @ (ST c [] mem lks) ==SC> (ST c' [] (mem_update mem x n) lks) [[EV_Write x n]] ->
    t @ (ST c [] mem' lks') ==SC> (ST c' [] (mem_update mem' x n) lks') [[EV_Write x n]].
Proof with eauto.
  intros.
  remember (ST c [] mem lks) as st1.
  remember (ST c' [] (mem_update mem x n) lks) as st2.
  remember (EV_Write x n) as evt.
  generalize dependent n; generalize dependent x;
  generalize dependent lks; generalize dependent mem;
  generalize dependent mem'; generalize dependent lks';
  generalize dependent c'; generalize dependent c.
  sc_cases (induction H) Case;
    intros; inversion Heqevt; inv Heqst1; inversion Heqst2...
  Case "SC_AssStep".
    apply astep_event_read_or_none in H.
    inversion H.
    inversion H1; inversion H4.
  Case "SC_SeqStep".
    subst...
  Case "SC_IfStep".
    apply bstep_event_read_or_none in H.
    inversion H.
    inversion H1; inversion H4.
Qed.


Lemma lock_context_invariance_mem :
  forall t c c' mem mem' lks l,
    t @ (ST c [] mem lks) ==SC> (ST c' [] mem (lock lks t l)) [[EV_Lock l]] ->
    t @ (ST c [] mem' lks) ==SC> (ST c' [] mem' (lock lks t l)) [[EV_Lock l]].
Proof with eauto.
  intros.
  remember (ST c [] mem lks) as st1.
  remember (ST c' [] mem (lock lks t l)) as st2.
  remember (EV_Lock l) as evt.
  generalize dependent l; generalize dependent lks;
  generalize dependent mem'; generalize dependent mem;
  generalize dependent c'; generalize dependent c.
  sc_cases (induction H) Case;
    intros; inversion Heqevt; inv Heqst1; inversion Heqst2...
  Case "SC_AssStep".
    apply astep_event_read_or_none in H.
    inversion H.
    inversion H1; inversion H4.
  Case "SC_SeqStep".
    subst...
  Case "SC_IfStep".
    apply bstep_event_read_or_none in H.
    inversion H.
    inversion H1; inversion H4.
Qed.

Lemma lock_context_invariance_lks_less :
  forall t c c' mem lks l1 l2 v2,
    l1 <> l2 ->
    t @ (ST c [] mem (lks_update lks l2 v2)) ==SC>
        (ST c' [] mem (lock (lks_update lks l2 v2) t l1)) [[EV_Lock l1]] ->
    t @ (ST c [] mem lks) ==SC> (ST c' [] mem (lock lks t l1)) [[EV_Lock l1]].
Proof with eauto.
  intros.
  remember (ST c [] mem (lks_update lks l2 v2)) as st1.
  remember (ST c' [] mem (lock (lks_update lks l2 v2) t l1)) as st2.
  remember (EV_Lock l1) as evt.
  generalize dependent c'; generalize dependent c;
  generalize dependent mem; generalize dependent lks;
  generalize dependent l1; generalize dependent l2;
  generalize dependent v2.
  sc_cases (induction H0) Case;
    intros; inversion Heqevt; inv Heqst1; inv Heqst2...
  Case "SC_AssStep".
    apply astep_event_read_or_none in H.
    inv H.
    inv H2; invf H.
  Case "SC_IfStep".
    apply bstep_event_read_or_none in H.
    inv H.
    inv H2; invf H.
  Case "SC_Lock".
    rewrite -> lks_update_neq in H...
Qed.

Lemma lock_context_invariance_lks_more :
  forall t c c' mem lks l1 l2 v2,
    l1 <> l2 ->
    t @ (ST c [] mem lks) ==SC> (ST c' [] mem (lock lks t l1)) [[EV_Lock l1]] ->
    t @ (ST c [] mem (lks_update lks l2 v2)) ==SC>
         (ST c' [] mem (lock (lks_update lks l2 v2) t l1)) [[EV_Lock l1]].
Proof with eauto.
  intros.
  remember (ST c [] mem lks) as st1.
  remember (ST c' [] mem (lock lks t l1)) as st2.
  remember (EV_Lock l1) as evt.
  generalize dependent c'; generalize dependent c;
  generalize dependent mem; generalize dependent lks;
  generalize dependent l1; generalize dependent l2;
  generalize dependent v2.
  sc_cases (induction H0) Case;
    intros; inversion Heqevt; inv Heqst1; inversion Heqst2.
  Case "SC_AssStep".
    apply astep_event_read_or_none in H.
    inversion H.
    inversion H2; inversion H5.
  Case "SC_SeqStep".
    subst...
  Case "SC_IfStep".
    apply bstep_event_read_or_none in H.
    inversion H.
    inversion H2; inversion H5.
  Case "SC_Lock".
    subst...
    constructor.
    rewrite -> lks_update_neq...
Qed.


Lemma unlock_context_invariance_mem :
  forall t c c' mem mem' lks l,
    t @ (ST c [] mem lks) ==SC> (ST c' [] mem (unlock lks l)) [[EV_Unlock l]] ->
    t @ (ST c [] mem' lks) ==SC> (ST c' [] mem' (unlock lks l)) [[EV_Unlock l]].
Proof with eauto.
  Admitted.

Lemma unlock_context_invariance_lks_less :
  forall t c c' mem lks l1 l2 v2,
    l1 <> l2 ->
    t @ (ST c [] mem (lks_update lks l2 v2)) ==SC>
        (ST c' [] mem (unlock (lks_update lks l2 v2) l1)) [[EV_Unlock l1]] ->
    t @ (ST c [] mem lks) ==SC> (ST c' [] mem (unlock lks l1)) [[EV_Unlock l1]].
Proof with eauto.
  Admitted.

Lemma unlock_context_invariance_lks_more :
  forall t c c' mem lks l1 l2 v2,
    l1 <> l2 ->
    t @ (ST c [] mem lks) ==SC> (ST c' [] mem (unlock lks l1)) [[EV_Unlock l1]] ->
    t @ (ST c [] mem (lks_update lks l2 v2)) ==SC>
         (ST c' [] mem (unlock (lks_update lks l2 v2) l1)) [[EV_Unlock l1]].
Proof with eauto.
  Admitted.

Lemma none_context_invariance :
  forall t c c' mem mem' lks lks',
    t @ (ST c [] mem lks) ==SC> (ST c' [] mem lks) [[EV_None]] ->
    t @ (ST c [] mem' lks') ==SC> (ST c' [] mem' lks') [[EV_None]].
Proof with eauto.
(* TODO: this lemma I am not 100% sure *)
  Admitted.


(* end of all lemmas for:

  If a smallstep generates an event EV_XXX, then it will also generate
  this event in a slightly different context.
*)

(* ---------------------------------------------------------------- *)

(* Finally, the Diamon theorem itself: *)

Theorem diamond :
  forall cfg0 cfg1 cfg2 t1 t2 evt1 evt2,
    t1 <> t2 ->
    cfg0 --SC> cfg1 [[(t1, evt1)]] ->
    cfg1 --SC> cfg2 [[(t2, evt2)]] ->
    ~ (conflict evt1 evt2) ->
    exists cfg1', cfg0 --SC> cfg1' [[(t2, evt2)]] /\ cfg1' --SC> cfg2 [[(t1, evt1)]].
Proof with eauto.
(*
In this almost 400-lines proof, I first divide the cases of "--SC>",
when at least one step is by ending one thread, it's easy to prove
that swapping the execution order of the 2 threads can reach the same
final configuration.
*)
  intros cfg0 cfg1 cfg2 t1 t2 evt1 evt2 Ht H01 H12 Hcfl.
  generalize dependent evt2.
  generalize dependent cfg2.
  generalize dependent t2.
  inversion H01;
    intros; subst.
  Case "cfg0 --> cfg1 : CFGSC_Done".
    inversion H12; subst.
    SCase "cfg1 --> cfg2 : CFGSC_Done".
      rewrite -> remove_order_independent.
      exists (CFG (remove_tid t2 tids) thds bufs mem lks); split.
      constructor...
      constructor.
      rewrite <- remove_irrelevant...
      auto. auto.
    SCase "cfg1 --> cfg2 : CFGSC_One".
      exists (CFG tids (thds_update thds t2 c') bufs mem' lks'); split.
      apply tids_irrelevant with (remove_tid t1 tids); auto.
      rewrite <- H8; apply remove_irrelevant; auto.
      constructor...
      unfold thds_update; rewrite -> neq_tid...
  Case "cfg0 --> cfg1 : CFGSC_One".
    inversion H12; subst.
    SCase "cfg1 --> cfg2 : CFGSC_Done".
      exists (CFG (remove_tid t2 tids) thds bufs mem lks); split.
      constructor...
      unfold thds_update in H11; rewrite -> neq_tid in H11...
      apply tids_irrelevant with tids; auto.
      rewrite <- H1; symmetry; apply remove_irrelevant...
    SCase "cfg1 --> cfg2 : CFGSC_One".
(*
When both steps are by executing one thread, there are many cases to
analysize.

I choose to do case analysis on events, each event can be Read, Write,
Lock, Unlock, None. So there are 25 cases.. >_<

Generating a Rd event means: mem' = mem /\ lks' = lks
Generating a Wr event means: mem' = update mem x n /\ lks' = lks
Generating a Lk event means: mem' = mem /\ lks' = lock lks t lk
Generating a Un event means: mem' = mem /\ lks' = unlock lks lk
Generating a None event means: mem' = mem /\ lks' = lks

Then by a bunch of lemmas stated above this theorem, the proof in each
case is not hard. It's just time-consuming!
*)
      event_cases (induction evt1) SSCase.
      SSCase "EV_Read". (* evt1 : Read *)
        assert (mem = mem' /\ lks = lks').
          eapply sc_event_read; apply H6.
        inv H.
        event_cases (induction evt2) SSSCase;
          (* make it first update t2, then update t1 *)
          rewrite -> thds_update_permute.

        SSSCase "EV_Read". (* evt1 : Read / evt2 : Read *)
          assert (mem' = mem'0 /\ lks' = lks'0).
            eapply sc_event_read; apply H14.
          inv H.
          exists (CFG tids (thds_update thds t2 c'0) bufs mem'0 lks'0); split.
          rewrite -> thds_update_neq in H14...
          apply CFGSC_One with (thds t1)... auto.

        SSSCase "EV_Write". (* evt1 : Read / evt2 : Write *)
          destruct (eq_var_dec x x0); subst.
          assert (conflict (EV_Read x0) (EV_Write x0 n)) by auto.
          apply Hcfl in H; invf H. (* x = x0, evt1 & evt2 conflict *)

          assert (mem'0 = mem_update mem' x0 n /\ lks' = lks'0).
            eapply sc_event_write; apply H14.
          inv H.
          exists (CFG tids (thds_update thds t2 c'0) bufs (mem_update mem' x0 n) lks'0); split.
          rewrite -> thds_update_neq in H14...
          apply CFGSC_One with (thds t1)...
          apply read_context_invariance_mem_more... auto.

        SSSCase "EV_Lock". (* evt1 : Read / evt2 : Lock *)
          assert (mem' = mem'0 /\ lks'0 = lock lks' t2 l).
            eapply sc_event_lock; apply H14.
          inv H.
          exists (CFG tids (thds_update thds t2 c'0) bufs mem'0 (lock lks' t2 l)); split.
          rewrite -> thds_update_neq in H14...
          apply CFGSC_One with (thds t1)...
          eapply read_context_invariance_lks... auto.

        SSSCase "EV_Unlock". (* evt1 : Read / evt2 : Unlock *)
          assert (mem' = mem'0 /\ lks'0 = unlock lks' l).
            eapply sc_event_unlock; apply H14.
          inv H.
          exists (CFG tids (thds_update thds t2 c'0) bufs mem'0 (unlock lks' l)); split.
          rewrite -> thds_update_neq in H14...
          apply CFGSC_One with (thds t1)...
          eapply read_context_invariance_lks... auto.

        SSSCase "EV_None". (* evt1 : Read / evt2 : None *)
          assert (mem' = mem'0 /\ lks' = lks'0).
            eapply sc_event_none; apply H14.
          inv H.
          exists (CFG tids (thds_update thds t2 c'0) bufs mem'0 lks'0); split.
          rewrite -> thds_update_neq in H14...
          apply CFGSC_One with (thds t1)... auto.

      SSCase "EV_Write". (* evt1 : Write *)
        assert (mem' = mem_update mem x n /\ lks = lks').
          eapply sc_event_write; apply H6.
        inv H.
        event_cases (induction evt2) SSSCase;
          (* make it first update t2, then update t1 *)
          rewrite -> thds_update_permute.

        SSSCase "EV_Read". (* evt1 : Write / evt2 : Read *)
          destruct (eq_var_dec x x0); subst.
          assert (conflict (EV_Write x0 n) (EV_Read x0)) by auto.
          apply Hcfl in H; invf H. (* x = x0, evt1 & evt2 conflict *)

          assert (mem_update mem x n = mem'0 /\ lks' = lks'0).
            eapply sc_event_read; apply H14.
          inv H.
          exists (CFG tids (thds_update thds t2 c'0) bufs mem lks'0); split.
          rewrite -> thds_update_neq in H14.
          apply CFGSC_One with (thds t2)...
          eapply read_context_invariance_mem_less... auto.
          apply CFGSC_One with (thds t1)... auto.

        SSSCase "EV_Write". (* evt1 : Write / evt2 : Write *)
          destruct (eq_var_dec x x0); subst.
          assert (conflict (EV_Write x0 n) (EV_Write x0 n0)) by auto.
          apply Hcfl in H; invf H. (* x = x0, evt1 & evt2 conflict *)

          assert (mem'0 = mem_update (mem_update mem x n) x0 n0 /\ lks' = lks'0).
            eapply sc_event_write; apply H14.
          inv H.
          rewrite -> mem_update_permute.
          exists (CFG tids (thds_update thds t2 c'0) bufs (mem_update mem x0 n0) lks'0); split.
          rewrite -> thds_update_neq in H14.
          apply CFGSC_One with (thds t2)...
          eapply write_context_invariance; apply H14. auto.
          apply CFGSC_One with (thds t1)...
          eapply write_context_invariance; apply H6. auto. auto.

        SSSCase "EV_Lock". (* evt1 : Write / evt2 : Lock *)
          assert (mem_update mem x n = mem'0 /\ lks'0 = lock lks' t2 l).
            eapply sc_event_lock; apply H14.
          inv H.
          exists (CFG tids (thds_update thds t2 c'0) bufs mem (lock lks' t2 l)); split.
          rewrite -> thds_update_neq in H14.
          apply CFGSC_One with (thds t2)...
          eapply lock_context_invariance_mem; apply H14. auto.
          apply CFGSC_One with (thds t1)...
          eapply write_context_invariance; apply H6. auto.

        SSSCase "EV_Unlock". (* evt1 : Write / evt2 : Unlock *)
          assert (mem_update mem x n = mem'0 /\ lks'0 = unlock lks' l).
            eapply sc_event_unlock; apply H14.
          inv H.
          exists (CFG tids (thds_update thds t2 c'0) bufs mem (unlock lks' l)); split.
          rewrite -> thds_update_neq in H14.
          apply CFGSC_One with (thds t2)...
          eapply unlock_context_invariance_mem; apply H14. auto.
          apply CFGSC_One with (thds t1)...
          eapply write_context_invariance; apply H6. auto.

        SSSCase "EV_None". (* evt1 : Write / evt2 : None *)
          assert (mem_update mem x n = mem'0 /\ lks' = lks'0).
            eapply sc_event_none; apply H14.
          inv H.
          exists (CFG tids (thds_update thds t2 c'0) bufs mem lks'0); split.
          rewrite -> thds_update_neq in H14.
          apply CFGSC_One with (thds t2)...
          eapply none_context_invariance; apply H14. auto.
          apply CFGSC_One with (thds t1)... auto.

      SSCase "EV_Lock". (* evt1 : Lock *)
        assert (mem = mem' /\ lks' = lock lks t1 l).
          eapply sc_event_lock; apply H6.
        inv H.
        event_cases (induction evt2) SSSCase;
          (* make it first update t2, then update t1 *)
          rewrite -> thds_update_permute.

        SSSCase "EV_Read". (* evt1 : Lock / evt2 : Read *)
          assert (mem' = mem'0 /\ lock lks t1 l = lks'0).
            eapply sc_event_read; apply H14.
          inv H.
          rewrite -> thds_update_neq in H14...
          exists (CFG tids (thds_update thds t2 c'0) bufs mem'0 lks); split.
          apply CFGSC_One with (thds t2)...
          eapply read_context_invariance_lks...
          apply CFGSC_One with (thds t1)... auto.

        SSSCase "EV_Write". (* evt1 : Lock / evt2 : Write *)
          assert (mem'0 = mem_update mem' x n /\ lock lks t1 l = lks'0).
            eapply sc_event_write; apply H14.
          inv H.
          rewrite -> thds_update_neq in H14...
          exists (CFG tids (thds_update thds t2 c'0) bufs (mem_update mem' x n) lks); split.
          apply CFGSC_One with (thds t2)...
          eapply write_context_invariance; apply H14.
          apply CFGSC_One with (thds t1)...
          eapply lock_context_invariance_mem; apply H6. auto.

        SSSCase "EV_Lock". (* evt1 : Lock / evt2 : Lock *)
          destruct (eq_lid_dec l l0); subst.
          assert (conflict (EV_Lock l0) (EV_Lock l0)) by auto.
          apply Hcfl in H; invf H. (* l = l0, evt1 & evt2 conflict *)

          assert (mem' = mem'0 /\ lks'0 = lock (lock lks t1 l) t2 l0).
            eapply sc_event_lock; apply H14.
          inv H.
          unfold lock; rewrite -> lks_update_permute.
          exists (CFG tids (thds_update thds t2 c'0) bufs mem'0 (lks_update lks l0 (Some t2))); split.
          apply CFGSC_One with (thds t2)...
          rewrite -> thds_update_neq in H14...
          eapply lock_context_invariance_lks_less...
          apply CFGSC_One with (thds t1)...
          eapply lock_context_invariance_lks_more... auto. auto.

        SSSCase "EV_Unlock". (* evt1 : Lock / evt2 : Unlock *)
          destruct (eq_lid_dec l l0); subst.
          assert (conflict (EV_Lock l0) (EV_Unlock l0)) by auto.
          apply Hcfl in H; invf H. (* l = l0, evt1 & evt2 conflict *)

          assert (mem' = mem'0 /\ lks'0 = unlock (lock lks t1 l) l0).
            eapply sc_event_unlock; apply H14.
          inv H.
          unfold unlock, lock; rewrite -> lks_update_permute.
          exists (CFG tids (thds_update thds t2 c'0) bufs mem'0 (lks_update lks l0 None)); split.
          apply CFGSC_One with (thds t2)...
          rewrite -> thds_update_neq in H14...
          eapply unlock_context_invariance_lks_less...
          apply CFGSC_One with (thds t1)...
          eapply lock_context_invariance_lks_more... auto. auto.

        SSSCase "EV_None". (* evt1 : Lock / evt2 : None *)
          assert (mem' = mem'0 /\ lock lks t1 l = lks'0).
            eapply sc_event_none; apply H14.
          inv H.
          rewrite -> thds_update_neq in H14...
          exists (CFG tids (thds_update thds t2 c'0) bufs mem'0 lks); split.
          apply CFGSC_One with (thds t2)...
          eapply none_context_invariance...
          apply CFGSC_One with (thds t1)... auto.

      SSCase "EV_Unlock". (* evt1 : Unlock *)
        assert (mem = mem' /\ lks' = unlock lks l).
          eapply sc_event_unlock; apply H6.
        inv H.
        event_cases (induction evt2) SSSCase;
          (* make it first update t2, then update t1 *)
          rewrite -> thds_update_permute.

        SSSCase "EV_Read". (* evt1 : Unlock / evt2 : Read *)
          assert (mem' = mem'0 /\ unlock lks l = lks'0).
            eapply sc_event_read; apply H14.
          inv H.
          rewrite -> thds_update_neq in H14...
          exists (CFG tids (thds_update thds t2 c'0) bufs mem'0 lks); split.
          apply CFGSC_One with (thds t2)...
          eapply read_context_invariance_lks...
          apply CFGSC_One with (thds t1)... auto.

        SSSCase "EV_Write". (* evt1 : Unlock / evt2 : Write *)
          assert (mem'0 = mem_update mem' x n /\ unlock lks l = lks'0).
            eapply sc_event_write; apply H14.
          inv H.
          rewrite -> thds_update_neq in H14...
          exists (CFG tids (thds_update thds t2 c'0) bufs (mem_update mem' x n) lks); split.
          apply CFGSC_One with (thds t2)...
          eapply write_context_invariance...
          apply CFGSC_One with (thds t1)...
          eapply unlock_context_invariance_mem... auto.

        SSSCase "EV_Lock". (* evt1 : Unlock / evt2 : Lock *)
          destruct (eq_lid_dec l l0); subst.
          assert (conflict (EV_Unlock l0) (EV_Lock l0)) by auto.
          apply Hcfl in H; invf H. (* l = l0, evt1 & evt2 conflict *)

          assert (mem' = mem'0 /\ lks'0 = lock (unlock lks l) t2 l0).
            eapply sc_event_lock; apply H14.
          inv H.
          unfold lock, unlock; rewrite -> lks_update_permute.
          rewrite -> thds_update_neq in H14...
          exists (CFG tids (thds_update thds t2 c'0) bufs mem'0 (lks_update lks l0 (Some t2))); split.
          apply CFGSC_One with (thds t2)...
          eapply lock_context_invariance_lks_less...
          apply CFGSC_One with (thds t1)...
          eapply unlock_context_invariance_lks_more... auto. auto.

        SSSCase "EV_Unlock". (* evt1 : Unlock / evt2 : Unlock *)
          destruct (eq_lid_dec l l0); subst.
          assert (conflict (EV_Unlock l0) (EV_Unlock l0)) by auto.
          apply Hcfl in H; invf H. (* l = l0, evt1 & evt2 conflict *)

          assert (mem' = mem'0 /\ lks'0 = unlock (unlock lks l) l0).
            eapply sc_event_unlock; apply H14.
          inv H.
          rewrite -> thds_update_neq in H14...
          unfold unlock; rewrite -> lks_update_permute.
          exists (CFG tids (thds_update thds t2 c'0) bufs mem'0 (lks_update lks l0 None)); split.
          apply CFGSC_One with (thds t2)...
          eapply unlock_context_invariance_lks_less...
          apply CFGSC_One with (thds t1)...
          eapply unlock_context_invariance_lks_more... auto. auto.

        SSSCase "EV_None". (* evt1 : Unlock / evt2 : None *)
          assert (mem' = mem'0 /\ unlock lks l = lks'0).
            eapply sc_event_none; apply H14.
          inv H.
          rewrite -> thds_update_neq in H14...
          exists (CFG tids (thds_update thds t2 c'0) bufs mem'0 lks); split.
          apply CFGSC_One with (thds t2)...
          eapply none_context_invariance...
          apply CFGSC_One with (thds t1)... auto.

      SSCase "EV_None". (* evt1 : None *)
        assert (mem = mem' /\ lks = lks').
          eapply sc_event_none; apply H6.
        inv H.
        event_cases (induction evt2) SSSCase;
          (* make it first update t2, then update t1 *)
          rewrite -> thds_update_permute.

        SSSCase "EV_Read". (* evt1 : None / evt2 : Read *)
          assert (mem' = mem'0 /\ lks' = lks'0).
            eapply sc_event_read; apply H14.
          inv H.
          rewrite -> thds_update_neq in H14...
          exists (CFG tids (thds_update thds t2 c'0) bufs mem'0 lks'0); split.
          apply CFGSC_One with (thds t2)...
          apply CFGSC_One with (thds t1)... auto.

        SSSCase "EV_Write". (* evt1 : None / evt2 : Write *)
          assert (mem'0 = mem_update mem' x n /\ lks' = lks'0).
            eapply sc_event_write; apply H14.
          inv H.
          rewrite -> thds_update_neq in H14.
          exists (CFG tids (thds_update thds t2 c'0) bufs (mem_update mem' x n) lks'0); split.
          apply CFGSC_One with (thds t2)...
          apply CFGSC_One with (thds t1)...
          eapply none_context_invariance... auto. auto.

        SSSCase "EV_Lock". (* evt1 : None / evt2 : Lock" *)
          assert (mem' = mem'0 /\ lks'0 = lock lks' t2 l).
            eapply sc_event_lock; apply H14.
          inv H.
          rewrite -> thds_update_neq in H14.
          exists (CFG tids (thds_update thds t2 c'0) bufs mem'0 (lock lks' t2 l)); split.
          apply CFGSC_One with (thds t2)...
          apply CFGSC_One with (thds t1)...
          eapply none_context_invariance... auto. auto.

        SSSCase "EV_Unlock". (* evt1 : None / evt2 : Unlock *)
          assert (mem' = mem'0 /\ lks'0 = unlock lks' l).
            eapply sc_event_unlock; apply H14.
          inv H.
          rewrite -> thds_update_neq in H14...
          exists (CFG tids (thds_update thds t2 c'0) bufs mem'0 (unlock lks' l)); split.
          apply CFGSC_One with (thds t2)...
          apply CFGSC_One with (thds t1)...
          eapply none_context_invariance... auto.

        SSSCase "EV_None". (* evt1 : None / evt2 : None *)
          assert (mem' = mem'0 /\ lks' = lks'0).
            eapply sc_event_none; apply H14.
          inv H.
          rewrite -> thds_update_neq in H14...
          exists (CFG tids (thds_update thds t2 c'0) bufs mem'0 lks'0); split.
          apply CFGSC_One with (thds t2)...
          apply CFGSC_One with (thds t1)... auto.
Qed.
(* ---------------- end of Diamond Lemma ---------------- *)


(* ---------------- DRF Guarantee Property ---------------- *)
(* This is the ultimate theorem: "data race free programs have SC semantics" *)
Fixpoint _flushall (b : buffer) (m : memory) : memory :=
  match b with
    | nil => m
    | (x, n) :: t => _flushall t (mem_update m x n)
  end.

Fixpoint _flattening (ts : list tid) (bufs : buffer_status) (m : memory) : memory :=
  match ts with
    | nil => m
    | t :: ts' => _flattening ts' bufs (_flushall (bufs t) m)
  end.

Fixpoint flattening (cfg : configuration) : configuration :=
  match cfg with
    | CFG tids thds bufs mem lks =>
      CFG tids thds bufs (_flattening tids bufs mem) lks
  end.

Lemma flattening_empty_buffers :
  forall ts mem, _flattening ts empty_buffers mem = mem.
Proof with auto.
  intros ts.
  induction ts as [ | hd tl];
    intros; simpl...
Qed.

Hint Resolve flattening_empty_buffers.


Inductive simulation : configuration -> configuration -> configuration -> Prop :=
| Simulation : forall c0 ctso csc tr1 tr2,
                 c0 -->* ctso [[tr1]] ->
                 flattening ctso = csc ->
                 c0 --SC>* csc [[tr2]] ->
                 simulation c0 ctso csc
.

Hint Constructors simulation.


Theorem drf_guarantee :
  forall cfg ctso tr tids thds,
    (* start from initial state *)
    cfg = CFG tids thds empty_buffers empty_memory empty_locks ->
    data_race_free cfg ->
    cfg -->* ctso [[tr]]->
    exists csc, simulation cfg ctso csc.
Proof with eauto.
  intros cfg ctso tr tids thds Hcfg Hdrf Htso.
  generalize dependent thds; generalize dependent tids.
(*
  revert Hdrf. (* TODO: need this?? *)
*)
  multi_cases (induction Htso) Case;
    intros.
  Case "multi_refl".
    rename x into cfg.
    exists (flattening cfg).
    inv Hcfg; inv H; simpl; rewrite -> flattening_empty_buffers.
    apply Simulation with [] [].
    apply multi_refl...
    simpl; rewrite -> flattening_empty_buffers...
    apply multi_refl...
  Case "multi_step".
    (* TODO: Resume here *)
Qed.
(* ---------------- end of DRF Guarantee Property ---------------- *)


(* ---------------- ?? ---------------- *)
Theorem drf_must_have_unlock :
  cfg -->* cfg' with a list of evts ->
  in that list, (t1, evt1) < (t2, evt2) ->
  evt1 and evt2 have data-race ->
  exists (t1, unlock) between (t1, evt1) and (t2, evt2) in the list.
(* Gustavo didn't prove this, so he's not sure about the difficulty,
if hard, make this an axiom. *)

