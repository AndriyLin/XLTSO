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
Updated: 04/25/2014


Structure:
* Variable
* Memory
* Thread ID
* Locks
* Write Buffer
* Arithmatic Expression
* Boolean Expression
* Commands & State (uni-thread)
* Threads & Configuration (multi-threads)
* Proof of TSO Semantics
* Data-Race-Free
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

(* For simplicity (without checking program correctness), it won't
crush even if t doesn't hold the lock. *)
Definition unlock (st : lock_status) (t : tid) (l : lid) : lock_status :=
  match st l with
    | Some t' => if eq_tid_dec t t'
                 then fun l' => if eq_lid_dec l l' then None else st l'
                 else st (* bad attempt *)
    | None => st (* bad attempt *)
  end.

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
  destruct (st l) eqn:Hl...
  destruct (eq_tid_dec t t0)...
  inv H.
  assert (t = t) by auto.
  apply n in H; inv H.
Qed.

End TestLocks.
(* ---------------- end of Lock ---------------- *)


(* ---------------- Write Buffer ---------------- *)
(* In the buffer: [old ... new], new writes are appended to the right *)
Definition buffer : Type := list (var * nat).

(* Add a new write to the end of buffer *)
Fixpoint write (b : buffer) (x : var) (n : nat) : buffer :=
  match b with
    | nil => [(x, n)]
    | h :: t => h :: write t x n
  end.

(* get the oldest write in the buffer *)
Definition oldest (b : buffer) : option (var * nat) :=
  hd b.

Hint Unfold oldest.

(* remove the oldest one in the buffer *)
Definition flush (b : buffer) : buffer :=
  tl b.

Hint Unfold flush.


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
    rewrite -> IHt.
    destruct h...
Qed.

End TestWriteBuffer.
(* ---------------- end of Write Buffer ---------------- *)


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

Reserved Notation "a1 '/-' b '~' m '==A>' a2" (at level 80).

Inductive astep : buffer -> memory -> aexp -> aexp -> Prop :=
| AS_Plus : forall b m n1 n2,
              (APlus (ANum n1) (ANum n2)) /- b ~ m ==A> ANum (n1 + n2)
| AS_Plus1 : forall b m a1 a1' a2,
               a1 /- b ~ m ==A> a1' ->
               (APlus a1 a2) /- b ~ m ==A> (APlus a1' a2)
| AS_Plus2 : forall b m a1 a2 a2',
               avalue a1 ->
               a2 /- b ~ m ==A> a2' ->
               (APlus a1 a2) /- b ~ m ==A> (APlus a1 a2')

| AS_Minus : forall b m n1 n2,
               AMinus (ANum n1) (ANum n2) /- b ~ m ==A> ANum (n1 - n2)
| AS_Minus1 : forall b m a1 a1' a2,
                a1 /- b ~ m ==A> a1' ->
                (AMinus a1 a2) /- b ~ m ==A> (AMinus a1' a2)
| AS_Minus2 : forall b m a1 a2 a2',
                avalue a1 ->
                a2 /- b ~ m ==A> a2' ->
                (AMinus a1 a2) /- b ~ m ==A> (AMinus a1 a2')

| AS_Mult : forall b m n1 n2,
              AMult (ANum n1) (ANum n2) /- b ~ m ==A> ANum (n1 * n2)
| AS_Mult1 : forall b m a1 a1' a2,
               a1 /- b ~ m ==A> a1' ->
               (AMult a1 a2) /- b ~ m ==A> (AMult a1' a2)
| AS_Mult2 : forall b m a1 a2 a2',
               avalue a1 ->
               a2 /- b ~ m ==A> a2' ->
               (AMult a1 a2) /- b ~ m ==A> (AMult a1 a2')

| AS_VarBuf : forall b m x n,
                get b x = Some n ->
                (AVar x) /- b ~ m ==A> (ANum n)
| AS_VarMem : forall b m x,
                get b x = None ->
                (AVar x) /- b ~ m ==A> ANum (m x)

where "a1 '/-' b '~' m '==A>' a2" := (astep b m a1 a2).

Hint Constructors astep.

Tactic Notation "astep_cases" tactic(first) ident(c) :=
  first;
  [ Case_aux c "AS_Plus" | Case_aux c "AS_Plus1" | Case_aux c "AS_Plus2"
  | Case_aux c "AS_Minus" | Case_aux c "AS_Minus1" | Case_aux c "AS_Minus2"
  | Case_aux c "AS_Mult" | Case_aux c "AS_Mult1" | Case_aux c "AS_Mult2"
  | Case_aux c "AS_VarBuf" | Case_aux c "AS_VarMem" ].

Theorem strong_progress_a :
  forall a b m, avalue a \/ (exists a', a /- b ~ m ==A> a').
Proof with eauto.
  intros.
  aexp_cases (induction a) Case;
    simpl...
  Case "APlus".
    right. inv IHa1.
    SCase "avalue a1". inv IHa2.
      SSCase "avalue a2". inv H. inv H0...
      SSCase "a2 ==A> a2'". inv H0...
    SCase "a1 ==A> a1'". inv H...
  Case "AMinus".
    right. inv IHa1.
    SCase "avalue a1". inv IHa2.
      SSCase "avalue a2". inv H. inv H0...
      SSCase "a2 ==A> a2'". inv H0...
    SCase "a1 ==A> a1'". inv H...
  Case "AMult".
    right. inv IHa1.
    SCase "avalue a1". inv IHa2.
      SSCase "avalue a2". inv H. inv H0...
      SSCase "a2 ==A> a2'". inv H0...
    SCase "a1 ==A> a1'". inv H...
  Case "AVar".
    right.
    destruct (get b v) eqn:Hb...
Qed.


Theorem astep_deterministic: forall b m a a1 a2,
                               a /- b ~ m ==A> a1 ->
                               a /- b ~ m ==A> a2 ->
                               a1 = a2.
Proof with auto.
  intros.
  generalize dependent a2.
  astep_cases (induction H) Case;
    intros.
  Case "AS_Plus".
    inv H0...
    invf H5.
    invf H6.
  Case "AS_Plus1".
    inv H0; try solve by inversion 1.
    rewrite -> (IHastep a1'0)...
    inv H5; inv H.
  Case "AS_Plus2".
    inv H1; try solve by inversion 1.
    inv H; inv H7.
    rewrite -> (IHastep a2'0)...
  Case "AS_Minus".
    inv H0...
    invf H5.
    invf H6.
  Case "AS_Minus1".
    inv H0; try solve by inversion 1.
    rewrite -> (IHastep a1'0)...
    inv H5; inv H.
  Case "AS_Minus2".
    inv H1; try solve by inversion 1.
    inv H; invf H7.
    rewrite -> (IHastep a2'0)...
  Case "AS_Mult".
    inv H0...
    invf H5.
    invf H6.
  Case "AS_Mult1".
    inv H0; try solve by inversion 1.
    rewrite -> (IHastep a1'0)...
    inv H5; invf H.
  Case "AS_Mult2".
    inv H1; try solve by inversion 1.
    inv H; invf H7.
    rewrite -> (IHastep a2'0)...
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

Reserved Notation "b1 '/-' buf '~' mem '==B>' b2" (at level 80).

Inductive bstep : buffer -> memory -> bexp -> bexp -> Prop :=
| BS_Not : forall buf mem b,
             BNot (BBool b) /- buf ~ mem ==B> BBool (negb b)
| BS_Not1 : forall buf mem b b',
              b /- buf ~ mem ==B> b' ->
              (BNot b) /- buf ~ mem ==B> BNot b'

| BS_And : forall buf mem b1 b2,
             (BAnd (BBool b1) (BBool b2)) /- buf ~ mem ==B> BBool (andb b1 b2)
| BS_And1 : forall buf mem be1 be1' be2,
              be1 /- buf ~ mem ==B> be1' ->
              (BAnd be1 be2) /- buf ~ mem ==B> BAnd be1' be2
| BS_And2 : forall buf mem be1 be2 be2',
              bvalue be1 ->
              be2 /- buf ~ mem ==B> be2' ->
              (BAnd be1 be2) /- buf ~ mem ==B> BAnd be1 be2'

| BS_Eq : forall buf mem n1 n2,
            (BEq (ANum n1) (ANum n2)) /- buf ~ mem ==B> BBool (beq_nat n1 n2)
| BS_Eq1 : forall buf mem a1 a1' a2,
             a1 /- buf ~ mem ==A> a1' ->
             (BEq a1 a2) /- buf ~ mem ==B> BEq a1' a2
| BS_Eq2 : forall buf mem a1 a2 a2',
             avalue a1 ->
             a2 /- buf ~ mem ==A> a2' ->
             (BEq a1 a2) /- buf ~ mem ==B> BEq a1 a2'

| BS_Le : forall buf mem n1 n2,
            (BLe (ANum n1) (ANum n2)) /- buf ~ mem ==B> BBool (ble_nat n1 n2)
| BS_Le1 : forall buf mem a1 a1' a2,
             a1 /- buf ~ mem ==A> a1' ->
             (BLe a1 a2) /- buf ~ mem ==B> BLe a1' a2
| BS_Le2 : forall buf mem a1 a2 a2',
             avalue a1 ->
             a2 /- buf ~ mem ==A> a2' ->
             (BLe a1 a2) /- buf ~ mem ==B> BLe a1 a2'

where "b1 '/-' buf '~' mem '==B>' b2" := (bstep buf mem b1 b2).

Hint Constructors bstep.

Tactic Notation "bstep_cases" tactic(first) ident(c) :=
  first;
  [ Case_aux c "BS_Not" | Case_aux c "BS_Not1"
  | Case_aux c "BS_And" | Case_aux c "BS_And1" | Case_aux c "BS_And2"
  | Case_aux c "BS_Eq" | Case_aux c "BS_Eq1" | Case_aux c "BS_Eq2"
  | Case_aux c "BS_Le" | Case_aux c "BS_Le1" | Case_aux c "BS_Le2" ].

Theorem strong_progress_b :
  forall b buf mem, bvalue b \/ (exists b', b /- buf ~ mem ==B> b').
Proof with eauto.
  intros.
  bexp_cases (induction b) Case;
    simpl...
  Case "BNot".
    right. inv IHb.
    inv H...
    inv H...
  Case "BAnd".
    right. inv IHb1; inv IHb2...
    inv H; inv H0...
    inv H0...
    inv H...
    inv H; inv H0...
  Case "BEq".
    right; rename a into a1; rename a0 into a2.
    destruct (strong_progress_a a1 buf mem).
    SCase "avalue a1".
      destruct (strong_progress_a a2 buf mem).
      inv H; inv H0...
      inv H0...
    SCase "a1 ==A> a1'".
      inv H...
  Case "BLe".
    right; rename a into a1; rename a0 into a2.
    destruct (strong_progress_a a1 buf mem).
    SCase "avalue a1".
      destruct (strong_progress_a a2 buf mem).
      inv H; inv H0...
      inv H0...
    SCase "a1 ==A> a1'".
      inv H...
Qed.


Theorem bstep_deterministic:
  forall buf mem b b1 b2,
    b /- buf ~ mem ==B> b1 ->
    b /- buf ~ mem ==B> b2 ->
    b1 = b2.
Proof with auto.
  intros.
  generalize dependent b2.
  bstep_cases (induction H) Case;
    intros.
  Case "BS_Not".
    inv H0...
    invf H3.
  Case "BS_Not1".
    inv H0...
    invf H.
    rewrite -> (IHbstep b'0)...
  Case "BS_And".
    inv H0; try solve by inversion 1...
  Case "BS_And1".
    inv H0; try solve by inversion 1...
    rewrite -> (IHbstep be1'0)...
    inv H5; invf H.
  Case "BS_And2".
    inv H1; try solve by inversion 1...
    inv H; invf H7.
    rewrite -> (IHbstep be2'0)...
  Case "BS_Eq".
    inv H0; try solve by inversion 1...
  Case "BS_Eq1".
    inv H0; try solve by inversion 1...
    assert (a1' = a1'0) by eauto.
    subst...
    inv H5; invf H.
  Case "BS_Eq2".
    inv H1...
    invf H0.
    inv H; invf H7.
    assert (a2' = a2'0) by eauto.
    subst...
  Case "BS_Le".
    inv H0; try solve by inversion 1...
  Case "BS_Le1".
    inv H0; try solve by inversion 1...
    assert (a1' = a1'0) by eauto.
    subst...
    inv H5; invf H.
  Case "BS_Le2".
    inv H1; try solve by inversion 1...
    inv H; invf H7.
    assert (a2' = a2'0) by eauto.
    subst...
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


(* Although using word "value", it actually means unable to move forward *)
Inductive stvalue : tid -> state -> Prop :=
| STV_End : forall t mem lks,
              stvalue t (ST SKIP nil mem lks)
| STV_Stuck : forall t t' l buf mem lks,
                lks l = Some t' ->
                t <> t' ->
                stvalue t (ST (LOCK l) buf mem lks)
.

Hint Constructors stvalue.

Reserved Notation "t '@' st1 '==>' st2" (at level 80).

Inductive ststep : tid -> state -> state -> Prop :=
| ST_Ass : forall t x n buf mem lks,
             t @ (ST (x ::= ANum n) buf mem lks) ==>
               (ST SKIP (write buf x n) mem lks)
| ST_AssStep : forall t x a a' buf mem lks,
                 a /- buf ~ mem ==A> a' ->
                 t @ (ST (x ::= a) buf mem lks) ==> (ST (x ::= a') buf mem lks)

| ST_Seq : forall t c2 buf mem lks,
             t @ (ST (SKIP ;; c2) buf mem lks) ==> (ST c2 buf mem lks)
| ST_SeqStep : forall t c1 c1' c2 buf mem lks buf' mem' lks',
                 t @ (ST c1 buf mem lks) ==> (ST c1' buf' mem' lks') ->
                 t @ (ST (c1 ;; c2) buf mem lks) ==> (ST (c1' ;; c2) buf' mem' lks')

| ST_IfTrue : forall t c1 c2 buf mem lks,
                t @ (ST (IFB (BBool true) THEN c1 ELSE c2 FI) buf mem lks) ==>
                  (ST c1 buf mem lks)
| ST_IfFalse : forall t c1 c2 buf mem lks,
                 t @ (ST (IFB (BBool false) THEN c1 ELSE c2 FI) buf mem lks) ==>
                   (ST c2 buf mem lks)
| ST_IfStep : forall t c1 c2 be be' buf mem lks,
                be /- buf ~ mem ==B> be' ->
                t @ (ST (IFB be THEN c1 ELSE c2 FI) buf mem lks) ==>
                  (ST (IFB be' THEN c1 ELSE c2 FI) buf mem lks)

| ST_While : forall t b c buf mem lks,
               t @ (ST (WHILE b DO c END) buf mem lks) ==>
                 (ST (IFB b THEN (c ;; (WHILE b DO c END)) ELSE SKIP FI) buf mem lks)

| ST_FlushOne : forall t buf mem lks x n c,
               (* Here no matter blocked or not, it can flush anyway *)
               oldest buf = Some (x, n) ->
               t @ (ST c buf mem lks) ==> (ST c (flush buf) (update mem x n) lks)

| ST_LockDone : forall t buf mem lks lk,
                  lks lk = None \/ lks lk = Some t ->
                  t @ (ST (LOCK lk) buf mem lks) ==>
                    (ST SKIP buf mem (lock lks t lk))
| ST_LockStuck : forall t t' buf mem lks lk,
                   lks lk = Some t' ->
                   t <> t' ->
                   t @ (ST (LOCK lk) buf mem lks) ==> (ST (LOCK lk) buf mem lks)
| ST_Unlock : forall t buf mem lks lk,
                (* For simplicity, I don't check the validity of this action, it won't
                   change the state anyway if t doesn't hold the lock *)
                (* lks lk = Some t -> *)
                t @ (ST (UNLOCK lk) buf mem lks) ==>
                  (ST SKIP buf mem (unlock lks t lk))

where "t1 '@' st1 '==>' st2" := (ststep t1 st1 st2).

Hint Constructors ststep.

Tactic Notation "ststep_cases" tactic(first) ident(c) :=
  first;
  [ Case_aux c "ST_Ass" | Case_aux c "ST_AssStep"
  | Case_aux c "ST_Seq" | Case_aux c "ST_SeqStep"
  | Case_aux c "ST_IfTrue" | Case_aux c "ST_IfFalse"
  | Case_aux c "ST_IfStep" | Case_aux c "ST_While"
  | Case_aux c "ST_FlushOne" | Case_aux c "ST_LockDone"
  | Case_aux c "ST_LockStuck" | Case_aux c "ST_Unlock"
  ].


Theorem strong_progress_st :
  forall c buf mem lks t,
    stvalue t (ST c buf mem lks) \/ (exists st', t @ (ST c buf mem lks) ==> st').
Proof with eauto.
  intros c.
  cmd_cases (induction c) Case;
    intros; simpl...
  Case "SKIP".
    destruct buf...
    right.
    destruct p.
    exists (ST SKIP buf (update mem v n) lks)...
    apply ST_FlushOne...
  Case "::=".
    right; destruct (strong_progress_a a buf mem)...
    inv H...
    inv H...
  Case ";;".
    right; destruct (IHc1 buf mem lks t).
    inv H...
    inv H; destruct x...
  Case "IFB".
    right; destruct (strong_progress_b b buf mem)...
    inv H; destruct b0...
    inv H...
  Case "LOCK".
    destruct (lks l) eqn:Hl...
    destruct (eq_tid_dec t t0); subst...
Qed.


(* When a thread get stuck, it can resume when that lock is released *)
Theorem thread_stuck_resume:
  forall t l buf mem lks lks',
    stvalue t (ST (LOCK l) buf mem lks) ->
    lks' l = None \/ lks' l = Some t ->
    exists st', t @ (ST (LOCK l) buf mem lks') ==> st'.
Proof. eauto. Qed.


(* ststep is no longer deterministic, one state may execute one
command, it may also flush one unit of its write buffer to memory *)
Theorem ststep_not_deterministic:
  ~ (forall t st st1 st2,
       t @ st ==> st1 ->
       t @ st ==> st2 ->
       st1 = st2).
Proof with auto.
  intros Hf.
  remember (SKIP ;; SKIP) as c.
  remember ([(X, 100)]) as buf.
  remember (ST c buf empty_memory empty_locks) as st.
  remember (ST SKIP buf empty_memory empty_locks) as st1.
  remember (ST c nil (update empty_memory X 100) empty_locks) as st2.
  assert (T0 @ st ==> st1).
    subst...
  assert (T0 @ st ==> st2).
    subst.
    apply ST_FlushOne.
    simpl...
  assert (st1 = st2).
    eapply Hf.
    apply H.
    assumption.
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
  cfg_lks : lock_status
}.

Hint Constructors configuration.

Definition empty_configuration :=
  CFG empty_tids empty_threads empty_memory empty_locks.


Inductive cfgvalue : configuration -> Prop :=
(* All threads finish *)
| CFGV_End : forall thds mem lks,
               cfgvalue (CFG empty_tids thds mem lks)
(* Deadlock *)
(*| CFGV_Deadlock: TODO *)
.

Hint Constructors cfgvalue.

Reserved Notation "cfg1 '-->' cfg2" (at level 60).

Inductive cfgstep : configuration -> configuration -> Prop :=
(* One thread already ends its job, thus remove it *)
| CFGS_Done : forall t tids thds mem lks,
                in_tids t tids = true ->
                thds t = (SKIP, nil) ->
                (CFG tids thds mem lks) --> (CFG (remove_tid t tids) thds mem lks)

(* One thread can move one step forward, in terms of "state" *)
| CFGS_One : forall t tids thds c c' b b' mem mem' lks lks',
               in_tids t tids = true ->
               thds t = (c, b) ->
               t @ (ST c b mem lks) ==> (ST c' b' mem' lks') ->
               (CFG tids thds mem lks) --> (CFG tids (override thds t c' b') mem' lks')

where "cfg1 '-->' cfg2" := (cfgstep cfg1 cfg2).

Hint Constructors cfgstep.

Tactic Notation "cfgstep_cases" tactic(first) ident(c) :=
  first;
  [ Case_aux c "CFG_Done" | Case_aux c "CFG_One" ].


(* used in init_cfg() *)
Fixpoint _init_cfg (lc : list cmd) (n : nat) (accu : configuration) : configuration :=
  match lc with
    | nil => accu
    | h :: tlc =>
      match accu with
        | CFG tids thds mem lks =>
          let t := TID n in
          let accu' := CFG (add_tid t tids) (override thds t h nil) mem lks in
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
  forall tids thds mem lks,
    init_cfg codes = (CFG tids thds mem lks) ->
    size_tids tids = 2 /\ in_tids T0 tids = true /\ in_tids T1 tids = true
    /\ thds T0 = (proc0, nil) /\ thds T1 = (proc1, nil).
Proof.
  intros.
  unfold codes, proc0, proc1, init_cfg in *.
  inv H.
  auto.
Qed.

(* The following is to prove that the final state is actually
reachable by the language and semantics I defined above *)
Theorem tso_semantics:
  exists thds mem lks,
    init_cfg codes -->* (CFG empty_tids thds mem lks) /\
    cfgvalue (CFG empty_tids thds mem lks) /\ (* final state *)
    mem EAX = 1 /\ mem EBX = 0 /\ mem X = 1.
Proof with eauto.
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
  auto.
Qed.

End TsoSemanticsProof.
(* ---------------- end of Proof of having TSO Semantics ---------------- *)


(* ---------------- Data-Race-Free ---------------- *)
(* the variable is just about to be written *)
Inductive writes : cmd -> var -> Prop :=
| WritesInAss : forall x ae,
                  avalue ae ->
                  writes (x ::= ae) x
| WritesInSeq : forall x c1 c2,
                  writes c1 x ->
                  writes (c1 ;; c2) x
.
(* Note: Only 2 cases above can write a variable immediately. IF &
WHILE needs further steps. *)

Hint Constructors writes.

Tactic Notation "writes_cases" tactic(first) ident(c) :=
  first;
  [ Case_aux c "WritesInAss" | Case_aux c "WritesInSeq" ].


(* the variable is just about to be evaluated, used in reads *)
Inductive var_in_aexp : var -> aexp -> Prop :=
| VIA_Var : forall x,
              var_in_aexp x (AVar x)

| VIA_Plus1 : forall x a1 a2,
                var_in_aexp x a1 ->
                var_in_aexp x (APlus a1 a2)
| VIA_Plus2 : forall x a1 a2,
                avalue a1 ->
                var_in_aexp x a2 ->
                var_in_aexp x (APlus a1 a2)

| VIA_Minus1 : forall x a1 a2,
                 var_in_aexp x a1 ->
                 var_in_aexp x (AMinus a1 a2)
| VIA_Minus2 : forall x a1 a2,
                 avalue a1 ->
                 var_in_aexp x a2 ->
                 var_in_aexp x (AMinus a1 a2)

| VIA_Mult1 : forall x a1 a2,
                var_in_aexp x a1 ->
                var_in_aexp x (AMult a1 a2)
| VIA_Mult2 : forall x a1 a2,
                avalue a1 ->
                var_in_aexp x a2 ->
                var_in_aexp x (AMult a1 a2)
.

Hint Constructors var_in_aexp.

Tactic Notation "var_in_aexp_cases" tactic(first) ident(c) :=
  first;
  [ Case_aux c "VIA_Var"
  | Case_aux c "VIA_Plus1" | Case_aux c "VIA_Plus2"
  | Case_aux c "VIA_Minus1" | Case_aux c "VIA_Minus2"
  | Case_aux c "VIA_Mult1" | Case_aux c "VIA_Mult2" ].


(* x is just about to be evaluated in bexp, used in reads *)
Inductive var_in_bexp : var -> bexp -> Prop :=
| VIB_Not : forall x be,
              var_in_bexp x be ->
              var_in_bexp x (BNot be)

| VIB_And1 : forall x be1 be2,
               var_in_bexp x be1 ->
               var_in_bexp x (BAnd be1 be2)
| VIB_And2 : forall x be1 be2,
               bvalue be1 ->
               var_in_bexp x be2 ->
               var_in_bexp x (BAnd be1 be2)

| VIB_Eq1 : forall x a1 a2,
              var_in_aexp x a1 ->
              var_in_bexp x (BEq a1 a2)
| VIB_Eq2 : forall x a1 a2,
              avalue a1 ->
              var_in_aexp x a2 ->
              var_in_bexp x (BEq a1 a2)

| VIB_Le1 : forall x a1 a2,
              var_in_aexp x a1 ->
              var_in_bexp x (BLe a1 a2)
| VIB_Le2 : forall x a1 a2,
              avalue a1 ->
              var_in_aexp x a2 ->
              var_in_bexp x (BLe a1 a2)
.

Hint Constructors var_in_bexp.

Tactic Notation "var_in_bexp_cases" tactic(first) ident(c) :=
  first;
  [ Case_aux c "VIB_Not"
  | Case_aux c "VIB_And1" | Case_aux c "VIB_And2"
  | Case_aux c "VIB_Eq1" | Case_aux c "VIB_Eq2"
  | Case_aux c "VIB_Le1" | Case_aux c "VIB_Le2" ].


(* the variable is just about to be evaluated in the command*)
Inductive reads : cmd -> var -> Prop :=
| ReadsInAss : forall x y a,
                 var_in_aexp y a ->
                 reads (x ::= a) y
| ReadsInIf : forall b c1 c2 x,
                var_in_bexp x b ->
                reads (IFB b THEN c1 ELSE c2 FI) x
| ReadsInSeq : forall c1 c2 x,
                 reads c1 x ->
                 reads (c1 ;; c2) x
.
(* Note: Only the 3 cases above can read a var immediately. WHILE is
expanded to "if b then while else skip end" in the semantics so there
is no need to add WHILE here *)

Hint Constructors reads.

Tactic Notation "reads_cases" tactic(first) ident(c) :=
  first;
  [ Case_aux c "ReadsInAss"
  | Case_aux c "ReadsInIf"
  | Case_aux c "ReadsInSeq" ].


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

(* TODO: Define Data-Race-Free *)

(* ---------------- end of Data-Race-Free ---------------- *)


(* Doubts: Do I need to use events to abstract? Yes, I may define
that: two xx are equiv if they have the same sequence of events *)

