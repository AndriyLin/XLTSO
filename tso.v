(**

This is for the final project of CS565 Programming Languages in
Purdue.

Write a simple programming language that exposes relaxed memory
semantics (e.g. TSO). Prove that data race free programs have SC
semantics.

Written in Coq, mechanically formalized and verified.

Contraints:
* It is only a simple language, so the only possible value is nat.
* If var is not in memory, it will return 0 as default value, rather than None.

Andriy LIN
Updated: 04/16/2014


Structure:
* Variable
* Main memory
* Thread ID
* LockID and Locks
* Write Buffers
* State
* Arithmatic Expressions
* Boolean Expressions
* Commands
* TODO..
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


(* ---------------- Main Memory ---------------- *)
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
(* ---------------- end of Main Memory ---------------- *)


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
crush even t doesn't hold the lock. *)
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

(*
Definition buffer_status : Type := tid -> buffer.

Definition empty_buffers : buffer_status :=
  fun _ => nil.

Definition write (bs : buffer_status) (t : tid) (x : var) (n : nat) : buffer_status :=
  fun t' => if eq_tid_dec t t'
            then _write (bs t) x n
            else bs t'.

Hint Unfold write.

(* remove the oldest write in the buffer *)
Definition flush (bs : buffer_status) (t : tid) : buffer_status :=
  fun t' => if eq_tid_dec t t'
            then tl (bs t)
            else bs t'.

Hint Unfold flush.

Theorem test_write_correctness:
  forall t x n, oldest (write empty_buffers t x n) t = Some (x, n).
Proof with auto.
  intros.
  unfold write, oldest.
  rewrite -> eq_tid...
Qed.

Theorem test_flush_correctness:
  forall t x n, flush (write empty_buffers t x n) t = empty_buffers.
Proof with auto.
  intros.
  apply functional_extensionality.
  intros t'.
  unfold flush, write, empty_buffers.
  rewrite -> eq_tid.
  destruct (eq_tid_dec t t')...
Qed.

Definition get (bs : buffer_status) (t : tid) (x : var) : option nat :=
  _get (bs t) x.

Theorem test_get_correctness:
  forall bs t x n1 n2, get (write (write bs t x n1) t x n2) t x = Some n2.
Proof with auto.
  intros.
  unfold write, get.
  repeat rewrite -> eq_tid.
  induction (bs t) as [ | hd tl];
    simpl.
  Case "bs t = nil".
    repeat rewrite -> eq_var...
  Case "bs t = hd :: tl".
    rewrite -> IHtl.
    destruct hd...
Qed.
*)
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


Ltac find_avalue_astep :=
  match goal with
      H1: ANum ?n /- ?b ~ ?m ==A> ?a' |- _ => invf H1
  end.

Ltac find_avalue :=
  match goal with
      H1: avalue ?a |- _ => inv H1
  end.

Theorem astep_deterministic: forall b m a a1 a2,
                               a /- b ~ m ==A> a1 ->
                               a /- b ~ m ==A> a2 ->
                               a1 = a2.
Proof with auto.
  intros.
  generalize dependent a2.
  astep_cases (induction H) Case;
    intros; simpl;
    inv H0;
    auto;
    repeat find_avalue;
    try (find_avalue_astep).
  Case "AS_Plus1".
    rewrite -> (IHastep _ H6)...
    inv H1; try find_avalue_astep.
    inv H6; find_avalue; try find_avalue_astep...
  Case "AS_Plus2".
    inv H1; try find_avalue_astep.
    rewrite -> (IHastep _ H7)...
(* TODO: too many details here, think of another way to prove this! *)
    Admitted.

Hint Resolve astep_deterministic.

(* TODO: Do I need to prove any corollary as that in Smallstep.v?
May be used in proof of deterministic.
Corollary nf_same_as_value : forall t,
  normal_form step t <-> value t.
*)
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

Ltac find_bvalue_bstep :=
  match goal with
      H1: BBool ?b /- ?buf ~ ?mem ==B> ?b' |- _ => invf H1
  end.

Ltac find_bvalue :=
  match goal with
      H1: bvalue ?a |- _ => inv H1
  end.


Theorem bstep_deterministic:
  forall buf mem b b1 b2,
    b /- buf ~ mem ==B> b1 ->
    b /- buf ~ mem ==B> b2 ->
    b1 = b2.
Proof with auto.
  intros.
  generalize dependent b2.
  bstep_cases (induction H) Case;
    intros; inv H0;
    try find_bvalue;
    try find_bvalue_bstep;
    auto.
  Case "BS_Not1".
    rewrite (IHbstep _ H4)...
  Case "BS_And1".
    rewrite (IHbstep _ H6)...
  Case "BS_And2".
    inv H1.
    Admitted.
(* TODO: excruciating.. *)

(* TODO: Do I need to prove any corollary as that in Smallstep.v?
May be used in proof of deterministic.
Corollary nf_same_as_value : forall t,
  normal_form step t <-> value t.
*)
(* ---------------- end of Boolean Expressions ---------------- *)


(* ---------------- Command & State (uni) ---------------- *)
Inductive fence : Type :=
| MFENCE : fence
.

Hint Constructors fence.

Tactic Notation "fence_cases" tactic(first) ident(c) :=
  first;
  [ Case_aux c "MFENCE" ].


Inductive cmd : Type :=
| CSkip : cmd
| CAss : var -> aexp -> cmd
| CSeq : cmd -> cmd -> cmd
| CIf : bexp -> cmd -> cmd -> cmd
| CWhile : bexp -> cmd -> cmd
| CBar : fence -> cmd (* Barrier *)
| CLock : lid -> cmd
| CUnlock : lid -> cmd
(* TODO: CAtomic?? *)
.

Hint Constructors cmd.

Tactic Notation "cmd_cases" tactic(first) ident(c) :=
  first;
  [ Case_aux c "SKIP" | Case_aux c "::=" | Case_aux c ";;"
  | Case_aux c "IFB" | Case_aux c "WHILE"
  | Case_aux c "BAR"
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
Notation "'BAR' f" :=
  (CBar f) (at level 80).
Notation "'LOCK' l" :=
  (CLock l) (at level 80).
Notation "'UNLOCK' l" :=
  (CUnlock l) (at level 80).


(* state contains all that ONE single thread can change *)
Record state := ST {
  st_cmd : cmd;
  st_buf : buffer;
  st_mem : memory;
  st_lks : lock_status
}.

Hint Constructors state.


(* Although using word "value", it actually means unable to move forward *)
Inductive cvalue : tid -> state -> Prop :=
| CV_End : forall t mem lks,
             cvalue t (ST SKIP nil mem lks)
| CV_Stuck : forall t t' l buf mem lks,
               lks l = Some t' ->
               t <> t' ->
               cvalue t (ST (LOCK l) buf mem lks)
.

Hint Constructors cvalue.

Reserved Notation "t '@' st1 '==>' st2" (at level 80).

Inductive cstep : tid -> state -> state -> Prop :=
| CS_Ass : forall t x n buf mem lks,
             t @ (ST (x ::= ANum n) buf mem lks) ==>
               (ST SKIP (write buf x n) mem lks)
| CS_AssStep : forall t x a a' buf mem lks,
                 a /- buf ~ mem ==A> a' ->
                 t @ (ST (x ::= a) buf mem lks) ==> (ST (x ::= a') buf mem lks)

| CS_Seq : forall t c2 buf mem lks,
             t @ (ST (SKIP ;; c2) buf mem lks) ==> (ST c2 buf mem lks)
| CS_SeqStep : forall t c1 c1' c2 buf mem lks buf' mem' lks',
                 t @ (ST c1 buf mem lks) ==> (ST c1' buf' mem' lks') ->
                 t @ (ST (c1 ;; c2) buf mem lks) ==> (ST (c1' ;; c2) buf' mem' lks')

| CS_IfTrue : forall t c1 c2 buf mem lks,
                t @ (ST (IFB (BBool true) THEN c1 ELSE c2 FI) buf mem lks) ==>
                  (ST c1 buf mem lks)
| CS_IfFalse : forall t c1 c2 buf mem lks,
                 t @ (ST (IFB (BBool false) THEN c1 ELSE c2 FI) buf mem lks) ==>
                   (ST c2 buf mem lks)
| CS_IfStep : forall t c1 c2 be be' buf mem lks,
                be /- buf ~ mem ==B> be' ->
                t @ (ST (IFB be THEN c1 ELSE c2 FI) buf mem lks) ==>
                  (ST (IFB be' THEN c1 ELSE c2 FI) buf mem lks)

| CS_While : forall t b c buf mem lks,
               t @ (ST (WHILE b DO c END) buf mem lks) ==>
                 (ST (IFB b THEN (c ;; (WHILE b DO c END)) ELSE SKIP FI) buf mem lks)

| CS_Bar : forall t buf mem lks,
             oldest buf = None ->
             t @ (ST (BAR MFENCE) buf mem lks) ==> (ST SKIP buf mem lks)
| CS_Flush : forall t buf mem lks x n c,
               (* Here either blocked or not it can flush anyway *)
               oldest buf = Some (x, n) ->
               t @ (ST c buf mem lks) ==> (ST c (flush buf) (update mem x n) lks)

| CS_LockDone : forall t buf mem lks lk,
                  lks lk = None \/ lks lk = Some t ->
                  t @ (ST (LOCK lk) buf mem lks) ==>
                    (ST SKIP buf mem (lock lks t lk))
| CS_LockStuck : forall t t' buf mem lks lk,
                   lks lk = Some t' ->
                   t <> t' ->
                   t @ (ST (LOCK lk) buf mem lks) ==> (ST (LOCK lk) buf mem lks)
| CS_Unlock : forall t buf mem lks lk,
                (* For simplicity, I don't check the validity of this action, it won't
                   change the state anyway if t doesn't hold the lock *)
                (* lks lk = Some t -> *)
                t @ (ST (UNLOCK lk) buf mem lks) ==>
                  (ST SKIP buf mem (unlock lks t lk))

where "t1 '@' st1 '==>' st2" := (cstep t1 st1 st2).

Hint Constructors cstep.

Tactic Notation "cstep_cases" tactic(first) ident(c) :=
  first;
  [ Case_aux c "CS_Ass" | Case_aux c "CS_AssStep"
  | Case_aux c "CS_Seq" | Case_aux c "CS_SeqStep"
  | Case_aux c "CS_IfTrue" | Case_aux c "CS_IfFalse"
  | Case_aux c "CS_IfStep" | Case_aux c "CS_While"
  | Case_aux c "CS_Bar" | Case_aux c "CS_Flush"
  | Case_aux c "CS_LockDone" | Case_aux c "CS_LockStuck" | Case_aux c "CS_Unlock"
  ].


Theorem strong_progress_c :
  forall c buf mem lks t,
    cvalue t (ST c buf mem lks) \/ (exists st', t @ (ST c buf mem lks) ==> st').
Proof with eauto.
  intros c.
  cmd_cases (induction c) Case;
    intros; simpl...
  Case "SKIP".
    destruct buf...
    right.
    destruct p.
    exists (ST SKIP buf (update mem v n) lks)...
    apply CS_Flush...
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
  Case "BAR".
    destruct f; right.
    destruct buf...
    destruct p.
    eexists (ST (BAR MFENCE) buf (update mem v n) lks).
    apply CS_Flush...
  Case "LOCK".
    destruct (lks l) eqn:Hl...
    destruct (eq_tid_dec t t0); subst...
Qed.


(* When a thread get stuck, it can resume when that lock is released *)
Theorem thread_stuck_resume:
  forall t l buf mem lks lks',
    cvalue t (ST (LOCK l) buf mem lks) ->
    lks' l = None \/ lks' l = Some t ->
    exists st', t @ (ST (LOCK l) buf mem lks') ==> st'.
Proof. eauto. Qed.


(* cstep is no longer deterministic, one state may execute one
command, it may also flush one write to memory *)
Theorem cstep_not_deterministic:
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
    apply CS_Flush.
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


(* TODO: resume from here *)
(* ---------------- Threads & Configuration ---------------- *)
Definition threads := tid -> (cmd * buffer).

Definition empty_threads : threads :=
  fun _ => (SKIP, nil).

Hint Unfold empty_threads.


(* configuration contains everything that may be modified *)
Record configuration := CFG {
  cfg_tids : set tid;
  cfg_tds : threads;
  cfg_mem : memory;
  cfg_lks : lock_status
}.

(* ---------------- end of Thread & State (uni) & Configuration ---------------- *)



(* ---------------- State & Multi-Relation ---------------- *)
(* State consists of necessary information for a tid*cmd to execute:
   * buffer status
   * memory
   * lock status
*)
Record state := ST {
  st_bs : buffer_status;
  st_mem : memory;
  st_ls : lock_status
}.

Hint Constructors state.

Definition empty_state := ST empty_buffers empty_memory empty_locks.


(* TODO: is the relation & normal form definition here necessary?? *)
Definition relation (X:Type) := tid -> X -> X -> Prop.

Definition deterministic {X: Type} (R: relation X) :=
  forall t x y1 y2, R t x y1 -> R t x y2 -> y1 = y2.

Hint Unfold deterministic.

Inductive multi {X:Type} (R: relation X) : tid -> X -> X -> Prop :=
| multi_refl  : forall t x,
                  multi R t x x
| multi_step : forall t x y z,
                 R t x y ->
                 multi R t y z ->
                 multi R t x z.

Hint Constructors multi.

Tactic Notation "multi_cases" tactic(first) ident(c) :=
  first;
  [ Case_aux c "multi_refl" | Case_aux c "multi_step" ].

Theorem multi_R : forall (X:Type) (R:relation X) (t : tid) (x y : X),
                    R t x y -> multi R t x y.
Proof. eauto. Qed.

Hint Resolve multi_R.

Theorem multi_trans :
  forall (X:Type) (R: relation X) (t : tid) (x y z : X),
      multi R t x y  ->
      multi R t y z ->
      multi R t x z.
Proof.
  intros X R t x y z Hxy Hyz.
  multi_cases (induction Hxy) Case;
    simpl; eauto.
Qed.

Hint Resolve multi_trans.
(* ---------------- end of State & Multi-Relation ---------------- *)








(* Due to the definition of relation, normal_form is only for cstep. *)
Definition normal_form {X:Type} (R : relation X) (x : X) : Prop :=
  forall t, ~ exists x', R t x x'.





Notation "'PAR' t1 '@' c1 'WITH' t2 '@' c2 'END'" :=

| CS_Par1 : forall st c1 c1' c2 st',
              c1 / st ==> c1' / st' -> 
              (PAR c1 WITH c2 END) / st ==> (PAR c1' WITH c2 END) / st'
| CS_Par2 : forall st c1 c2 c2' st',
              c2 / st ==> c2' / st' ->
              (PAR c1 WITH c2 END) / st ==> (PAR c1 WITH c2' END) / st'
| CS_ParDone : forall st,
                 (PAR SKIP WITH SKIP END) / st ==> SKIP / st



Hint Constructors ceval.

Tactic Notation "ceval_cases" tactic(first) ident(c) :=
  first;
  [ Case_aux c "CE_Skip" | Case_aux c "CE_Ass"
  | Case_aux c "CE_Seq" | Case_aux c "CE_IfTrue"
  | Case_aux c "CE_IfFalse" | Case_aux c "CE_WhileEnd"
  | Case_aux c "CE_WhileLoop" ].


Theorem ceval_deterministic:
  forall c st st1 st2,
    c / st || st1  ->
    c / st || st2 ->
    st1 = st2.
Proof with auto.
  intros c st st1 st2 E1 E2.
  generalize dependent st2.
  ceval_cases (induction E1) Case;
           intros st2 E2; inversion E2; subst; auto;
           try find_rwinv.
  Case "CE_Seq".
    apply IHE1_1 in H1.
    subst...
  Case "CE_WhileLoop".
    SCase "b1 evaluates to true".
      apply IHE1_1 in H3.
      subst.
      apply IHE1_2...
Qed.

Hint Resolve ceval_deterministic.


(* TODO: also prove the "strong_progress" version for cstep, regarding normal_form *)
(* ---------------- end of Fence & Command ---------------- *)







(* Equivalence chapter in SF may not be used later on.
   It is likely for different kinds of optimization.
   Also, I don't think Hoare Logic would be used in the proof.
*)
(* ---------------- Equivalence ---------------- *)
(* ---------------- end of Equivalence ---------------- *)
(* ---------------- Hoare Logic ---------------- *)
Definition Assertion := state -> Prop.

Definition assert_implies (P Q : Assertion) : Prop :=
  forall st, P st -> Q st.

Hint Unfold assert_implies.

Notation "P ->> Q" :=
  (assert_implies P Q) (at level 80) : hoare_spec_scope.
Open Scope hoare_spec_scope.

Notation "P <<->> Q" :=
  (P ->> Q /\ Q ->> P) (at level 80) : hoare_spec_scope.


Definition hoare_triple (P : Assertion) (c : cmd) (Q : Assertion) : Prop :=
  forall st st', c / st || st'  ->
                 P st  ->
                 Q st'.

Hint Unfold hoare_triple.

Notation "{{ P }}  c  {{ Q }}" :=
  (hoare_triple P c Q) (at level 90, c at next level)
  : hoare_spec_scope.


Theorem hoare_skip : forall P,
                       {{P}} SKIP {{P}}.
Proof with eauto.
  unfold hoare_triple; intros.
  inversion H; subst...
Qed.

Hint Resolve hoare_skip.

Definition assn_sub X a P : Assertion :=
  fun (st : state) =>
    P (update st X (aeval st a)).

Hint Unfold assn_sub.

Notation "P [ X |-> a ]" := (assn_sub X a P) (at level 10).

Theorem hoare_asgn : forall Q X a,
                       {{Q [X |-> a]}} (X ::= a) {{Q}}.
Proof with eauto.
  unfold hoare_triple.
  intros.
  inversion H; subst...
Qed.

Hint Resolve hoare_asgn.

Theorem hoare_seq : forall P Q R c1 c2,
                      {{Q}} c2 {{R}} ->
                      {{P}} c1 {{Q}} ->
                      {{P}} c1;;c2 {{R}}.
Proof with eauto.
  unfold hoare_triple; intros.
  inversion H1; subst...
Qed.

Hint Resolve hoare_seq.

Definition bassn b : Assertion :=
  fun st => (beval st b = true).

Hint Unfold bassn.

Lemma bexp_eval_true :
  forall b st, beval st b = true -> (bassn b) st.
Proof. auto. Qed.

Hint Resolve bexp_eval_true.

Lemma bexp_eval_false : forall b st,
  beval st b = false -> ~ ((bassn b) st).
Proof.
  intros.
  unfold bassn.
  intros Hf.
  find_rwinv.
Qed.

Hint Resolve bexp_eval_false.

Theorem hoare_if :
  forall P Q b c1 c2,
    {{fun st => P st /\ bassn b st}} c1 {{Q}} ->
    {{fun st => P st /\ ~(bassn b st)}} c2 {{Q}} ->
    {{P}} (IFB b THEN c1 ELSE c2 FI) {{Q}}.
Proof with eauto.
  unfold hoare_triple; intros.
  inversion H1; subst...
Qed.

Hint Resolve hoare_if.

Lemma hoare_while : forall P b c,
  {{fun st => P st /\ bassn b st}} c {{P}} ->
  {{P}} WHILE b DO c END {{fun st => P st /\ ~ (bassn b st)}}.
Proof with eauto.
  intros P b c Hhoare st st' He HP.
  (* Like we've seen before, we need to reason by induction 
     on He, because, in the "keep looping" case, its hypotheses 
     talk about the whole loop instead of just c *)
  remember (WHILE b DO c END) as wcom eqn:Heqwcom.
  ceval_cases (induction He) Case;
    try (inv Heqwcom)...
Qed.

Hint Resolve hoare_while.

Theorem hoare_consequence_pre : forall (P P' Q : Assertion) c,
  {{P'}} c {{Q}} ->
  P ->> P' ->
  {{P}} c {{Q}}.
Proof. eauto. Qed.

Hint Resolve hoare_consequence_pre.

Theorem hoare_consequence_post : forall (P Q Q' : Assertion) c,
  {{P}} c {{Q'}} ->
  Q' ->> Q ->
  {{P}} c {{Q}}.
Proof. eauto. Qed.

Hint Resolve hoare_consequence_post.

Theorem hoare_consequence : forall (P P' Q Q' : Assertion) c,
  {{P'}} c {{Q'}} ->
  P ->> P' ->
  Q' ->> Q ->
  {{P}} c {{Q}}.
Proof. eauto. Qed.

Hint Resolve hoare_consequence.

Definition is_wp P c Q :=
  {{P}} c {{Q}} /\
  forall P', {{P'}} c {{Q}} -> (P' ->> P).

Hint Unfold is_wp.
(* ---------------- end of Hoare Logic ---------------- *)


(* ---------------- Smallstep Semantics ---------------- *)
(*
TODO: Change the operational semantics to this smallstep semantics
It's better in an parallel environment.
 *)
(* ---------------- end of Smallstep Semantics ---------------- *)


(*
Doubts:
* Do I need to specify Registers?? No.
* Do I need to specify Barriers?? I think so.
* What's the difference between MFENCE, LFENCE, SFENCE.
* Do I need to use events to abstract? maybe yes, I may define that:
    two xx are equiv if they have the same sequence of events
*)


(*
TODOs:
1. Add test cases (Example) to check the correctness of each definition above.
2. Will Hoare Logic be used in the project? I am not sure.
3. Do I need to extend the language to contain Lambda?
4. Add BOr into bexp??
*)

