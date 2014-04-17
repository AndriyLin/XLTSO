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

(* Default TID is zero, only used when haven't specified the TID *)
Definition TID_DEF : tid := TID 0.
Definition T1 : tid := TID 1.
Definition T2 : tid := TID 2.

Hint Unfold TID_DEF.
Hint Unfold T1.
Hint Unfold T2.
(* ---------------- end of Thread ID ---------------- *)


(* ---------------- Lock ---------------- *)
Inductive lid : Type :=
| LockID : nat -> lid.
(* TODO: do I need to change lid to "var -> lid"?? *)

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

Theorem test_lock_correctness:
  forall st t l, (lock st t l) l = Some t.
Proof with auto.
  intros.
  unfold lock...
Qed.

(* Again, checking of validity is not done here, it's left to semantics *)
Definition unlock (st : lock_status) (l : lid) : lock_status :=
  fun l' => if eq_lid_dec l l' then None else st l'.

Hint Unfold unlock.

Theorem test_unlock_correctness:
  forall st l, (unlock st l) l = None.
Proof with auto.
  intros.
  unfold unlock...
Qed.
(* ---------------- end of Lock ---------------- *)


(* ---------------- Write Buffer ---------------- *)
(* In the buffer: [old ... new], new writes are appended to the right *)
Definition buffer : Type := list (var * nat).
Definition buffer_status : Type := tid -> buffer.

Definition empty_buffers : buffer_status :=
  fun _ => nil.

(* Used in write() *)
Fixpoint _write (b : buffer) (x : var) (n : nat) : buffer :=
  match b with
    | nil => [(x, n)]
    | h :: t => h :: _write t x n
  end.

Hint Unfold _write.

(* Add a new write to the end of buffer *)
Definition write (bs : buffer_status) (t : tid) (x : var) (n : nat) : buffer_status :=
  fun t' => if eq_tid_dec t t'
            then _write (bs t) x n
            else bs t'.

Hint Unfold write.

(* get the oldest write in the buffer *)
Definition oldest (bs : buffer_status) (t : tid) : option (var * nat) :=
  hd (bs t).

Hint Unfold oldest.

Theorem test_write_correctness:
  forall t x n, oldest (write empty_buffers t x n) t = Some (x, n).
Proof with auto.
  intros.
  unfold write, oldest.
  rewrite -> eq_tid...
Qed.

(* remove the oldest write in the buffer *)
Definition flush (bs : buffer_status) (t : tid) : buffer_status :=
  fun t' => if eq_tid_dec t t'
            then tl (bs t)
            else bs t'.

Hint Unfold flush.

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

(* the helper function for get, the accumulator version is not useful in proof *)
Fixpoint _get (b : buffer) (x : var) : option nat :=
  match b with
    | nil => None
    | (k, v) :: t => match _get t x with
                       | None => if eq_var_dec x k
                                 then Some v
                                 else None
                       | r => r
                     end
  end.

Hint Unfold _get.

(* get the latest value of some variable in the buffer, if any *)
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
(* ---------------- end of Write Buffer ---------------- *)


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

Reserved Notation "t '@' a1 '~' st '==A>' a2" (at level 50).

Inductive astep : tid -> aexp -> state -> aexp -> Prop :=
| AS_Plus : forall t n1 n2 st,
              t @ (APlus (ANum n1) (ANum n2)) ~ st ==A> ANum (n1 + n2)
| AS_Plus1 : forall t a1 a1' a2 st,
               t @ a1 ~ st ==A> a1' ->
               t @ (APlus a1 a2) ~ st ==A> APlus a1' a2
| AS_Plus2 : forall t a1 a2 a2' st,
               avalue a1 ->
               t @ a2 ~ st ==A> a2' ->
               t @ (APlus a1 a2) ~ st ==A> APlus a1 a2'

| AS_Minus : forall t n1 n2 st,
               t @ (AMinus (ANum n1) (ANum n2)) ~ st ==A> ANum (n1 - n2)
| AS_Minus1 : forall t a1 a1' a2 st,
                t @ a1 ~ st ==A> a1' ->
                t @ (AMinus a1 a2) ~ st ==A> AMinus a1' a2
| AS_Minus2 : forall t a1 a2 a2' st,
                avalue a1 ->
                t @ a2 ~ st ==A> a2' ->
                t @ (AMinus a1 a2) ~ st ==A> AMinus a1 a2'

| AS_Mult : forall t n1 n2 st,
              t @ (AMult (ANum n1) (ANum n2)) ~ st ==A> ANum (n1 * n2)
| AS_Mult1 : forall t a1 a1' a2 st,
               t @ a1 ~ st ==A> a1' ->
               t @ (AMult a1 a2) ~ st ==A> AMult a1' a2
| AS_Mult2 : forall t a1 a2 a2' st,
               avalue a1 ->
               t @ a2 ~ st ==A> a2' ->
               t @ (AMult a1 a2) ~ st ==A> AMult a1 a2'

| AS_VarBuf : forall t x bs mem ls n,
                get bs t x = Some n ->
                t @ (AVar x) ~ (ST bs mem ls) ==A> (ANum n)
| AS_VarMem : forall t x bs mem ls,
                get bs t x = None ->
                t @ (AVar x) ~ (ST bs mem ls) ==A> (ANum (mem x))

where "t '@' a1 '~' st '==A>' a2" := (astep t a1 st a2).

Hint Constructors astep.

Tactic Notation "astep_cases" tactic(first) ident(c) :=
  first;
  [ Case_aux c "AS_Plus" | Case_aux c "AS_Plus1" | Case_aux c "AS_Plus2"
  | Case_aux c "AS_Minus" | Case_aux c "AS_Minus1" | Case_aux c "AS_Minus2"
  | Case_aux c "AS_Mult" | Case_aux c "AS_Mult1" | Case_aux c "AS_Mult2"
  | Case_aux c "AS_VarBuf" | Case_aux c "AS_VarMem" ].

Theorem strong_progress_a :
  forall a t st, avalue a \/ (exists a', t @ a ~ st ==A> a').
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
    destruct st as [bs mem ls].
    destruct (get bs t v) eqn:Hbs...
Qed.

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
| BV_Bool : forall b : bool,
              bvalue (BBool b).

Hint Constructors bvalue.

Reserved Notation "t '@' b1 '~' st '==B>' b2" (at level 50).

Inductive bstep : tid -> bexp -> state -> bexp -> Prop :=
| BS_Not : forall t st b,
             t @ (BNot (BBool b)) ~ st ==B> BBool (negb b)
| BS_Not1 : forall t st be be',
              t @ be ~ st ==B> be' ->
              t @ (BNot be) ~ st ==B> (BNot be')

| BS_And : forall t st b1 b2,
             t @ (BAnd (BBool b1) (BBool b2)) ~ st ==B> BBool (andb b1 b2)
| BS_And1 : forall t st be1 be1' be2,
              t @ be1 ~ st ==B> be1' ->
              t @ (BAnd be1 be2) ~ st ==B> BAnd be1' be2
| BS_And2 : forall t st be1 be2 be2',
              bvalue be1 ->
              t @ be2 ~ st ==B> be2' ->
              t @ (BAnd be1 be2) ~ st ==B> BAnd be1 be2'

| BS_Eq : forall t st n1 n2,
            t @ (BEq (ANum n1) (ANum n2)) ~ st ==B> BBool (beq_nat n1 n2)
| BS_Eq1 : forall t st a1 a1' a2,
             t @ a1 ~ st ==A> a1' ->
             t @ (BEq a1 a2) ~ st ==B> BEq a1' a2
| BS_Eq2 : forall t st a1 a2 a2',
             avalue a1 ->
             t @ a2 ~ st ==A> a2' ->
             t @ (BEq a1 a2) ~ st ==B> BEq a1 a2'

| BS_Le : forall t st n1 n2,
            t @ (BLe (ANum n1) (ANum n2)) ~ st ==B> BBool (ble_nat n1 n2)
| BS_Le1 : forall t st a1 a1' a2,
             t @ a1 ~ st ==A> a1' ->
             t @ (BLe a1 a2) ~ st ==B> BLe a1' a2
| BS_Le2 : forall t st a1 a2 a2',
             avalue a1 ->
             t @ a2 ~ st ==A> a2' ->
             t @ (BLe a1 a2) ~ st ==B> BLe a1 a2'

where "t '@' b1 '~' st '==B>' b2" := (bstep t b1 st b2).

Hint Constructors bstep.

Tactic Notation "bstep_cases" tactic(first) ident(c) :=
  first;
  [ Case_aux c "BS_Not" | Case_aux c "BS_Not1"
  | Case_aux c "BS_And" | Case_aux c "BS_And1" | Case_aux c "BS_And2"
  | Case_aux c "BS_Eq" | Case_aux c "BS_Eq1" | Case_aux c "BS_Eq2"
  | Case_aux c "BS_Le" | Case_aux c "BS_Le1" | Case_aux c "BS_Le2" ].

Theorem strong_progress_b :
  forall b t st, bvalue b \/ (exists b', t @ b ~ st ==B> b').
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
    destruct (strong_progress_a a1 t st).
    SCase "avalue a1".
      destruct (strong_progress_a a2 t st).
      inv H; inv H0...
      inv H0...
    SCase "a1 ==A> a1'".
      inv H...
  Case "BLe".
    right; rename a into a1; rename a0 into a2.
    destruct (strong_progress_a a1 t st).
    SCase "avalue a1".
      destruct (strong_progress_a a2 t st).
      inv H; inv H0...
      inv H0...
    SCase "a1 ==A> a1'".
      inv H...
Qed.

(* TODO: Do I need to prove any corollary as that in Smallstep.v?
May be used in proof of deterministic.
Corollary nf_same_as_value : forall t,
  normal_form step t <-> value t.
*)
(* ---------------- end of Boolean Expressions ---------------- *)


(* ---------------- Fence & Command ---------------- *)
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
(*
TODO: I don't know how to specify the thread ID of a cmd, so I
"hardcode" it like this.
*)
| CPar : tid -> cmd -> tid -> cmd -> cmd
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
  | Case_aux c "PAR" | Case_aux c "BAR"
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
Notation "'PAR' t1 '@' c1 'WITH' t2 '@' c2 'END'" :=
  (CPar t1 c1 t2 c2) (at level 80, right associativity).
Notation "'BAR' f" :=
  (CBar f) (at level 80).
Notation "'LOCK' l" :=
  (CLock l) (at level 80).
Notation "'UNLOCK' l" :=
  (CUnlock l) (at level 80).


(* Due to the definition of relation, normal_form is only for cstep. *)
Definition normal_form {X:Type} (R : relation X) (x : X) : Prop :=
  forall t, ~ exists x', R t x x'.


(* TODO: a Triple for (tid * cmd * state)?? *)

Reserved Notation "t1 '@' c1 '~' st1 '==>' t2 '@' c2 '~' st2" (at level 50).

Inductive cstep : tid -> (cmd * state) -> tid -> (cmd * state) -> Prop :=
| CS_Ass : forall t x n bs mem ls,
             t @ (x ::= (ANum n)) ~ (ST bs mem ls) ==> t @ SKIP ~ (ST (write bs t x n) mem ls)
| CS_AssStep : forall (t : tid) (x : var) (a a' : aexp) (st : state),
                 t @ a ~ st ==A> a' ->
                 t @ (x ::= a) ~ st ==> t @ (x ::= a') ~ st

| CS_Seq : forall t c2 st,
             t @ (SKIP ;; c2) ~ st ==> t @ c2 ~ st
| CS_SeqStep : forall t c1 c1' c2 st st',
                 t @ c1 ~ st ==> c1' ~ st' ->
                 t @ (c1 ;; c2) ~ st ==> (c1' ;; c2) ~ st'

| CS_IfTrue : forall t c1 c2 st,
                t @ (IFB (BBool true) THEN c1 ELSE c2 FI) ~ st ==> c1 ~ st
| CS_IfFalse : forall t c1 c2 st,
                 t @ (IFB (BBool false) THEN c1 ELSE c2 FI) ~ st ==> c2 ~ st
| CS_IfStep : forall t c1 c2 be be' st,
                t @ be ~ st ==B> be' ->
                t @ (IFB be THEN c1 ELSE c2 FI) ~ st ==> (IFB be' THEN c1 ELSE c2 FI) ~ st

| CS_While : forall t b c st,
               t @ (WHILE b DO c END) ~ st ==>
                 (IFB b THEN (c ;; (WHILE b DO c END)) ELSE SKIP FI) ~ st

| CS_BarGo : forall t bs mem ls,
               oldest bs t = None ->
               t @ (BAR MFENCE) ~ (ST bs mem ls) ==> SKIP ~ (ST bs mem ls)
| CS_BarFlush : forall t bs mem ls x n,
                  oldest bs t = Some (x, n) ->
                  t @ (BAR MFENCE) ~ (ST bs mem ls) ==>
                    (BAR MFENCE) ~ (ST (flush bs t) (update mem x n) ls)

| CS_Lock : forall t bs mem ls id,
              ls id = None ->
              t @ (CLock id) ~ (ST bs mem ls) ==> SKIP ~ (ST bs mem (lock ls t id))
| CS_Unlock : forall t bs mem ls id,
                ls id = Some t ->
                t @ (CUnlock id) ~ (ST bs mem ls) ==> SKIP ~ (ST bs mem (unlock ls id))

(* TODO: Finish the semantics for PAR
| CS_Par1 : forall t t1 t2 c1 c2 st,
              t @ (PAR t1 @ c1 WITH t2 @ c2 END) ~ st ==> SKIP ~ st
*)

where "t1 '@' c1 '~' st1 '==>' t2 '@' c2 '~' st2" := (cstep t1 (c1, st1) t2 (c2, st2)).


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




(* TODO Here is to define the term of "Threads", but I didn't find it
useful now.. My current version can only support 2 threads. This will
be useful when I extend to variable threads.

Definition threads := tid -> (buffer * cmd).

Definition empty_threads : threads :=
  fun _ => ([], SKIP).

Hint Unfold empty_threads.
*)



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

