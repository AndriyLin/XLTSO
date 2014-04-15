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
Updated: 04/09/2014


Structure:
1. Variable
2. Main memory
3. Arithmatic / Boolean Expressions & Commands
4. Thread ID
5. LockID and Locks
6. Write Buffers & Threads
7. State
8. Evaluation & Semantics
9. TODO..
*)

Require Export XLib.


(* ---------------- 1. Var ---------------- *)
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


(* ---------------- 2. Main Memory ---------------- *)
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
(* ---------------- end of 2. Main Memory ---------------- *)


(* ---------------- 3. A/B Expressions & Command ---------------- *)
Inductive aexp : Type :=
| ANum : nat -> aexp
| APlus : aexp -> aexp -> aexp
| AMinus : aexp -> aexp -> aexp
| AMult : aexp -> aexp -> aexp
| AVar : var -> aexp.

Hint Constructors aexp.

Tactic Notation "aexp_cases" tactic(first) ident(c) :=
  first;
  [ Case_aux c "ANum" | Case_aux c "APlus"
  | Case_aux c "AMinus" | Case_aux c "AMult"
  | Case_aux c "AVar" ].


Inductive bexp : Type :=
| BTrue : bexp
| BFalse : bexp
| BNot : bexp -> bexp
| BAnd : bexp -> bexp -> bexp
| BOr : bexp -> bexp -> bexp
| BEq : aexp -> aexp -> bexp
| BLe : aexp -> aexp -> bexp.

Hint Constructors bexp.

Tactic Notation "bexp_cases" tactic(first) ident(c) :=
  first;
  [ Case_aux c "BTrue" | Case_aux c "BFalse" | Case_aux c "BNot"
  | Case_aux c "BAnd" | Case_aux c "BOr" | Case_aux c "BEq"
  | Case_aux c "BLe" ].


Inductive cmd : Type :=
| CSkip : cmd
| CAss : var -> aexp -> cmd
| CSeq : cmd -> cmd -> cmd
| CIf : bexp -> cmd -> cmd -> cmd
| CWhile : bexp -> cmd -> cmd.

Hint Constructors cmd.

Tactic Notation "cmd_cases" tactic(first) ident(c) :=
  first;
  [ Case_aux c "SKIP" | Case_aux c "::=" | Case_aux c ";;"
  | Case_aux c "IFB" | Case_aux c "WHILE" ].

Notation "'SKIP'" :=
  CSkip.
Notation "x '::=' a" :=
  (CAss x a) (at level 60).
Notation "c1 ;; c2" :=
  (CSeq c1 c2) (at level 80, right associativity).
Notation "'WHILE' b 'DO' c 'END'" :=
  (CWhile b c) (at level 80, right associativity).
Notation "'IFB' b 'THEN' c1 'ELSE' c2 'FI'" :=
  (CIf b c1 c2) (at level 80, right associativity).
(* ---------------- end of 3. A/B Expressions & Command ---------------- *)


(* ---------------- 4. Thread ID ---------------- *)
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
(* ---------------- end of 4. Thread ID ---------------- *)


(* ---------------- 5. Lock ---------------- *)
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

Hint Unfold empty_locks.

(* Checking of validity is left to semantics, not done here *)
Definition lock (st : lock_status) (t : tid) (l : lid) : lock_status :=
  fun l' => if eq_lid_dec l l' then Some t else st l'.

Hint Unfold lock.

(* Again, checking of validity is not done here, it's left to semantics *)
Definition unlock (st : lock_status) (t : tid) (l : lid) : lock_status :=
  fun l' => if eq_lid_dec l l' then None else st l'.

Hint Unfold unlock.
(* ---------------- end of 5. Lock ---------------- *)


(* ---------------- 6. Write Buffer & Threads ---------------- *)
(* In the buffer: [old ... new], new writes are appended to the right *)
Definition buffer : Type := list (var * nat).

(* Add a new write to the end of buffer *)
Fixpoint write (b : buffer) (x : var) (n : nat) : buffer :=
  match b with
    | nil => [(x, n)]
    | hd :: tl => hd :: write tl x n
  end.

(* get the oldest write in the buffer *)
Definition lastone (b : buffer) : option (var * nat) :=
  hd b.

(* remove the oldest write in the buffer *)
Fixpoint flush (b : buffer) : buffer :=
  tl b.

(* the helper function for get *)
Fixpoint _get (b : buffer) (x : var) (result : option nat) : option nat :=
  match b with
    | nil => result
    | (k, v) :: tl => if eq_var_dec x k
                      then _get tl x (Some v)
                      else _get tl x result
  end.

(* get the latest value of some variable in the buffer, if any *)
Fixpoint get (b : buffer) (x : var) : option nat :=
  _get b x None.


Definition threads := tid -> (buffer * cmd).

Definition empty_threads : threads :=
  fun _ => ([], SKIP).

Hint Unfold empty_threads.
(* ---------------- end of 6. Write Buffer & Threads ---------------- *)


(* ---------------- 7. State ---------------- *)
(* state consists of 3 parts: threads (i.e. buffer + cmd) * locks * memory *)
Record state := ST {
  st_ts : threads;
  st_ls : lock_status;
  st_mem : memory
}.

Definition empty_state := ST empty_threads empty_locks empty_memory.
(* ---------------- end of 7. State ---------------- *)


(* ---------------- 8. Evaluation & Semantics ---------------- *)
(* Only memory & buffer information is needed *)
Fixpoint aeval (mem : memory) (buf : buffer) (a : aexp) : nat :=
  match a with
    | ANum n => n
    | APlus a1 a2 => (aeval mem buf a1) + (aeval mem buf a2)
    | AMinus a1 a2 => (aeval mem buf a1) - (aeval mem buf a2)
    | AMult a1 a2 => (aeval mem buf a1) * (aeval mem buf a2)
    | AVar x => match get buf x with
                  | None => mem x
                  | Some n => n
                end
  end.

(* Only memory & buffer information is needed *)
Fixpoint beval (mem : memory) (buf : buffer) (b : bexp) : bool :=
  match b with
    | BTrue => true
    | BFalse => false
    | BNot b' => negb (beval mem buf b')
    | BAnd b1 b2 => andb (beval mem buf b1) (beval mem buf b2)
    | BOr b1 b2 => orb (beval mem buf b1) (beval mem buf b2)
    | BEq a1 a2 => beq_nat (aeval mem buf a1) (aeval mem buf a2)
    | BLe a1 a2 => ble_nat (aeval mem buf a1) (aeval mem buf a2)
  end.


(* TODO Resume here *)
Reserved Notation "c1 '/' st '||' st'" (at level 40, st at level 39).

Inductive ceval : cmd -> state -> state -> Prop :=
  | CE_Skip : forall st,
                SKIP / st || st
  | CE_Ass  : forall st a1 n x,
                aeval st a1 = n ->
                (x ::= a1) / st || (update st x n)
  | CE_Seq : forall c1 c2 st st' st'',
               c1 / st  || st' ->
               c2 / st' || st'' ->
               (c1 ;; c2) / st || st''
  | CE_IfTrue : forall st st' b c1 (c2 : cmd),
                  beval st b = true ->
                  c1 / st || st' ->
                  (IFB b THEN c1 ELSE c2 FI) / st || st'
  | CE_IfFalse : forall st st' b c1 c2,
                   beval st b = false ->
                   c2 / st || st' ->
                   (IFB b THEN c1 ELSE c2 FI) / st || st'
  | CE_WhileEnd : forall b st c,
                    beval st b = false ->
                    (WHILE b DO c END) / st || st
  | CE_WhileLoop : forall st st' st'' b c,
                     beval st b = true ->
                     c / st || st' ->
                     (WHILE b DO c END) / st' || st'' ->
                     (WHILE b DO c END) / st || st''

where "c1 '/' st '||' st'" := (ceval c1 st st').

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
(* ---------------- end of 8. Evaluation & Semantics ---------------- *)


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
*)

