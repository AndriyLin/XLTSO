(* TSO.v defines the Total Store Ordering semantics, i.e. with write buffers.

Table of Contents:
1. Uni-thread Semantics
2. Multi-threads Semantics
3. Proof of having TSO semantics
*)

Require Import XLib.
Require Import Basics.


(* ---------------- Uni-thread Semantics ---------------- *)

(* Note: evt is the event incurred by this step of evaluation *)
Reserved Notation "t '@' st1 '==>' st2 '[[' evt ']]'" (at level 80).

Inductive tsostep : tid -> state -> state -> event -> Prop :=
| TSO_Ass : forall t x n buf mem lks,
              t @ (ST (x ::= ANum n) buf mem lks) ==>
                  (ST SKIP (write buf x n) mem lks) [[EV_Write x n]]
| TSO_AssStep : forall t x a a' buf mem lks evt,
                  a /- buf ~ mem ==A> a' [[evt]] ->
                  t @ (ST (x ::= a) buf mem lks) ==> (ST (x ::= a') buf mem lks) [[evt]]

| TSO_Seq : forall t c2 buf mem lks,
              t @ (ST (SKIP ;; c2) buf mem lks) ==> (ST c2 buf mem lks) [[EV_None]]
| TSO_SeqStep : forall t c1 c1' c2 buf mem lks buf' mem' lks' evt,
                  t @ (ST c1 buf mem lks) ==> (ST c1' buf' mem' lks') [[evt]] ->
                  t @ (ST (c1 ;; c2) buf mem lks) ==> (ST (c1' ;; c2) buf' mem' lks') [[evt]]

| TSO_IfTrue : forall t c1 c2 buf mem lks,
                 t @ (ST (IFB (BBool true) THEN c1 ELSE c2 FI) buf mem lks) ==>
                     (ST c1 buf mem lks) [[EV_None]]
| TSO_IfFalse : forall t c1 c2 buf mem lks,
                  t @ (ST (IFB (BBool false) THEN c1 ELSE c2 FI) buf mem lks) ==>
                      (ST c2 buf mem lks) [[EV_None]]
| TSO_IfStep : forall t c1 c2 be be' buf mem lks evt,
                 be /- buf ~ mem ==B> be' [[evt]] ->
                 t @ (ST (IFB be THEN c1 ELSE c2 FI) buf mem lks) ==>
                     (ST (IFB be' THEN c1 ELSE c2 FI) buf mem lks) [[evt]]

| TSO_While : forall t b c buf mem lks,
                t @ (ST (WHILE b DO c END) buf mem lks) ==>
                    (ST (IFB b THEN (c ;; (WHILE b DO c END)) ELSE SKIP FI) buf mem lks)
                    [[EV_None]]

| TSO_FlushOne : forall t buf mem lks x n c,
                   (* Here it's defined as "it can flush no matter blocked or not" *)
                   oldest buf = Some (x, n) ->
                   t @ (ST c buf mem lks) ==> (ST c (flushone buf) (mem_update mem x n) lks)
                     [[EV_None]]

(* to LOCK/UNLOCK, buffer must be empty *)
| TSO_Lock : forall t mem lks lk,
               lks lk = None ->
               t @ (ST (LOCK lk) nil mem lks) ==>
                   (ST SKIP nil mem (lock lks t lk)) [[EV_Lock lk]]
| TSO_Unlock : forall t mem lks lk,
                 lks lk = Some t ->
                 t @ (ST (UNLOCK lk) nil mem lks) ==>
                     (ST SKIP nil mem (unlock lks lk)) [[EV_Unlock lk]]

where "t1 '@' st1 '==>' st2 '[[' evt ']]'" := (tsostep t1 st1 st2 evt).

Hint Constructors tsostep.

Tactic Notation "tsostep_cases" tactic(first) ident(c) :=
  first;
  [ Case_aux c "TSO_Ass" | Case_aux c "TSO_AssStep"
  | Case_aux c "TSO_Seq" | Case_aux c "TSO_SeqStep"
  | Case_aux c "TSO_IfTrue" | Case_aux c "TSO_IfFalse"
  | Case_aux c "TSO_IfStep" | Case_aux c "TSO_While"
  | Case_aux c "TSO_FlushOne"
  | Case_aux c "TSO_Lock" | Case_aux c "TSO_Unlock"
  ].


Theorem strong_progress_tso :
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
    apply TSO_FlushOne...
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
      apply TSO_FlushOne.
      simpl...
  Case "UNLOCK".
    destruct buf...
    SCase "empty buffer".
      destruct (lks l) eqn:Hl...
      destruct (eq_tid_dec t t0); subst...
    SCase "non-empty buffer".
      right; destruct p.
      eexists; eexists.
      apply TSO_FlushOne...
      simpl...
Qed.

Hint Resolve strong_progress_tso.


(* ststep is no longer deterministic, one state may execute one
command, it may also flush one unit of its write buffer to memory *)
Theorem tsostep_not_deterministic:
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
    apply TSO_FlushOne.
    simpl...
  assert (st1 = st2).
    eapply Hf.
    apply H.
    apply H0.
  subst.
  clear H H0.
  inv H1.
Qed.
(* ---------------- end of 1. Uni-thread Semantics ---------------- *)


(* ---------------- 2. Multi-threads Semantics ---------------- *)

Reserved Notation "cfg1 '-->' cfg2 '[[' tevt ']]'" (at level 60).

Inductive cfgtso : configuration -> configuration -> (tid * event) -> Prop :=
(* One thread can move one step forward, in terms of "state" *)
| CFGTSO : forall t tids thds bufs c c' b b' mem mem' lks lks' evt,
             in_tids t tids = true ->
             thds t = c ->
             bufs t = b ->
             t @ (ST c b mem lks) ==> (ST c' b' mem' lks') [[evt]] ->
             (CFG tids thds bufs mem lks) -->
               (CFG tids (thds_update thds t c') (bufs_update bufs t b') mem' lks')
               [[(t, evt)]]

where "cfg1 '-->' cfg2 '[[' tevt ']]'" := (cfgtso cfg1 cfg2 tevt).

Hint Constructors cfgtso.


Theorem strong_progress_cfgtso :
  forall tids thds bufs mem lks,
    cfg_normal_form (CFG tids thds bufs mem lks) \/
    exists cfg' t evt, (CFG tids thds bufs mem lks) --> cfg' [[(t, evt)]].
Proof with eauto.
  intros tids.
  induction tids as [ | hd tl];
    intros.
  Case "tids = nil".
    left; constructor.
    intros.
    invf H.
  Case "tids = hd :: tl".
    destruct (IHtl thds bufs mem lks); clear IHtl.
    SCase "all other threads are in normal_form".
      inv H.
      assert (st_normal_form hd (ST (thds hd) (bufs hd) mem lks) \/
              (exists st' evt, hd @ (ST (thds hd) (bufs hd) mem lks) ==> st' [[evt]])) by eauto.
      inv H.
      SSCase "thread hd is in normal_form".
        left; constructor; intros.
        destruct (eq_tid_dec t hd); subst.
        auto.
        simpl in H; rewrite -> neq_tid in H...
      SSCase "thread hd is not in normal_form".
        inv H0; inv H.
        rename x0 into evt; destruct x.
        right.
        eexists; exists hd; exists evt.
        apply CFGTSO with (thds hd) (bufs hd).
        simpl... auto. auto.
        apply H0.
    SCase "some other thread is not in normal_form".
      inv H; inv H0; inv H; inv H0.
      rename x0 into t; rename x1 into evt.
      right; eexists; exists t; exists evt.
      apply CFGTSO with (thds t) (bufs t).
      simpl; destruct (eq_tid_dec t hd)... auto. auto.
      apply H11.
Qed.

(* For deterministic, multi-threaded semantics is definitely not deterministic *)


Definition multicfgtso := multi cfgtso.

Notation "cfg1 '-->*' cfg2 '[[' tevts ']]'" := (multicfgtso cfg1 cfg2 tevts) (at level 40).

(* ---------------- end of 2. Multi-threads Semantics ---------------- *)


(* ---------------- 3. Proof of having TSO Semantics ---------------- *)
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
  exists tids thds bufs mem lks trc,
    init_cfg codes -->* (CFG tids thds bufs mem lks) [[trc]] /\
    mem EAX = 1 /\ mem EBX = 0 /\ mem X = 1.
Proof with eauto.
  eexists.
  eexists.
  eexists.
  eexists.
  eexists.
  eexists.
  split.

  (* proc1: write of Y := 2 is buffered *)
  eapply multi_step.
  apply CFGTSO with (t := T1) (c := proc1) (b := nil)...
  unfold proc1...
  eapply multi_step.
  apply CFGTSO with (t := T1) (c := (SKIP;; X ::= (ANum 2))) (b := [(Y, 2)])...

  (* proc0: write of X := 1 is buffered *)
  eapply multi_step.
  apply CFGTSO with (t := T0) (c := proc0) (b := nil)...
  unfold proc0...
  eapply multi_step.
  apply CFGTSO with (t := T0) (c := (SKIP;; EAX ::= (AVar X) ;; (EBX ::= (AVar Y)))) (b := [(X, 1)])...

  (* proc0: read EAX := X from write buffer *)
  eapply multi_step.
  apply CFGTSO with (t := T0) (c := (EAX ::= (AVar X) ;; (EBX ::= (AVar Y)))) (b := [(X, 1)])...
  constructor.
  constructor.
  constructor.
  reflexivity.
  eapply multi_step.
  apply CFGTSO with (t := T0) (c := (EAX ::= (ANum 1);; (EBX ::= (AVar Y)))) (b := [(X, 1)])...
  eapply multi_step.
  apply CFGTSO with (t := T0) (c := (SKIP;; (EBX ::= (AVar Y)))) (b := [(X, 1); (EAX, 1)])...

  (* proc0: read EBX := Y from memory *)
  eapply multi_step.
  apply CFGTSO with (t := T0) (c := (EBX ::= (AVar Y))) (b := [(X, 1); (EAX, 1)])...
  eapply multi_step.
  apply CFGTSO with (t := T0) (c := (EBX ::= (ANum 0))) (b := [(X, 1); (EAX, 1)])...
  (* after this, proc0: c := SKIP, b := (X, 1) :: (EAX, 1) :: (EBX, 0) :: nil *)

  (* proc1: write of X := 2 buffered *)
  eapply multi_step.
  apply CFGTSO with (t := T1) (c := (X ::= (ANum 2))) (b := [(Y, 2)])...
  (* after this, proc1: c := SKIP, b := (Y, 2) :: (X, 2) :: nil *)

  (* proc1: flushes write Y := 2 to memory *)
  eapply multi_step.
  apply CFGTSO with (t := T1) (c := SKIP) (b := [(Y, 2); (X, 2)])...
  constructor.
  simpl...

  (* proc1: flushes write X := 2 to memory *)
  eapply multi_step.
  apply CFGTSO with (t := T1) (c := SKIP) (b := [(X, 2)])...
  constructor.
  simpl...

  (* proc1: done *)

  (* proc0: flushes write X := 1 to memory *)
  eapply multi_step.
  apply CFGTSO with (t := T0) (c := SKIP) (b := [(X, 1); (EAX, 1); (EBX, 0)])...
  constructor.
  simpl...

  (* proc0: flushes all else in the write buffer to memory *)
  eapply multi_step.
  apply CFGTSO with (t := T0) (c := SKIP) (b := [(EAX, 1); (EBX, 0)])...
  constructor.
  simpl...
  eapply multi_step.
  apply CFGTSO with (t := T0) (c := SKIP) (b := [(EBX, 0)])...
  constructor.
  simpl...

  (* proc0: done *)

  (* DONE, now the final state is: EAX = 1 /\ EBX = 0 /\ X = 1 *)
  apply multi_refl.
  simpl in *.
  auto.
Qed.

End TsoSemanticsProof.
(* ---------------- end of 3. Proof of having TSO Semantics ---------------- *)

