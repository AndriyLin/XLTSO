(* SC.v defines the Sequential Consistency semantics, i.e. no write buffers.

Table of Contents:
1. Uni-thread Semantics
2. Multi-threads Semantics
*)

Require Import XLib.
Require Import Basics.


(* ---------------- Uni-thread Semantics ---------------- *)
(* Note: The following is the sequential semantics (without write
buffers).  Buffer is still declared in state for consistency with TSO,
but is as always nil in semantics. *)
Reserved Notation "t '@' st1 '==SC>' st2 '[[' evt ']]'" (at level 80).

Inductive scstep : tid -> state -> state -> event -> Prop :=
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
| SC_Unlock : forall t mem lks lk,
                lks lk = Some t ->
                t @ (ST (UNLOCK lk) nil mem lks) ==SC>
                  (ST SKIP nil mem (unlock lks lk)) [[EV_Unlock lk]]

where "t1 '@' st1 '==SC>' st2 '[[' evt ']]'" := (scstep t1 st1 st2 evt).

Hint Constructors scstep.

Tactic Notation "scstep_cases" tactic(first) ident(c) :=
  first;
  [ Case_aux c "SC_Ass" | Case_aux c "SC_AssStep"
  | Case_aux c "SC_Seq" | Case_aux c "SC_SeqStep"
  | Case_aux c "SC_IfTrue" | Case_aux c "SC_IfFalse"
  | Case_aux c "SC_IfStep" | Case_aux c "SC_While"
  | Case_aux c "SC_Lock" | Case_aux c "SC_Unlock"
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
    destruct (lks l) eqn:Hl...
    destruct (eq_tid_dec t t0); subst...
Qed.

Hint Resolve strong_progress_sc.


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
  scstep_cases (induction H) Case;
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
    apply IHscstep in H8.
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
  Case "SC_Unlock".
    inv H2...
Qed.

(* ---------------- end of 1. Uni-thread Semantics ---------------- *)


(* ---------------- 2. Multi-threads Semantics ---------------- *)

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

(* ---------------- end of 2. Multi-threads Semantics ---------------- *)

