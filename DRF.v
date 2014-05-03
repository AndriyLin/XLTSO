(* DRF.v defines lemmas and theorems for the DRF Guarantee Theorem

Table of Contents:
* Data-Race-Free
* Diamond Lemma
* DRF -> Well-Synchronized
* DRF Guarantee Property

* TODO.. to be numbered
*)

Require Import XLib.
Require Import Basics.
Require Import TSO.
Require Import SC.


(* ---------------- Data-Race-Free ---------------- *)
(* The command determines whether "writes c x" is provable, so just
assign the most basic context. *)
Inductive writes : cmd -> var -> Prop :=
| Writes : forall t c mem lks st' x n,
             t @ (ST c nil mem lks) ==SC> st' [[EV_Write x n]] ->
             writes c x
.

Hint Constructors writes.

(* The command determines whether "reads c x" is provable, so just
assign the most basic context. *)
Inductive reads : cmd -> var -> Prop :=
| Reads : forall t c mem lks st' x,
            t @ (ST c nil mem lks) ==SC> st' [[EV_Read x]] ->
            reads c x
.

Hint Constructors reads.

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

(* Whether 2 consecutive events of different tids in a trace can be
simply swapped. The rules are copied from paper "Relaxed Memory
Models: an Operational Approach" (Definition 3.4). LOCK & UNLOCK are
considered to be "write" operations. *)
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

Hint Resolve bstep_event_read_or_none.

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
  scstep_cases (induction H) Case;
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
  scstep_cases (induction H) Case;
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
  scstep_cases (induction H) Case;
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
  scstep_cases (induction H) Case;
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
  scstep_cases (induction H) Case;
    intros; inversion Heqevt; subst;
    inv Heqst1; inv Heqst2...
Qed.

(* end of all lemmas for:
     What it means for a smallstep to generate a EV_XX event?
*)

(* ---------------------------------------------------------------- *)
(* The following several lemmas are for the Diamond Theorem:

    If a smallstep generates an event EV_XXX, then it will also
    generate this event in a slightly different context.
*)

Lemma astep_read_context_invariance_more :
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

Hint Resolve astep_read_context_invariance_more.

Lemma astep_read_context_invariance_less :
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

Hint Resolve astep_read_context_invariance_less.

Lemma bstep_read_context_invariance_more :
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

Hint Resolve bstep_read_context_invariance_more.

Lemma bstep_read_context_invariance_less :
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

Hint Resolve bstep_read_context_invariance_less.


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
  scstep_cases (induction H0) Case;
    intros; inversion Heqevt; inv Heqst1; inv Heqst2.
  Case "SC_AssStep".
    constructor.
    apply astep_read_context_invariance_more...
  Case "SC_SeqStep".
    constructor.
    apply IHscstep with x1...
  Case "SC_IfStep".
    constructor.
    apply bstep_read_context_invariance_more...
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
  scstep_cases (induction H0) Case;
    intros; inversion Heqevt; inv Heqst1; inv Heqst2.
  Case "SC_AssStep".
    constructor.
    eapply astep_read_context_invariance_less...
  Case "SC_SeqStep".
    constructor.
    eapply IHscstep...
  Case "SC_IfStep".
    constructor.
    eapply bstep_read_context_invariance_less...
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
  scstep_cases (induction H) Case;
    intros; inversion Heqevt; inv Heqst1; inv Heqst2.
  Case "SC_AssStep".
    constructor...
  Case "SC_SeqStep".
    constructor...
  Case "SC_IfStep".
    constructor...
Qed.

(* If added this, it would somehow cause problems..
Hint Resolve read_context_invariance_lks.
*)


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
  scstep_cases (induction H) Case;
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
  scstep_cases (induction H) Case;
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
  scstep_cases (induction H0) Case;
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
  scstep_cases (induction H0) Case;
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
  intros.
  remember (ST c [] mem lks) as st1.
  remember (ST c' [] mem (unlock lks l)) as st2.
  remember (EV_Unlock l) as evt.
  generalize dependent l; generalize dependent lks;
  generalize dependent mem'; generalize dependent mem;
  generalize dependent c'; generalize dependent c.
  scstep_cases (induction H) Case;
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

Lemma unlock_context_invariance_lks_less :
  forall t c c' mem lks l1 l2 v2,
    l1 <> l2 ->
    t @ (ST c [] mem (lks_update lks l2 v2)) ==SC>
        (ST c' [] mem (unlock (lks_update lks l2 v2) l1)) [[EV_Unlock l1]] ->
    t @ (ST c [] mem lks) ==SC> (ST c' [] mem (unlock lks l1)) [[EV_Unlock l1]].
Proof with eauto.
  intros.
  remember (ST c [] mem (lks_update lks l2 v2)) as st1.
  remember (ST c' [] mem (unlock (lks_update lks l2 v2) l1)) as st2.
  remember (EV_Unlock l1) as evt.
  generalize dependent c'; generalize dependent c;
  generalize dependent mem; generalize dependent lks;
  generalize dependent l1; generalize dependent l2;
  generalize dependent v2.
  scstep_cases (induction H0) Case;
    intros; inversion Heqevt; inv Heqst1; inv Heqst2...
  Case "SC_AssStep".
    apply astep_event_read_or_none in H.
    inv H.
    inv H2; invf H.
  Case "SC_IfStep".
    apply bstep_event_read_or_none in H.
    inv H.
    inv H2; invf H.
  Case "SC_Unlock".
    rewrite -> lks_update_neq in H...
Qed.

Lemma unlock_context_invariance_lks_more :
  forall t c c' mem lks l1 l2 v2,
    l1 <> l2 ->
    t @ (ST c [] mem lks) ==SC> (ST c' [] mem (unlock lks l1)) [[EV_Unlock l1]] ->
    t @ (ST c [] mem (lks_update lks l2 v2)) ==SC>
         (ST c' [] mem (unlock (lks_update lks l2 v2) l1)) [[EV_Unlock l1]].
Proof with eauto.
  intros.
  remember (ST c [] mem lks) as st1.
  remember (ST c' [] mem (unlock lks l1)) as st2.
  remember (EV_Unlock l1) as evt.
  generalize dependent c'; generalize dependent c;
  generalize dependent mem; generalize dependent lks;
  generalize dependent l1; generalize dependent l2;
  generalize dependent v2.
  scstep_cases (induction H0) Case;
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
  Case "SC_Unlock".
    subst...
    constructor.
    rewrite -> lks_update_neq...
Qed.


Lemma astep_none_context_invariance :
  forall a a' buf mem mem',
    a /- buf ~ mem ==A> a' [[EV_None]] ->
    a /- buf ~ mem' ==A> a' [[EV_None]].
Proof with eauto.
  intros.
  remember EV_None as evt.
  generalize dependent mem'.
  astep_cases (induction H) Case;
    intros; inversion Heqevt; subst; eauto.
Qed.

Hint Resolve astep_none_context_invariance.

Lemma bstep_none_context_invariance :
  forall b b' buf mem mem',
    b /- buf ~ mem ==B> b' [[EV_None]] ->
    b /- buf ~ mem' ==B> b' [[EV_None]].
Proof with eauto.
  intros.
  remember EV_None as evt.
  generalize dependent mem'.
  bstep_cases (induction H) Case;
    intros; inversion Heqevt; subst; eauto.
Qed.

Hint Resolve bstep_none_context_invariance.

Lemma none_context_invariance :
  forall t c c' mem mem' lks lks',
    t @ (ST c [] mem lks) ==SC> (ST c' [] mem lks) [[EV_None]] ->
    t @ (ST c [] mem' lks') ==SC> (ST c' [] mem' lks') [[EV_None]].
Proof with eauto.
  intros.
  remember (ST c [] mem lks) as st1.
  remember (ST c' [] mem lks) as st2.
  remember EV_None as evt.
  generalize dependent c; generalize dependent c';
  generalize dependent mem; generalize dependent mem';
  generalize dependent lks; generalize dependent lks'.
  scstep_cases (induction H) Case;
    intros; inversion Heqevt; inv Heqst1; inv Heqst2...
Qed.

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
  intros cfg0 cfg1 cfg2 t1 t2 evt1 evt2 Ht H01 H12 Hcfl.
  inversion H01; subst.
  inversion H12; subst.
(*
I choose to do case analysis on events, each event can be Read, Write,
Lock, Unlock, or None. So there are 25 cases.. >_<

Generating a Rd event means: mem' = mem /\ lks' = lks
Generating a Wr event means: mem' = update mem x n /\ lks' = lks
Generating a Lk event means: mem' = mem /\ lks' = lock lks t lk
Generating a Un event means: mem' = mem /\ lks' = unlock lks lk
Generating a None event means: mem' = mem /\ lks' = lks

Then by a bunch of lemmas stated above this theorem, the proof in each
case is not hard. It's just time-consuming!
*)
  event_cases (induction evt1) Case.
  Case "EV_Read". (* evt1 : Read *)
    assert (mem = mem' /\ lks = lks').
      eapply sc_event_read; apply H6.
    inv H.
    event_cases (induction evt2) SCase;
    (* make it first update t2, then update t1 *)
      rewrite -> thds_update_permute.

    SCase "EV_Read". (* evt1 : Read / evt2 : Read *)
      assert (mem' = mem'0 /\ lks' = lks'0).
        eapply sc_event_read; apply H14.
      inv H.
      exists (CFG tids (thds_update thds t2 c'0) bufs mem'0 lks'0); split.
      rewrite -> thds_update_neq in H14...
      apply CFGSC with (thds t1)... auto.

    SCase "EV_Write". (* evt1 : Read / evt2 : Write *)
      destruct (eq_var_dec x x0); subst.
      assert (conflict (EV_Read x0) (EV_Write x0 n)) by auto.
      apply Hcfl in H; invf H. (* x = x0, evt1 & evt2 conflict *)

      assert (mem'0 = mem_update mem' x0 n /\ lks' = lks'0).
        eapply sc_event_write; apply H14.
      inv H.
      exists (CFG tids (thds_update thds t2 c'0) bufs (mem_update mem' x0 n) lks'0); split.
      rewrite -> thds_update_neq in H14...
      apply CFGSC with (thds t1)... auto.

    SCase "EV_Lock". (* evt1 : Read / evt2 : Lock *)
      assert (mem' = mem'0 /\ lks'0 = lock lks' t2 l).
        eapply sc_event_lock; apply H14.
      inv H.
      exists (CFG tids (thds_update thds t2 c'0) bufs mem'0 (lock lks' t2 l)); split.
      rewrite -> thds_update_neq in H14...
      apply CFGSC with (thds t1)...
      eapply read_context_invariance_lks... auto.

    SCase "EV_Unlock". (* evt1 : Read / evt2 : Unlock *)
      assert (mem' = mem'0 /\ lks'0 = unlock lks' l).
        eapply sc_event_unlock; apply H14.
      inv H.
      exists (CFG tids (thds_update thds t2 c'0) bufs mem'0 (unlock lks' l)); split.
      rewrite -> thds_update_neq in H14...
      apply CFGSC with (thds t1)...
      eapply read_context_invariance_lks... auto.

    SCase "EV_None". (* evt1 : Read / evt2 : None *)
      assert (mem' = mem'0 /\ lks' = lks'0).
        eapply sc_event_none; apply H14.
      inv H.
      exists (CFG tids (thds_update thds t2 c'0) bufs mem'0 lks'0); split.
      rewrite -> thds_update_neq in H14...
      apply CFGSC with (thds t1)... auto.

  Case "EV_Write". (* evt1 : Write *)
    assert (mem' = mem_update mem x n /\ lks = lks').
      eapply sc_event_write; apply H6.
    inv H.
    event_cases (induction evt2) SCase;
      (* make it first update t2, then update t1 *)
      rewrite -> thds_update_permute.

    SCase "EV_Read". (* evt1 : Write / evt2 : Read *)
      destruct (eq_var_dec x x0); subst.
      assert (conflict (EV_Write x0 n) (EV_Read x0)) by auto.
      apply Hcfl in H; invf H. (* x = x0, evt1 & evt2 conflict *)

      assert (mem_update mem x n = mem'0 /\ lks' = lks'0).
        eapply sc_event_read; apply H14.
      inv H.
      exists (CFG tids (thds_update thds t2 c'0) bufs mem lks'0); split.
      rewrite -> thds_update_neq in H14.
      apply CFGSC with (thds t2)... auto.
      apply CFGSC with (thds t1)... auto.

    SCase "EV_Write". (* evt1 : Write / evt2 : Write *)
      destruct (eq_var_dec x x0); subst.
      assert (conflict (EV_Write x0 n) (EV_Write x0 n0)) by auto.
      apply Hcfl in H; invf H. (* x = x0, evt1 & evt2 conflict *)

      assert (mem'0 = mem_update (mem_update mem x n) x0 n0 /\ lks' = lks'0).
        eapply sc_event_write; apply H14.
      inv H.
      rewrite -> mem_update_permute.
      exists (CFG tids (thds_update thds t2 c'0) bufs (mem_update mem x0 n0) lks'0); split.
      rewrite -> thds_update_neq in H14.
      apply CFGSC with (thds t2)...
      eapply write_context_invariance; apply H14. auto.
      apply CFGSC with (thds t1)...
      eapply write_context_invariance; apply H6. auto. auto.

    SCase "EV_Lock". (* evt1 : Write / evt2 : Lock *)
      assert (mem_update mem x n = mem'0 /\ lks'0 = lock lks' t2 l).
        eapply sc_event_lock; apply H14.
      inv H.
      exists (CFG tids (thds_update thds t2 c'0) bufs mem (lock lks' t2 l)); split.
      rewrite -> thds_update_neq in H14.
      apply CFGSC with (thds t2)...
      eapply lock_context_invariance_mem; apply H14. auto.
      apply CFGSC with (thds t1)...
      eapply write_context_invariance; apply H6. auto.

    SCase "EV_Unlock". (* evt1 : Write / evt2 : Unlock *)
      assert (mem_update mem x n = mem'0 /\ lks'0 = unlock lks' l).
        eapply sc_event_unlock; apply H14.
      inv H.
      exists (CFG tids (thds_update thds t2 c'0) bufs mem (unlock lks' l)); split.
      rewrite -> thds_update_neq in H14.
      apply CFGSC with (thds t2)...
      eapply unlock_context_invariance_mem; apply H14. auto.
      apply CFGSC with (thds t1)...
      eapply write_context_invariance; apply H6. auto.

    SCase "EV_None". (* evt1 : Write / evt2 : None *)
      assert (mem_update mem x n = mem'0 /\ lks' = lks'0).
        eapply sc_event_none; apply H14.
      inv H.
      exists (CFG tids (thds_update thds t2 c'0) bufs mem lks'0); split.
      rewrite -> thds_update_neq in H14.
      apply CFGSC with (thds t2)...
      eapply none_context_invariance; apply H14. auto.
      apply CFGSC with (thds t1)... auto.

  Case "EV_Lock". (* evt1 : Lock *)
    assert (mem = mem' /\ lks' = lock lks t1 l).
      eapply sc_event_lock; apply H6.
    inv H.
    event_cases (induction evt2) SCase;
      (* make it first update t2, then update t1 *)
      rewrite -> thds_update_permute.

    SCase "EV_Read". (* evt1 : Lock / evt2 : Read *)
      assert (mem' = mem'0 /\ lock lks t1 l = lks'0).
        eapply sc_event_read; apply H14.
      inv H.
      rewrite -> thds_update_neq in H14...
      exists (CFG tids (thds_update thds t2 c'0) bufs mem'0 lks); split.
      apply CFGSC with (thds t2)...
      eapply read_context_invariance_lks...
      apply CFGSC with (thds t1)... auto.

    SCase "EV_Write". (* evt1 : Lock / evt2 : Write *)
      assert (mem'0 = mem_update mem' x n /\ lock lks t1 l = lks'0).
        eapply sc_event_write; apply H14.
      inv H.
      rewrite -> thds_update_neq in H14...
      exists (CFG tids (thds_update thds t2 c'0) bufs (mem_update mem' x n) lks); split.
      apply CFGSC with (thds t2)...
      eapply write_context_invariance; apply H14.
      apply CFGSC with (thds t1)...
      eapply lock_context_invariance_mem; apply H6. auto.

    SCase "EV_Lock". (* evt1 : Lock / evt2 : Lock *)
      destruct (eq_lid_dec l l0); subst.
      assert (conflict (EV_Lock l0) (EV_Lock l0)) by auto.
      apply Hcfl in H; invf H. (* l = l0, evt1 & evt2 conflict *)

      assert (mem' = mem'0 /\ lks'0 = lock (lock lks t1 l) t2 l0).
        eapply sc_event_lock; apply H14.
      inv H.
      unfold lock; rewrite -> lks_update_permute.
      exists (CFG tids (thds_update thds t2 c'0) bufs mem'0 (lks_update lks l0 (Some t2))); split.
      apply CFGSC with (thds t2)...
      rewrite -> thds_update_neq in H14...
      eapply lock_context_invariance_lks_less...
      apply CFGSC with (thds t1)...
      eapply lock_context_invariance_lks_more... auto. auto.

    SCase "EV_Unlock". (* evt1 : Lock / evt2 : Unlock *)
      destruct (eq_lid_dec l l0); subst.
      assert (conflict (EV_Lock l0) (EV_Unlock l0)) by auto.
      apply Hcfl in H; invf H. (* l = l0, evt1 & evt2 conflict *)

      assert (mem' = mem'0 /\ lks'0 = unlock (lock lks t1 l) l0).
        eapply sc_event_unlock; apply H14.
      inv H.
      unfold unlock, lock; rewrite -> lks_update_permute.
      exists (CFG tids (thds_update thds t2 c'0) bufs mem'0 (lks_update lks l0 None)); split.
      apply CFGSC with (thds t2)...
      rewrite -> thds_update_neq in H14...
      eapply unlock_context_invariance_lks_less...
      apply CFGSC with (thds t1)...
      eapply lock_context_invariance_lks_more... auto. auto.

    SCase "EV_None". (* evt1 : Lock / evt2 : None *)
      assert (mem' = mem'0 /\ lock lks t1 l = lks'0).
        eapply sc_event_none; apply H14.
      inv H.
      rewrite -> thds_update_neq in H14...
      exists (CFG tids (thds_update thds t2 c'0) bufs mem'0 lks); split.
      apply CFGSC with (thds t2)...
      eapply none_context_invariance...
      apply CFGSC with (thds t1)... auto.

  Case "EV_Unlock". (* evt1 : Unlock *)
    assert (mem = mem' /\ lks' = unlock lks l).
      eapply sc_event_unlock; apply H6.
    inv H.
    event_cases (induction evt2) SCase;
      (* make it first update t2, then update t1 *)
      rewrite -> thds_update_permute.

    SCase "EV_Read". (* evt1 : Unlock / evt2 : Read *)
      assert (mem' = mem'0 /\ unlock lks l = lks'0).
        eapply sc_event_read; apply H14.
      inv H.
      rewrite -> thds_update_neq in H14...
      exists (CFG tids (thds_update thds t2 c'0) bufs mem'0 lks); split.
      apply CFGSC with (thds t2)...
      eapply read_context_invariance_lks...
      apply CFGSC with (thds t1)... auto.

    SCase "EV_Write". (* evt1 : Unlock / evt2 : Write *)
      assert (mem'0 = mem_update mem' x n /\ unlock lks l = lks'0).
        eapply sc_event_write; apply H14.
      inv H.
      rewrite -> thds_update_neq in H14...
      exists (CFG tids (thds_update thds t2 c'0) bufs (mem_update mem' x n) lks); split.
      apply CFGSC with (thds t2)...
      eapply write_context_invariance...
      apply CFGSC with (thds t1)...
      eapply unlock_context_invariance_mem... auto.

    SCase "EV_Lock". (* evt1 : Unlock / evt2 : Lock *)
      destruct (eq_lid_dec l l0); subst.
      assert (conflict (EV_Unlock l0) (EV_Lock l0)) by auto.
      apply Hcfl in H; invf H. (* l = l0, evt1 & evt2 conflict *)

      assert (mem' = mem'0 /\ lks'0 = lock (unlock lks l) t2 l0).
        eapply sc_event_lock; apply H14.
      inv H.
      unfold lock, unlock; rewrite -> lks_update_permute.
      rewrite -> thds_update_neq in H14...
      exists (CFG tids (thds_update thds t2 c'0) bufs mem'0 (lks_update lks l0 (Some t2))); split.
      apply CFGSC with (thds t2)...
      eapply lock_context_invariance_lks_less...
      apply CFGSC with (thds t1)...
      eapply unlock_context_invariance_lks_more... auto. auto.

    SCase "EV_Unlock". (* evt1 : Unlock / evt2 : Unlock *)
      destruct (eq_lid_dec l l0); subst.
      assert (conflict (EV_Unlock l0) (EV_Unlock l0)) by auto.
      apply Hcfl in H; invf H. (* l = l0, evt1 & evt2 conflict *)

      assert (mem' = mem'0 /\ lks'0 = unlock (unlock lks l) l0).
        eapply sc_event_unlock; apply H14.
      inv H.
      rewrite -> thds_update_neq in H14...
      unfold unlock; rewrite -> lks_update_permute.
      exists (CFG tids (thds_update thds t2 c'0) bufs mem'0 (lks_update lks l0 None)); split.
      apply CFGSC with (thds t2)...
      eapply unlock_context_invariance_lks_less...
      apply CFGSC with (thds t1)...
      eapply unlock_context_invariance_lks_more... auto. auto.

    SCase "EV_None". (* evt1 : Unlock / evt2 : None *)
      assert (mem' = mem'0 /\ unlock lks l = lks'0).
        eapply sc_event_none; apply H14.
      inv H.
      rewrite -> thds_update_neq in H14...
      exists (CFG tids (thds_update thds t2 c'0) bufs mem'0 lks); split.
      apply CFGSC with (thds t2)...
      eapply none_context_invariance...
      apply CFGSC with (thds t1)... auto.

  Case "EV_None". (* evt1 : None *)
    assert (mem = mem' /\ lks = lks').
      eapply sc_event_none; apply H6.
    inv H.
    event_cases (induction evt2) SSSCase;
      (* make it first update t2, then update t1 *)
      rewrite -> thds_update_permute.

    SCase "EV_Read". (* evt1 : None / evt2 : Read *)
      assert (mem' = mem'0 /\ lks' = lks'0).
        eapply sc_event_read; apply H14.
      inv H.
      rewrite -> thds_update_neq in H14...
      exists (CFG tids (thds_update thds t2 c'0) bufs mem'0 lks'0); split.
      apply CFGSC with (thds t2)...
      apply CFGSC with (thds t1)... auto.

    SCase "EV_Write". (* evt1 : None / evt2 : Write *)
      assert (mem'0 = mem_update mem' x n /\ lks' = lks'0).
        eapply sc_event_write; apply H14.
      inv H.
      rewrite -> thds_update_neq in H14.
      exists (CFG tids (thds_update thds t2 c'0) bufs (mem_update mem' x n) lks'0); split.
      apply CFGSC with (thds t2)...
      apply CFGSC with (thds t1)...
      eapply none_context_invariance... auto. auto.

    SCase "EV_Lock". (* evt1 : None / evt2 : Lock" *)
      assert (mem' = mem'0 /\ lks'0 = lock lks' t2 l).
        eapply sc_event_lock; apply H14.
      inv H.
      rewrite -> thds_update_neq in H14.
      exists (CFG tids (thds_update thds t2 c'0) bufs mem'0 (lock lks' t2 l)); split.
      apply CFGSC with (thds t2)...
      apply CFGSC with (thds t1)...
      eapply none_context_invariance... auto. auto.

    SCase "EV_Unlock". (* evt1 : None / evt2 : Unlock *)
      assert (mem' = mem'0 /\ lks'0 = unlock lks' l).
        eapply sc_event_unlock; apply H14.
      inv H.
      rewrite -> thds_update_neq in H14...
      exists (CFG tids (thds_update thds t2 c'0) bufs mem'0 (unlock lks' l)); split.
      apply CFGSC with (thds t2)...
      apply CFGSC with (thds t1)...
      eapply none_context_invariance... auto.

    SCase "EV_None". (* evt1 : None / evt2 : None *)
      assert (mem' = mem'0 /\ lks' = lks'0).
        eapply sc_event_none; apply H14.
      inv H.
      rewrite -> thds_update_neq in H14...
      exists (CFG tids (thds_update thds t2 c'0) bufs mem'0 lks'0); split.
      apply CFGSC with (thds t2)...
      apply CFGSC with (thds t1)... auto.
Qed.
(* ---------------- end of Diamond Lemma ---------------- *)


(* ---------------- DRF -> Well-Synchronized ---------------- *)

Lemma trace_segment :
  forall cfg1 cfg2 tr1 tr2,
    cfg1 --SC>* cfg2 [[tr1 ++ tr2]] ->
    exists cfg', cfg1 --SC>* cfg' [[tr1]] /\ cfg' --SC>* cfg2 [[tr2]].
Proof with eauto.
  intros cfg1 cfg2 tr1.
  generalize dependent cfg2; generalize dependent cfg1.
  induction tr1 as [ | hd1 tl1];
    intros.
  Case "tr1 = nil".
    exists cfg1.
    simpl in *; split...
    apply multi_refl.
  Case "tr1 = hd1 :: tl1".
    inv H.
    apply IHtl1 in H5.
    inv H5; inv H.
    exists x; split...
    apply multi_step with y...
Qed.

Lemma trace_extract :
  forall cfg1 cfg2 tevt tr,
    cfg1 --SC>* cfg2 [[tevt :: tr]] ->
    exists cfg', cfg1 --SC> cfg' [[tevt]] /\ cfg' --SC>* cfg2 [[tr]].
Proof with eauto.
  intros.
  generalize dependent tevt; generalize dependent cfg2;
  generalize dependent cfg1.
  induction tr as [ | hd tl];
    intros.
  Case "tr = nil".
    inv H. inv H5.
    exists cfg2; split...
    apply multi_refl.
  Case "tr = hd :: tl".
    inv H.
    apply IHtl in H5; inv H5.
    exists y; split...
    inv H.
    eapply multi_step...
Qed.


Lemma sc_preserves_tids :
  forall tids thds bufs mem lks tids' thds' bufs' mem' lks' tevt,
    (CFG tids thds bufs mem lks) --SC> (CFG tids' thds' bufs' mem' lks') [[tevt]] ->
    tids = tids'.
Proof with eauto.
  intros.
  inv H...
Qed.

Hint Resolve sc_preserves_tids.

Lemma tevt_in_tids :
  forall trcl trcr tids thds bufs mem lks cfg' t evt,
    (CFG tids thds bufs mem lks) --SC>* cfg' [[trcl ++ (t, evt) :: trcr]] ->
    in_tids t tids = true.
Proof with eauto.
  intros trcl.
  induction trcl as [ | hdl tll];
    intros.
  Case "trcl = nil".
    simpl in H.
    apply trace_extract in H; inv H.
    inv H0.
    inv H...
  Case "trcl = hdl :: tll".
    inv H.
    destruct y as [tids' thds' bufs' mem' lks'].
    apply IHtll in H5.
    apply sc_preserves_tids in H4.
    subst...
Qed.

Hint Resolve tevt_in_tids.


Lemma try_to_lock_locked :
  forall t1 t2 c c' mem mem' lks lks' lk,
    t1 @ (ST c [] mem (lock lks t2 lk)) ==SC> (ST c' [] mem' lks') [[EV_Lock lk]] ->
    False.
Proof with eauto.
  intros.
  remember (ST c [] mem (lock lks t2 lk)) as st1.
  remember (ST c' [] mem' lks') as st2.
  remember (EV_Lock lk) as evt.
  generalize dependent t2; generalize dependent c;
  generalize dependent c'; generalize dependent mem;
  generalize dependent mem'; generalize dependent lks;
  generalize dependent lks'; generalize dependent lk.
  scstep_cases (induction H) Case;
    intros; inversion Heqevt; inv Heqst1; inv Heqst2...
  Case "SC_AssStep".
    apply astep_event_read_or_none in H.
    inv H.
    inv H1; invf H.
  Case "SC_IfStep".
    apply bstep_event_read_or_none in H.
    inv H.
    inv H1; invf H.
  Case "SC_Lock".
    unfold lock in H.
    rewrite -> lks_update_eq in H.
    invf H.
Qed.

Lemma try_to_unlock_others_locked :
  forall t1 t2 c c' mem mem' lks lks' lk,
    t1 <> t2 ->
    t1 @ (ST c [] mem (lock lks t2 lk)) ==SC> (ST c' [] mem' lks') [[EV_Unlock lk]] ->
    False.
Proof with eauto.
  intros.
  remember (ST c [] mem (lock lks t2 lk)) as st1.
  remember (ST c' [] mem' lks') as st2.
  remember (EV_Unlock lk) as evt.
  generalize dependent t2; generalize dependent c;
  generalize dependent c'; generalize dependent mem;
  generalize dependent mem'; generalize dependent lks;
  generalize dependent lks'; generalize dependent lk.
  scstep_cases (induction H0) Case;
    intros; inversion Heqevt; inv Heqst1; inv Heqst2...
  Case "SC_AssStep".
    apply astep_event_read_or_none in H.
    inv H.
    inv H2; invf H.
  Case "SC_IfStep".
    apply bstep_event_read_or_none in H.
    inv H.
    inv H2; invf H.
  Case "SC_Unlock".
    unfold lock in H.
    rewrite -> lks_update_eq in H.
    inv H.
    assert (t = t) as Hf by auto; apply H0 in Hf; invf Hf.
Qed.


Theorem conflict_nor_drf :
  forall cfg cfgl cfg1 cfg2 trcl t1 t2 evt1 evt2,
    cfg --SC>* cfgl [[trcl]] ->
    t1 <> t2 ->
    cfgl --SC> cfg1 [[(t1, evt1)]] ->
    cfg1 --SC> cfg2 [[(t2, evt2)]] ->
    conflict evt1 evt2 ->
    (forall lk, evt1 <> EV_Unlock lk) -> (* without this, it's not provable *)
    ~ data_race_free cfg.
Proof with eauto.
  intros.
  intros Hf.
  destruct cfgl as [tids thds bufs mem lks].
  assert (in_tids t1 tids = true) as Ht1.
    apply tevt_in_tids with [] [] thds bufs mem lks cfg1 evt1.
    eapply multi_step...
  assert (in_tids t2 tids = true) as Ht2.
    apply tevt_in_tids with [(t1, evt1)] [] thds bufs mem lks cfg2 evt2.
    eapply multi_step...

  assert (exists tids thds bufs mem lks t1 t2 trc,
            cfg --SC>* (CFG tids thds bufs mem lks) [[trc]] /\
            in_tids t1 tids = true /\
            in_tids t2 tids = true /\
            t1 <> t2 /\
            datarace (thds t1) (thds t2)) as Htt.
    exists tids; exists thds; exists bufs; exists mem; exists lks;
    exists t1; exists t2; exists trcl.
    split; auto.
    split; auto.
    split; auto.
    split; auto.
    destruct cfg1 as [tids1 thds1 bufs1 mem1 lks1].
    destruct cfg2 as [tids2 thds2 bufs2 mem2 lks2].
    inv H1; inv H2.
    rewrite -> thds_update_neq in H22...
    conflict_cases (induction H3) Case.
    Case "CFL_WrWr".
      assert (mem1 = mem_update mem x n1 /\ lks = lks1).
        eapply sc_event_write; apply H20.
      inv H1.
      assert (mem2 = mem_update (mem_update mem x n1) x n2 /\ lks1 = lks2).
        eapply sc_event_write; apply H22.
      inv H1.
      apply DataRaceL with x.
      econstructor; apply H20.
      left; econstructor; apply H22.
    Case "CFL_WrRd".
      assert (mem1 = mem_update mem x n /\ lks = lks1).
        eapply sc_event_write; apply H20.
      inv H1.
      assert (mem_update mem x n = mem2 /\ lks1 = lks2).
        eapply sc_event_read; apply H22.
      inv H1.
      apply DataRaceL with x.
      econstructor; apply H20.
      right; econstructor; apply H22.
    Case "CFL_RdWr".
      assert (mem = mem1 /\ lks = lks1).
        eapply sc_event_read; apply H20.
      inv H1.
      assert (mem2 = mem_update mem1 x n /\ lks1 = lks2).
        eapply sc_event_write; apply H22.
      inv H1.
      apply DataRaceR with x.
      econstructor; apply H22.
      right; econstructor; apply H20.
    Case "CFL_LkLk".
      assert (mem = mem1 /\ lks1 = lock lks t1 l).
        eapply sc_event_lock; apply H20.
      inv H1.
      apply try_to_lock_locked in H22; invf H22.
    Case "CFL_LkUn".
      assert (mem = mem1 /\ lks1 = lock lks t1 l).
        eapply sc_event_lock; apply H20.
      inv H1.
      apply try_to_unlock_others_locked in H22; invf H22...
    Case "CFL_UnLk".
      destruct (H4 l)...
    Case "CFL_UnUn".
      destruct (H4 l)...

  apply Hf in Htt; invf Htt.
Qed.

Hint Resolve conflict_nor_drf.

(* This is the weaker version for theorem DRF->WellSynchronized,
with nothing in between tevt1 & tevt2 *)
Lemma drf_well_synchronized_weaker :
  forall cfg cfg' t1 t2 trcl trcr evt1 evt2,
    data_race_free cfg ->
    t1 <> t2 ->
    cfg --SC>* cfg' [[trcl ++ (t1, evt1) :: (t2, evt2) :: trcr]] ->
    conflict evt1 evt2 ->
    exists lk, evt1 = EV_Unlock lk.
Proof with eauto.
  intros cfg cfg' t1 t2 trcl trcr evt1 evt2 Hdrf Ht12 Hmulti Hcfl.
  apply trace_segment in Hmulti.
  inversion Hmulti as [cfgl Hl]; clear Hmulti.
  inversion Hl as [Hcfgl H12]; clear Hl.
  apply trace_extract in H12.
  inversion H12 as [cfg1 H12']; clear H12.
  inversion H12' as [Ht1 Ht2']; clear H12'.
  apply trace_extract in Ht2'.
  inversion Ht2' as [cfg2 H']; clear Ht2'.
  inversion H' as [Ht2 Hcfgr]; clear H'.

  event_cases (destruct evt1) SCase.
  SCase "EV_Read".
    assert (~ data_race_free cfg) as Hf.
      eapply conflict_nor_drf...
      intros lk Hf; invf Hf.
    apply Hf in Hdrf; invf Hdrf.
  SCase "EV_Write".
    assert (~ data_race_free cfg) as Hf.
      eapply conflict_nor_drf...
      intros lk Hf; invf Hf.
    apply Hf in Hdrf; invf Hdrf.
  SCase "EV_Lock".
    assert (~ data_race_free cfg) as Hf.
      eapply conflict_nor_drf...
      intros lk Hf; invf Hf.
    apply Hf in Hdrf; invf Hdrf.
  SCase "EV_Unlock".
    exists l...
  SCase "EV_None".
    assert (~ data_race_free cfg) as Hf.
      eapply conflict_nor_drf...
      intros lk Hf; invf Hf.
    apply Hf in Hdrf; invf Hdrf.
Qed.

Lemma list_rearrange :
  forall (X : Type) (trcl trcm trcr : list X) (tevt1 tevt3 : X),
    trcl ++ tevt1 :: tevt3 :: trcm ++ trcr =
    (trcl ++ [tevt1]) ++ tevt3 :: trcm ++ trcr.
Proof with auto.
  intros X trcl.
  induction trcl as [ | hdl tll];
    intros; simpl...
  rewrite -> IHtll...
Qed.

(* Given a trace generated from a DRF program, if any two events in
the trace conflict, there must be an Unlock event in the middle
emitted by the first thread. *)
Theorem drf_well_synchronized :
  forall cfg cfg' t1 t2 trcl trcm trcr evt1 evt2,
    data_race_free cfg ->
    t1 <> t2 ->
    cfg --SC>* cfg' [[trcl ++ (t1, evt1) :: trcm ++ (t2, evt2) :: trcr]] ->
    conflict evt1 evt2 ->
    exists lk, In (t1, EV_Unlock lk) ((t1, evt1) :: trcm).
Proof with eauto.
  intros cfg cfg' t1 t2 trcl trcm trcr evt1 evt2 Hdrf Ht12 Hmulti Hcfl.
  generalize dependent evt2; generalize dependent evt1;
  generalize dependent trcr; generalize dependent trcl;
  generalize dependent t2; generalize dependent t1;
  generalize dependent cfg'; generalize dependent cfg.
  induction trcm as [ | hdm tlm];
    intros.
  Case "trcm = nil".
    simpl in Hmulti.
    assert (exists lk, evt1 = EV_Unlock lk).
      eapply drf_well_synchronized_weaker...
    inv H.
    exists x.
    left...
  Case "trcm = hdm :: tlm".
    simpl in Hmulti.
    destruct hdm as [t3 evt3].
    destruct (eq_tid_dec t1 t3); subst.
    SCase "t1 = t3".
      destruct (excluded_middle (conflict evt3 evt2)).
      SSCase "conflict evt3 evt2".
        rewrite -> list_rearrange in Hmulti.
        apply IHtlm in Hmulti...
        inv Hmulti.
        exists x.
        right...
      SSCase "~ conflict evt3 evt2".
        (* TODO: (t1, evt1) :: (t1, evt3) :: ... :: (t2, evt2). It
           cannot swap (t1, evt1) with (t1, evt3), and since evt3 &
           evt2 do not conflict, it cannot use the induction
           hypothesis. The only way seems to be (t2, evt2), but how to
           do that? *)
      Focus 2.
    SCase "t1 <> t3".
      destruct (excluded_middle (conflict evt1 evt3)).
      SSCase "conflict evt1 evt3".
        assert (exists lk, evt1 = EV_Unlock lk).
          remember (tlm ++ (t2, evt2) :: trcr) as trcr'.
          eapply drf_well_synchronized_weaker...
        inv H0.
        exists x; left...
      SSCase "~ conflict evt1 evt3".
        apply trace_segment in Hmulti.
        inversion Hmulti as [cfgl H']; clear Hmulti; inv H'.
        apply trace_extract in H1.
        inversion H1 as [cfg1 H']; clear H1; inv H'.
        apply trace_extract in H2.
        inversion H2 as [cfg2 H']; clear H2; inv H'.
        assert (exists cfg1', cfgl --SC> cfg1' [[(t3, evt3)]] /\
                              cfg1' --SC> cfg2 [[(t1, evt1)]]).
          eapply diamond...
        inversion H4 as [cfg1' H']; clear H4; inv H'.
        assert (cfg --SC>* cfg'
                    [[trcl ++ (t3, evt3) :: (t1, evt1) :: tlm ++ (t2, evt2) :: trcr]]) as Hm'.
          apply multi_trans with cfgl...
        rewrite -> list_rearrange in Hm'.
        apply IHtlm in Hm'...
        inv Hm'; exists x.
        inv H6. left...
        right; right...
(* Only the case when t1 = t3 /\ ~ conflict evt3 evt2 is not proved yet *)

(* TODO: I come up with a premature solution:
At the very beginning, given (t1, evt1) :: trcm ++ [(t2, evt2)], first
reconstruct the trace such to the form of trcl :: (t1, evt1) :: trcm'
++ (tr, evt2) :: trcr such that in trcm', every consecutive pair
conflict (if not, it will get swapped). Then induction on trcm'.

Or, change the "list (tid * event)" to "vector"?

Or, as the paper suggests, by induction on the length of trcm?  Maybe
this will work, but I have to prepare for the finals now.

Before retrying, read the complete proof in the paper first!!
*)
Admitted.
(* ---------------- end of DRF -> Well-Synchronized ---------------- *)


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

