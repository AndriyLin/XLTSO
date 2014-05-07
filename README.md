XLTSO
=====

Write a simple programming language that exposes relaxed memory
semantics (e.g. TSO). Prove that data race free programs have SC
semantics.

PS: This is for the final project of CS565 Programming Languages in
Purdue, 14spring.

Written in Coq, mechanically formalized and verified.

Xuankang LIN

----------

Contents:

* Basics.v

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

* TSO.v

    1. Uni-thread Semantics
    2. Multi-threads Semantics
    3. Proof of having TSO semantics

* SC.v

    1. Uni-thread Semantics
    2. Multi-threads Semantics

* DRF.v

    1. Data-Race-Free
    2. Diamond Lemma
    3. DRF -> Well-Synchronized (part)
    4. DRF Guarantee Property (not yet)

