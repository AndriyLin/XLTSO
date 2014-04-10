(**

This is for the final project of CS565 Programming Languages in
Purdue.

Write a simple programming language that exposes relaxed memory
semantics (e.g. TSO). Prove that data race free programs have SC
semantics.

Written in Coq, mechanically formalized and verified.

Andriy LIN

Updated: 04/09/2014

*)


(* TODOS

1. Copy the definitions from SF. Think about how much to copy.

Should have write buffer, thread, lock, etc.

thread: tid -> com, lockstatus may be lockid -> option tid.

Paper: A better x86 memory model: x86-TSO

*)


Require Export Lib.


