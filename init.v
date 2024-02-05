From HB Require Import structures.
Require Import Coq.Program.Equality.
From mathcomp Require Import all_ssreflect all_algebra.
From mathcomp Require Import lra.
From mathcomp Require Import all_classical.
From mathcomp Require Import reals ereal signed.
From mathcomp Require Import topology derive normedtype sequences
 exp measure lebesgue_measure lebesgue_integral probability hoelder.


Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.


Import Num.Def Num.Theory GRing.Theory.
Import Order.TTheory.
Import numFieldTopology.Exports.

Local Open Scope ring_scope.

Section decision_stump.
Context {R : realType}.

Definition label (d : R) := fun x => x <= d.

Definition algo (l : seq (R * bool)) :=
  let t := \big[maxr/0]_(i <- l | i.2) i.1 in
  label t.

End decision_stump.
