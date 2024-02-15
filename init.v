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
Local Open Scope classical_set_scope.

Section decision_stump.
Context d (T : measurableType d) {R : realType} (P : probability T R) (X : {RV P >-> R}) (t_hat : R) (delta : R) (epsilon : R)(n : nat).
Hypotheses (epsilon_01 : 0 <= epsilon < 1) (delta_01 : 0 < delta < 1).

  


Definition label (d : R) := fun x => x <= d.

Definition llist (l : seq R) := 
  map (fun x => (x, label t_hat x)) l.

Definition error (h: R -> bool) := P [set t : T | h (X t) != label t_hat (X t)].
  
Lemma n_value : 1 - (1 - epsilon)^+(n%:R) >= 1 - delta -> (n%:R) >= ln delta / ln (1 - epsilon).
Proof.
  rewrite -opprB opprD opprK -lerBrDr addrAC subrr add0r lerNr opprK.
  rewrite -ler_ln; last 2 first.
  rewrite posrE exprn_gt0 // subr_gt0 (andP epsilon_01).2 //. 
  rewrite posrE (andP delta_01).1 //.
  rewrite lnXn; last 1 first. 
  rewrite subr_gt0 (andP epsilon_01).2 //.
  Admitted. 





(* rewrite mulrC. rewrite ler_ndivrMr. *) 


Definition algo (l : seq (R * bool)) :=
  let t := \big[maxr/0]_(i <- l | i.2) i.1 in
  label t.

Definition pac_learnable (epsilon delta : R) := false.

End decision_stump.
