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
Import MatrixFormula.

Local Open Scope ring_scope.
Local Open Scope classical_set_scope.

Section move_to_analysis.
Context {R : realType}.

Lemma ln_lt0 (x : R) : 0 < x < 1 -> ln x < 0.
Proof. by move=> /andP[x_gt0 x_lt1]; rewrite -ltr_expR expR0 lnK. Qed.
End move_to_analysis.

Section decision_stump.
Context d (T : measurableType d) {R : realType} (P : probability T R) (X : {RV P >-> R}) (t : R) (delta : R) (epsilon : R) (n : nat).
Hypotheses (epsilon_01 : 0 < epsilon < 1) (delta_01 : 0 < delta < 1).

  


Definition label (d : R) := fun x => x <= d.

Definition llist (l : seq R) := 
  map (fun x => (x, label t x)) l.

Definition error (h: R -> bool) := P [set x : T | h (X x) != label t (X x)].


Lemma n_value : 1 - (1 - epsilon)^+n >= 1 - delta -> (n%:R) >= ln delta / ln (1 - epsilon).
Proof.
rewrite -opprB opprD opprK -lerBrDr addrAC subrr add0r lerNr opprK.
rewrite -ler_ln; last 2 first.
- by rewrite posrE exprn_gt0 // subr_gt0 (andP epsilon_01).2.
- by rewrite posrE (andP delta_01).1.
rewrite lnXn; last first.
  by rewrite subr_gt0 (andP epsilon_01).2.
rewrite -ler_ndivrMr.
- by rewrite invrK mulrC mulr_natr.
rewrite invr_lt0 -ln1 ltr_ln. 
- by rewrite gtrBl (andP epsilon_01).1.
- rewrite posrE subr_gt0 (andP epsilon_01).2 //.
by rewrite posrE ltr01.
Qed.


Definition algo (l : seq (R * bool)) :=
  let t := \big[maxr/0]_(i <- l | i.2) i.1 in
  label t.

Definition seq_of_RV := {RV P >-> R} ^nat.
Definition Xn : seq_of_RV := [sequence X]_n.

Variable t0 : R.
Definition I (X : {RV P >-> R}) := [set x | t0 <= X x <= t ].

Definition prob_of_X := P (I X).

Hypothesis (PXeps : prob_of_X = epsilon%:E).

Definition prob_of_seq := \prod_(i < n) P (I (X i)).

Definition test :=
  let row_vector : 'rV_n := \row_(j < n) X in
    @seq_of_rV R _ row_vector.


Definition pac_learnable (epsilon delta : R) := (n%:R) >= ln delta / ln (1 - epsilon) -> P (error (algo (llist ((* seq of n length *)))) <= epsilon) >= 1 - delta.

End decision_stump.
