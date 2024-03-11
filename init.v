From HB Require Import structures.
Require Import Coq.Program.Equality.
From mathcomp Require Import all_ssreflect all_algebra.
From mathcomp Require Import lra.
From mathcomp Require Import all_classical.
From mathcomp Require Import reals ereal signed.
From mathcomp Require Import topology derive normedtype sequences
 exp measure lebesgue_measure lebesgue_integral probability hoelder fintype.

Notation "\prod_ ( i <- r | P ) F" :=
  (\big[*%E/1%:E]_(i <- r | P%B) F%E) : ereal_scope.
Notation "\prod_ ( i <- r ) F" :=
  (\big[*%E/1%:E]_(i <- r) F%E) : ereal_scope.
Notation "\prod_ ( m <= i < n | P ) F" :=
  (\big[*%E/1%:E]_(m <= i < n | P%B) F%E) : ereal_scope.
Notation "\prod_ ( m <= i < n ) F" :=
  (\big[*%E/1%:E]_(m <= i < n) F%E) : ereal_scope.
Notation "\prod_ ( i | P ) F" :=
  (\big[*%E/1%:E]_(i | P%B) F%E) : ereal_scope.
Notation "\prod_ i F" :=
  (\big[*%E/1%:E]_i F%E) : ereal_scope.
Notation "\prod_ ( i : t | P ) F" :=
  (\big[*%E/1%:E]_(i : t | P%B) F%E) (only parsing) : ereal_scope.
Notation "\prod_ ( i : t ) F" :=
  (\big[*%E/1%:E]_(i : t) F%E) (only parsing) : ereal_scope.
Notation "\prod_ ( i < n | P ) F" :=
  (\big[*%E/1%:E]_(i < n | P%B) F%E) : ereal_scope.
Notation "\prod_ ( i < n ) F" :=
  (\big[*%E/1%:E]_(i < n) F%E) : ereal_scope.
Notation "\prod_ ( i 'in' A | P ) F" :=
  (\big[*%E/1%:E]_(i in A | P%B) F%E) : ereal_scope.
Notation "\prod_ ( i 'in' A ) F" :=
  (\big[*%E/1%:E]_(i in A) F%E) : ereal_scope.


Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.


Import Num.Def Num.Theory GRing.Theory.
Import Order.TTheory.
Import numFieldTopology.Exports.

Local Open Scope ring_scope.
Local Open Scope classical_set_scope.

Section move_to_analysis.
Context {R : realType}.

Lemma ln_lt0 (x : R) : 0 < x < 1 -> ln x < 0.
Proof. by move=> /andP[x_gt0 x_lt1]; rewrite -ltr_expR expR0 lnK. Qed.
End move_to_analysis.

Section decision_stump.
Context d (T : measurableType d) {R : realType} (P : probability T R) (X : {RV P >-> R}) (t : R) (delta : R) (epsilon : R) (n : nat).
Hypotheses (epsilon_01 : 0 < epsilon < 1) (delta_01 : 0 < delta < 1) (tge0: 0 <= t).


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


Definition choose (l : seq (R * bool)) :=
  \big[maxr/0]_(i <- l | i.2) i.1.

Lemma choose_prop_1 (l : seq R) :
  choose (llist l) <= t.
Proof.
  rewrite /choose /llist /label.
  rewrite big_map.
  elim: l.
  by rewrite big_nil tge0.
  move=> a l ih.
  rewrite big_cons/=.
  case: ifPn => //.
  move=> a_le_t; rewrite /maxr.
  by case: ifPn.
Qed.

Lemma choose_prop_2 (l : seq (R * bool)) :
  forall i, (i < size l)%nat ->
       let p := nth (0, false) l i in
       p.2 -> p.1 <= choose l.
Proof.
elim: l => //= a l ihl i.
elim: i => //= [_ aT|].
  rewrite /choose big_cons aT /maxr.
  by case: ifPn => //; lra.
  move=> n0 ihi; rewrite /choose big_cons.
  case: ifPn => h1 h2 h3.
    by rewrite le_max ihl// orbT.
    by rewrite ihl.
Qed.




Definition algo (l : seq (R * bool)) :=
  let t := choose l in
  label t.

Definition seq_of_RV := {RV P >-> R} ^nat.
Definition Xn : seq_of_RV := [sequence X]_n.

Variable t0 : R.
Definition I (X : {RV P >-> R}) := [set x | t0 <= X x <= t ].

Definition prob_of_X := P (I X).

Hypothesis (PXeps : prob_of_X = epsilon%:E).

Definition RV_prod (f g : T -> R) := fun i => (f i, g i).
Notation "f '\times' g" := (RV_prod f g) (at level 10).


Definition prob_of_seq := (\prod_(i < n) (P (I (Xn i))))%E.

Definition test :=
  let row_vector : 'rV_n := \row_(j < n) X in
    @seq_of_rV R _ row_vector.

Definition x_leq_t (X : {RV P >-> R}) := [set x | 0 > X x <= t]. (* \mu(0, t] *)
Lemma prob_xt_leq_eps (training_exs : seq (R * bool)) : P (x_leq_t X) <= epsilon -> error (algo training_exs) <= epsilon.
Lemma prob_xt_gt_eps : P (x <= t) > epsilon -> 1 - (1 - epsilon)^+n >= 1 - delta.

Definition pac_learnable (epsilon delta : R) := (n%:R) >= ln delta / ln (1 - epsilon) -> P (error (algo (llist ((* seq of n length *)))) <= epsilon) >= 1 - delta.

End decision_stump.
