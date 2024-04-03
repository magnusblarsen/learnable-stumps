From HB Require Import structures.
Require Import Coq.Program.Equality.
From mathcomp Require Import all_ssreflect all_algebra.
From mathcomp Require Import lra.
From mathcomp Require Import all_classical.
From mathcomp Require Import reals ereal signed.
From mathcomp Require Import topology derive normedtype sequences
 exp measure lebesgue_measure lebesgue_integral probability hoelder fintype kernel.
Require Import util.

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

Section decision_stump.
Context d (T : measurableType d) {R : realType} (P : probability T R) (X : {RV P >-> R}) (t : R) (delta : R) (epsilon : R) (n : nat).
Hypotheses (epsilon_01 : 0 < epsilon < 1) (delta_01 : 0 < delta < 1) (tge0: 0 <= t).


Definition label (d : R) := fun x => x <= d.

Definition llist (l : seq R) :=
  map (fun x => (x, label t x)) l.

Definition error (h: R -> bool) := P [set x : T | h (X x) != label t (X x)].

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

(*
Lemma negE (b : bool) : ~~ b = (~ b) :> Prop.
Proof. by rewrite propeqE; split;  move/negP. Qed.

Lemma orE (b1 b2 : bool) : (b1 || b2) = (b1 \/ b2) :> Prop.
Proof. by rewrite propeqE; split; move/orP. Qed.

Lemma in_pred_setE (TT : Type) (A : {pred TT}) (x : TT) :
  (x \in [set x | A x]) = A x.
Proof. by apply/idP/idP; rewrite inE /=. Qed.
*)

Lemma test x y :
  [set z | label x z != label y z] = `[minr x y, maxr x y[.
Proof.
Admitted.

Lemma set_label_neqE x y :
  [set z | label x z != label y z] = `]minr x y, maxr x y].
Proof.
apply: eq_set=> z.
rewrite !in_itv /= gt_min le_max !ltNge /label.
by case: lerP=> _; case: lerP.
Qed.

Lemma always_succeed:
  (P [set x | 0 <= X x <= t]%R <= epsilon%:E)%E ->
  forall l, (error (label (choose (llist l))) <= epsilon%:E)%E.
Proof.
move=> h l.
rewrite /error.
apply: (le_trans _ h).
apply: le_measure.
- rewrite inE -[Y in d.-measurable Y]setTI.
  set F := fun y => label (choose (llist l)) y != label t y.
  rewrite (_ : [set _ | _] = X@^-1` [set y | F y]) //.
  apply: measurable_funP=> //.
  by rewrite /F set_label_neqE.
- rewrite inE -[Y in d.-measurable Y]setTI.
  rewrite (_ : [set _ | _] = X@^-1` [set y | 0 <= y <= t]) //.
  apply: measurable_funP=> //.
  by rewrite -set_itvcc.
move=> x /=.
have h2 := choose_prop_1 l.
rewrite /label.
rewrite negb_eqb.
case: addbP=> //.
case: negP.
  move=> /[swap] <- /[swap] _ /negP.
  rewrite -ltNge ?num_real // andbT => A.
  apply/ltW/(le_lt_trans _ A).
  exact: bigmax_ge_id.
by move/contrapT /le_trans => /(_ _ h2) ->.
Qed.

Program Fixpoint sample n : probability (projT2 (S T n)) R :=
  match n with
  | 0 => _
  | m.+1 =>
      (* bind (bind P (sample m)) *)
      (*      (kdirac cons) *)
      bind P _
        (* (fun x => *)
        (*    bind (sample m) *)
        (*      (fun l => ret (x :: l))) *)
      (* bind *)
      (*   (sample m) *)
      (*   (fun l => *)
      (*      bind *)
      (*        P (fun x => ret (x :: l)) *)
      (*   ) *)
  end.
Next Obligation.
move=> n0 _.
apply: ret.
change unit.
exact: tt.

(probability (projT2 (S T n)) R)

Lemma test () :
  seq T measurable.



Definition algo (l : seq (R * bool)) :=
  let t := choose l in
  label t.



Definition x_leq_t (X : {RV P >-> R}) := [set x | 0 > X x <= t]. (* \mu(0, t] *)
Lemma prob_xt_leq_eps (training_exs : seq (R * bool)) : P (x_leq_t X) <= epsilon -> error (algo training_exs) <= epsilon.
Lemma prob_xt_gt_eps : P (x <= t) > epsilon -> 1 - (1 - epsilon)^+n >= 1 - delta.

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

Definition pac_learnable (epsilon delta : R) := (n%:R) >= ln delta / ln (1 - epsilon) -> P (error (algo (llist ((* seq of n length *)))) <= epsilon) >= 1 - delta.


Variable t0 : R.
Definition I (X : {RV P >-> R}) := [set x | t0 <= X x <= t ].

Definition seq_of_RV := {RV P >-> R} ^nat.
Definition Xn : seq_of_RV := [sequence X]_n.

Definition prob_of_X := P (I X).

Hypothesis (PXeps : prob_of_X = epsilon%:E).

Definition RV_prod (f g : T -> R) := fun i => (f i, g i).
Notation "f '\times' g" := (RV_prod f g) (at level 10).


Definition prob_of_seq := (\prod_(i < n) (P (I (Xn i))))%E.
End decision_stump.
