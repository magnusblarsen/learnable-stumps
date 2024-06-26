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
Context d (T : measurableType d) {R : realType} (P : probability T R) (X : {RV P >-> R}) (t : R) (delta epsilon theta : R) (n : nat).
Hypotheses (epsilon_01 : 0 < epsilon < 1) (delta_01 : 0 < delta < 1) (tge0: 0 <= t) (theta_eps : P [set x | X x \in `[theta, t]] = epsilon%:E).

Definition label (d : R) := fun x => x <= d.

Definition llist (l : seq R) :=
  map (fun x => (x, label t x)) l.

Definition error (h: R -> bool) := P [set x : T | h (X x) != label t (X x)].

Definition choose (l : seq (R * bool)) :=
  \big[maxr/0]_(i <- l | i.2) i.1.

Definition algo (l : seq (R * bool)) :=
  let t := choose l in
  label t.

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




Obligation Tactic := idtac.

(* Definition sample0 n (p : probability T R) x (l :  := ret (x :: l). *)

(* Definition sample1 n (p : probability (projT2 (S T n)) R) x := *)
(*   bind p sample0. *)

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

Definition complexity := ln delta / ln (1 - epsilon) - 1.
Lemma complexity_enough : n%:R >= complexity -> ((1-epsilon) ^+ (n.+1)) <= delta.
Proof.
move: epsilon_01 delta_01 => /andP[? ?] /andP[? ?].
rewrite/complexity lerBlDl nat1r.
rewrite ler_ndivrMr; last first.
  rewrite -ln1 ltr_ln ?posrE; lra.
rewrite mulrC.
rewrite mulr_natr.
rewrite -lnXn; last lra.
rewrite ler_ln// posrE ?exprn_gt0//; lra.
Qed.




Definition mybind (A : measurableType d) B (mu : {measure set A -> \bar R}) (f : A -> set B -> \bar R) : (set B -> \bar R) := \int[mu]_a f a.

Local Open Scope ereal_scope.
Fixpoint sample n : measure (projT2 (S T n)) R :=
  match n with
  | 0 => ret (d:=projT1 (S T 0)) tt
  | m.+1 => P \x^ (sample m)
  end.

Fixpoint sample n : (set (projT2 (S T n)) -> \bar R) :=
  match n with
  | 0 => ret (d:=projT1 (S T 0)) tt
  | m.+1 =>
      mybind
        P
        (fun x =>
           mybind
             (@sample m)
             (fun l => ret (x, l)))


        (* (sample m) *)
        (* (fun l => *)
        (*    bind *)
        (*      P (fun x => ret (x, l))) *)
  end.

Program Fixpoint sample n : probability (projT2 (S T n)) R :=
  match n with
  | 0 => ret (d:=projT1 (S T 0)) tt
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
Show Proof.

(* Lemma test () :
  seq T measurable.*)

Definition pac_learnable (epsilon delta : R) (l : n.-tuple T):= (n%:R >= ln delta / ln (1 - epsilon) -> P (error (algo (llist l)) <= epsilon) >= 1 - delta)%R.


Lemma miss_prob:
  P [set x | X x \in `[theta, t]] >= epsilon ->
  P [set x | if label t x then x else 0 < theta] <= 1 - epsilon.

Lemma miss_prob:
  P (`[theta, t]) >= epsilon ->
  P [set x : T | forall a b,
        let (a,b) = label target x in
        (if b then a else 0) < theta] <= 1 - epsilon.


End decision_stump.
