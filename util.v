
(* Require Import decision_stump. *)

(* Local Open Scope ereal_scope. *)

Context d {T : measurableType d} {R : realType}.
Definition ret : R.-ker T ~> T := kdirac (@measurable_id _ _ setT).

Variables (mu : probability T R) (f : (*T -> probability T R*) R.-pker T ~> T).

Let mu' : unit -> {measure set T -> \bar R} := fun _ : unit => mu.

Let mu'_kernel U : measurable U -> measurable_fun setT (mu' ^~ U).
Proof. by move=> mU /=; exact: measurable_cst. Qed.

HB.instance Definition _ := isKernel.Build _ _ unit T R mu' mu'_kernel.

Let f' : unit * T -> {measure set T -> \bar R} := fun ttt => f ttt.2.

Let f'_kernel U : measurable U -> measurable_fun setT (f' ^~ U).
Proof.
move=> mU /=.
apply: (@measurableT_comp _ _ _ _ _ _ (fun x => f x U) _ snd) => //.
exact/measurable_kernel.
Qed.

HB.instance Definition _ := isKernel.Build _ _ _ _ R f' f'_kernel.

Definition bind := kcomp mu' f' tt.

Lemma bindE A : bind A = \int[mu]_x f x A. Proof. by []. Qed.

HB.instance Definition _ := Measure.on bind.

Lemma bindT : bind setT = 1%E.
Proof.
rewrite bindE.
under eq_integral => x _ do rewrite (*probability_setT*) prob_kernel.
by rewrite integral_cst// mul1e; exact: probability_setT.
Qed.

HB.instance Definition _ :=
  @Measure_isProbability.Build _ _ _ bind bindT.

Check bind : probability T R.
