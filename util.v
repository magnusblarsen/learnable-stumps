(* Require Import decision_stump. *)

(* Local Open Scope ereal_scope. *)
Require Import kernel.

Context d {T : measurableType d} {R : realType}.

(* a pker that takes a superfluous arg *)
Section pker_curry.
Context d {T : measurableType d} {R : realType}
        d1 {T1 : measurableType d1}.
Variable (f : R.-pker T ~> T1).

Definition pker_curry (_ : T) : T -> {measure set T1 -> \bar R} := f.

Let pker_curry_kernel (x : T) U :
  measurable U -> measurable_fun setT (pker_curry x ^~ U).
Proof. by move=> mU/=; exact/measurable_kernel. Qed.

HB.instance Definition _ (x : T) :=
  isKernel.Build _ _ T T1 R (pker_curry x) (pker_curry_kernel x).

Let pker_curryT x : forall x', pker_curry x x' setT = 1%E.
Proof. by move=> x'; rewrite /pker_curry prob_kernel. Qed.

HB.instance Definition _ (x : T) :=
  Kernel_isProbability.Build _ _ _ _ R (pker_curry x) (pker_curryT x).

End pker_curry.

(* a pker that forgets its first arg *)
Section pker_snd.
Context d {T : measurableType d} {R : realType}
        d1 {T1 : measurableType d1}
        d2 {T2 : measurableType d2}.
Variable (g : R.-pker T1 ~> T2).

Definition pker_snd : T * T1 -> {measure set T2 -> \bar R} := g \o snd.

Let pker_snd_kernel U : measurable U -> measurable_fun setT (pker_snd ^~ U).
Proof.
move=> mU /=.
apply: (@measurableT_comp _ _ _ _ _ _ (fun x => g x U) _ snd) => //.
exact/measurable_kernel.
Qed.

HB.instance Definition _ := isKernel.Build _ _ _ _ R pker_snd pker_snd_kernel.

Let pker_sndT x : pker_snd x setT = 1%E.
Proof. by rewrite /pker_snd /= prob_kernel. Qed.

HB.instance Definition _ (x : T) :=
  Kernel_isProbability.Build _ _ _ _ R pker_snd pker_sndT.

End pker_snd.

Section giry_def.
Local Open Scope ereal_scope.
Context d {T : measurableType d} {R : realType} d' {T' : measurableType d'}.
Let G := pprobability T R.

Definition ret : R.-pker T ~> T := kdirac (@measurable_id _ _ setT).

Variables (mu : probability T R) (f : R.-pker T ~> T').

Definition bind :=
  kcomp (kprobability (measurable_cst (mu : pprobability T R)))(*mu'*) (pker_snd f) tt.

Lemma bindE A : bind A = \int[mu]_x f x A. Proof. by []. Qed.

HB.instance Definition _ := Measure.on bind.

Lemma bindT : bind setT = 1%E.
Proof.
rewrite bindE.
under eq_integral => x _ do rewrite prob_kernel.
by rewrite integral_cst// mul1e; exact: probability_setT.
Qed.

HB.instance Definition _ :=
  @Measure_isProbability.Build _ _ _ bind bindT.

Check bind : probability T' R.

End giry_def.

Section giry_prop.
Local Open Scope ereal_scope.
Context d {T : measurableType d} {R : realType}
        d1 {T1 : measurableType d1}
        d2 {T2 : measurableType d2}.

Lemma giryretf (f : R.-pker T ~> T1) (x : T) A :
  measurable A -> bind (ret x) f A = f x A.
Proof.
move=> ?; rewrite bindE /ret/= integral_dirac ?diracT ?mul1e//.
exact: measurable_kernel.
Qed.

Lemma girymret (mu : probability T R) A :
  measurable A -> bind mu (@ret _ _ _) A = mu A.
Proof.
by move=> ?; rewrite bindE /ret/kdirac/= integral_indic// setIT.
Qed.

Variables (mu : probability T R) (f : R.-pker T ~> T1) (g : R.-pker T1 ~> T2).

Definition bindfg : T -> {measure set T2 -> \bar R} :=
  fun x => ((pker_curry f x) \; pker_snd g) x.

Let bindfg_kernel U : measurable U -> measurable_fun setT (bindfg ^~ U).
Proof.
move=> mU.
apply: (measurable_fun_integral_sfinite_kernel (pker_snd g ^~ U)) => //.
exact/measurable_kernel.
Qed.

HB.instance Definition _ := isKernel.Build _ _ _ _ R bindfg bindfg_kernel.

Let bindfgT x : bindfg x setT = 1.
Proof.
rewrite /bindfg /= /kcomp /=.
under eq_integral do rewrite prob_kernel.
by rewrite integral_cst// mul1e prob_kernel.
Qed.

HB.instance Definition _ := Kernel_isProbability.Build _ _ _ _ R bindfg bindfgT.

Lemma giryA U : measurable U ->
  bind (bind mu f) g U = bind mu bindfg (*(fun x => bind (f x) g)*) U.
Proof.
move=> mU.
rewrite !bindE.
have -> : bind mu f = kcomp (cst mu) (pker_snd f) tt by [].
have -> // := @integral_kcomp _ _ d1  _ T T1 R
  (kprobability (measurable_cst (mu : pprobability T R (*IMP*))))
  (pker_snd f) tt (g ^~ U).
exact/measurable_kernel.
Qed.

End giry_prop.
