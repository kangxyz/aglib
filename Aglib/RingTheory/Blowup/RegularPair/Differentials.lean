/-
Copyright (c) 2026 kangxyz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.RingTheory.Blowup.RegularPair.Reciprocal
public import Mathlib.RingTheory.IsAdjoinRoot
public import Mathlib.RingTheory.Kaehler.Polynomial
public import Mathlib.Algebra.TrivSqZeroExt.Basic
public import Mathlib.LinearAlgebra.Quotient.Basic
public import Mathlib.Tactic.Abel

/-!
# Differentials of the original regular-pair blowup charts

For the actual quotient `B = R[T]/(x * T - y)`, the relative differential
module over `Λ` has the presentation
`((B ⊗[R] Ω[R⁄Λ]) × B) / B (T dx - dy, x)`. Its two generator formulas
retain the original coefficient map and original coordinate. No freeness,
smoothness, or residue-separability premise is used in this presentation.

The same construction applies to any specified presentation of the original
algebra by this polynomial. This transfers the result to the saturated chart
through `pairChartEquiv`, with precisely its regular-pair hypotheses.
-/

@[expose] public noncomputable section

open Polynomial TensorProduct

universe u v w

namespace Localization.Away

/-- Evaluation of the original chart polynomial keeps both the coefficient map and root. -/
theorem pairPolynomial_eval₂ {R T : Type*} [CommRing R] [CommRing T]
    (x y : R) (f : R →+* T) (t : T) :
    (pairPolynomial x y).eval₂ f t = f x * t - f y := by
  simp only [pairPolynomial, Polynomial.eval₂_sub, Polynomial.eval₂_mul,
    Polynomial.eval₂_C, Polynomial.eval₂_X]

end Localization.Away

namespace IsAdjoinRoot

variable {R : Type u} {S : Type v} [CommRing R] [CommRing S] [Algebra R S]
  {x y : R} (h : IsAdjoinRoot S (Localization.Away.pairPolynomial x y))

section Derivations

variable (Λ : Type w) [CommRing Λ] [Algebra Λ R] [Algebra Λ S]
  [IsScalarTower Λ R S]
  {M : Type*} [AddCommGroup M] [Module R M] [Module S M] [Module Λ M]
  [IsScalarTower R S M] [IsScalarTower Λ R M] [IsScalarTower Λ S M]

omit [Algebra Λ R] [IsScalarTower Λ R S] [Module R M] [IsScalarTower R S M]
  [IsScalarTower Λ R M] [IsScalarTower Λ S M] in
/-- Derivations on an actual one-generator presentation are determined by their
values on the original coefficient ring and original root. -/
theorem pair_derivation_ext {d e : Derivation Λ S M}
    (hR : ∀ r : R, d (algebraMap R S r) = e (algebraMap R S r))
    (hT : d h.root = e h.root) : d = e := by
  apply Derivation.ext
  intro z
  obtain ⟨p, rfl⟩ := h.map_surjective z
  induction p using Polynomial.induction_on' with
  | add p q hp hq => simp only [map_add, hp, hq]
  | monomial n r =>
    have hm : h.map (monomial n r) = algebraMap R S r * h.root ^ n := by
      rw [← C_mul_X_pow_eq_monomial, map_mul, map_pow, h.map_X,
        ← h.algebraMap_apply]
    simp only [hm, Derivation.leibniz, Derivation.leibniz_pow, hR, hT]

/-- Construct the derivation and its original generator equations together,
before exposing the square-zero presentation to any later transport. -/
def pairLiftDerivationData (d : Derivation Λ R M) (m : M)
    (hm : h.root • d x - d y + algebraMap R S x • m = 0) :
    {D : Derivation Λ S M //
      (∀ r : R, D (algebraMap R S r) = d r) ∧ D h.root = m} := by
  let unop : Sᵐᵒᵖ →+* S :=
    { toFun := MulOpposite.unop
      map_zero' := rfl
      map_one' := rfl
      map_add' _ _ := rfl
      map_mul' a b := mul_comm (MulOpposite.unop b) (MulOpposite.unop a) }
  letI : Module Sᵐᵒᵖ M := Module.compHom M unop
  letI : IsCentralScalar S M := ⟨fun _ _ => rfl⟩
  let i : R →+* TrivSqZeroExt S M :=
    { toFun := fun r => (algebraMap R S r, d r)
      map_zero' := by
        apply TrivSqZeroExt.ext
        · exact map_zero (algebraMap R S)
        · exact map_zero d
      map_one' := by
        apply TrivSqZeroExt.ext
        · exact map_one (algebraMap R S)
        · exact d.map_one_eq_zero
      map_add' := by
        intro a b
        apply TrivSqZeroExt.ext
        · change algebraMap R S (a + b) = algebraMap R S a + algebraMap R S b
          exact map_add (algebraMap R S) a b
        · change d (a + b) = d a + d b
          exact map_add d a b
      map_mul' := by
        intro a b
        apply TrivSqZeroExt.ext
        · exact map_mul (algebraMap R S) a b
        · change d (a * b) = algebraMap R S a • d b + algebraMap R S b • d a
          simpa only [algebraMap_smul] using d.leibniz a b }
  have hi : (Localization.Away.pairPolynomial x y).eval₂ i (h.root, m) = 0 := by
    refine (Localization.Away.pairPolynomial_eval₂ x y i (h.root, m)).trans ?_
    apply TrivSqZeroExt.ext
    · change algebraMap R S x * h.root - algebraMap R S y = 0
      simpa only [Localization.Away.pairPolynomial, aeval_sub, aeval_mul,
        aeval_C, aeval_X] using h.aeval_root_self
    · change algebraMap R S x • m + h.root • d x - d y = 0
      calc
        _ = h.root • d x - d y + algebraMap R S x • m := by abel
        _ = 0 := hm
  let F := h.lift i (h.root, m) hi
  have hFbase (r : R) : F (algebraMap R S r) = (algebraMap R S r, d r) :=
    h.lift_algebraMap hi r
  have hFroot : F h.root = (h.root, m) := h.lift_root hi
  have hFfst (z : S) : (F z).fst = z := by
    let G := (TrivSqZeroExt.fstHom S S M).toRingHom.comp F
    have hz : (Localization.Away.pairPolynomial x y).eval₂
        (algebraMap R S) h.root = 0 := h.aeval_root_self
    have hG : G = h.lift (algebraMap R S) h.root hz :=
      h.eq_lift hz G (fun r => by
        change (F (algebraMap R S r)).fst = algebraMap R S r
        rw [hFbase]
        rfl) (by
          change (F h.root).fst = h.root
          rw [hFroot]
          rfl)
    have hId : RingHom.id S = h.lift (algebraMap R S) h.root hz :=
      h.eq_lift hz (RingHom.id S) (fun _ => rfl) rfl
    exact RingHom.congr_fun (hG.trans hId.symm) z
  have hFscalar (a : Λ) : F (algebraMap Λ S a) =
      TrivSqZeroExt.inl (algebraMap Λ S a) := by
    rw [IsScalarTower.algebraMap_apply Λ R S, hFbase]
    apply TrivSqZeroExt.ext
    · rfl
    · exact d.map_algebraMap a
  let D : Derivation Λ S M :=
    { toFun := fun z => (F z).snd
      map_add' := by intro a b; simp
      map_smul' := by
        intro a z
        rw [Algebra.smul_def, map_mul, hFscalar]
        simp only [TrivSqZeroExt.snd_mul, TrivSqZeroExt.fst_inl,
          TrivSqZeroExt.snd_inl, smul_zero, add_zero, algebraMap_smul, RingHom.id_apply]
      map_one_eq_zero' := by simp
      leibniz' := by
        intro a b
        change (F (a * b)).snd = a • (F b).snd + b • (F a).snd
        calc
          (F (a * b)).snd = (F a * F b).snd :=
            congrArg TrivSqZeroExt.snd (F.map_mul a b)
          _ = (F a).fst • (F b).snd + (F b).fst • (F a).snd := rfl
          _ = a • (F b).snd + b • (F a).snd := by rw [hFfst, hFfst] }
  refine ⟨D, ?_, ?_⟩
  · intro r
    change (F (algebraMap R S r)).snd = d r
    exact congrArg TrivSqZeroExt.snd (hFbase r)
  · change (F h.root).snd = m
    exact congrArg TrivSqZeroExt.snd hFroot

/-- A compatible coefficient derivation and root value give a derivation on
the original algebra. The relation is imposed in the actual target module. -/
def pairLiftDerivation (d : Derivation Λ R M) (m : M)
    (hm : h.root • d x - d y + algebraMap R S x • m = 0) : Derivation Λ S M :=
  (pairLiftDerivationData h Λ d m hm).val

omit [IsScalarTower Λ R M] in
/-- The lifted derivation retains the original coefficient derivation. -/
@[simp]
theorem pairLiftDerivation_base (d : Derivation Λ R M) (m : M)
    (hm : h.root • d x - d y + algebraMap R S x • m = 0) (r : R) :
    pairLiftDerivation h Λ d m hm (algebraMap R S r) = d r :=
  (pairLiftDerivationData h Λ d m hm).property.1 r

omit [IsScalarTower Λ R M] in
/-- The lifted derivation has the prescribed value at the original root. -/
@[simp]
theorem pairLiftDerivation_root (d : Derivation Λ R M) (m : M)
    (hm : h.root • d x - d y + algebraMap R S x • m = 0) :
    pairLiftDerivation h Λ d m hm h.root = m :=
  (pairLiftDerivationData h Λ d m hm).property.2

end Derivations

section Presentation

variable (Λ : Type w) [CommRing Λ] [Algebra Λ R] [Algebra Λ S]
  [IsScalarTower Λ R S]

/-- Coefficient forms and the coefficient of the original root differential. -/
abbrev pairDifferentialAmbient := (S ⊗[R] KaehlerDifferential Λ R) × S

/-- The differential of the original relation `x * T - y`. -/
def pairDifferentialRelation : pairDifferentialAmbient (R := R) (S := S) Λ :=
  (h.root ⊗ₜ[R] KaehlerDifferential.D Λ R x -
      (1 : S) ⊗ₜ[R] KaehlerDifferential.D Λ R y,
    algebraMap R S x)

/-- The actual one-relation module presentation, with its original `S`-action. -/
abbrev pairDifferentialPresentation :=
  pairDifferentialAmbient (R := R) (S := S) Λ ⧸ S ∙ pairDifferentialRelation h Λ

/-- The original quotient map on coefficient forms and the root coefficient. -/
def pairDifferentialMk : pairDifferentialAmbient (R := R) (S := S) Λ →ₗ[S]
    pairDifferentialPresentation h Λ :=
  (S ∙ pairDifferentialRelation h Λ).mkQ

/-- Coefficient forms enter by the original scalar extension followed by the quotient. -/
def pairBaseDifferential : KaehlerDifferential Λ R →ₗ[R]
    pairDifferentialPresentation h Λ :=
  (((pairDifferentialMk h Λ).comp
      (LinearMap.inl S (S ⊗[R] KaehlerDifferential Λ R) S)).restrictScalars R).comp
    (TensorProduct.mk R S (KaehlerDifferential Λ R) 1)

omit [Algebra Λ S] [IsScalarTower Λ R S] in
@[simp]
theorem pairBaseDifferential_apply (η : KaehlerDifferential Λ R) :
    pairBaseDifferential h Λ η = pairDifferentialMk h Λ (1 ⊗ₜ[R] η, 0) := rfl

/-- The class representing the original root differential. -/
def pairRootDifferential : pairDifferentialPresentation h Λ :=
  pairDifferentialMk h Λ (0, 1)

omit [Algebra Λ S] [IsScalarTower Λ R S] in
/-- A scalar-extended coefficient form is its original coefficient class times the scalar. -/
theorem pairDifferentialMk_tmul (s : S) (η : KaehlerDifferential Λ R) :
    pairDifferentialMk h Λ (s ⊗ₜ[R] η, 0) = s • pairBaseDifferential h Λ η := by
  rw [pairBaseDifferential_apply, ← map_smul]
  congr 1
  simp [TensorProduct.smul_tmul']

omit [Algebra Λ S] [IsScalarTower Λ R S] in
/-- The relation is zero in the original quotient presentation. -/
theorem pairDifferential_relation :
    h.root • pairBaseDifferential h Λ (KaehlerDifferential.D Λ R x) -
        pairBaseDifferential h Λ (KaehlerDifferential.D Λ R y) +
        algebraMap R S x • pairRootDifferential h Λ = 0 := by
  have hz : pairDifferentialMk h Λ (pairDifferentialRelation h Λ) = 0 := by
    apply (Submodule.Quotient.mk_eq_zero _).mpr
    exact Submodule.subset_span (Set.mem_singleton _)
  calc
    _ = pairDifferentialMk h Λ (pairDifferentialRelation h Λ) := by
      rw [← pairDifferentialMk_tmul, pairBaseDifferential_apply,
        pairRootDifferential, ← map_sub, ← map_smul, ← map_add]
      congr 1
      simp [pairDifferentialRelation, Algebra.smul_def]
    _ = 0 := hz

/-- The derivation to the presentation is defined on the original quotient algebra. -/
def pairPresentationDerivation : Derivation Λ S (pairDifferentialPresentation h Λ) :=
  pairLiftDerivation h Λ
    ((pairBaseDifferential h Λ).compDer (KaehlerDifferential.D Λ R))
    (pairRootDifferential h Λ) (pairDifferential_relation h Λ)

@[simp]
theorem pairPresentationDerivation_base (r : R) :
    pairPresentationDerivation h Λ (algebraMap R S r) =
      pairBaseDifferential h Λ (KaehlerDifferential.D Λ R r) := by
  exact pairLiftDerivation_base h Λ
    ((pairBaseDifferential h Λ).compDer (KaehlerDifferential.D Λ R))
    (pairRootDifferential h Λ) (pairDifferential_relation h Λ) r

@[simp]
theorem pairPresentationDerivation_root :
    pairPresentationDerivation h Λ h.root = pairRootDifferential h Λ := by
  exact pairLiftDerivation_root h Λ
    ((pairBaseDifferential h Λ).compDer (KaehlerDifferential.D Λ R))
    (pairRootDifferential h Λ) (pairDifferential_relation h Λ)

/-- The forward map is the Kähler lift of the actual presentation derivation. -/
def pairDifferentialToPresentation : KaehlerDifferential Λ S →ₗ[S]
    pairDifferentialPresentation h Λ :=
  (pairPresentationDerivation h Λ).liftKaehlerDifferential

@[simp]
theorem pairDifferentialToPresentation_D (s : S) :
    pairDifferentialToPresentation h Λ (KaehlerDifferential.D Λ S s) =
      pairPresentationDerivation h Λ s :=
  Derivation.liftKaehlerDifferential_comp_D _ _

/-- The original base-change map and root differential evaluate a presentation representative. -/
def pairDifferentialFromAmbient : pairDifferentialAmbient (R := R) (S := S) Λ →ₗ[S]
    KaehlerDifferential Λ S :=
  (KaehlerDifferential.mapBaseChange Λ R S).coprod
    (LinearMap.toSpanSingleton S (KaehlerDifferential Λ S)
      (KaehlerDifferential.D Λ S h.root))

/-- Evaluation in genuine Kähler differentials kills the original relation. -/
theorem pairDifferentialFromAmbient_relation :
    pairDifferentialFromAmbient h Λ (pairDifferentialRelation h Λ) = 0 := by
  have hr : algebraMap R S x * h.root = algebraMap R S y := by
    have hz := h.aeval_root_self
    simpa only [Localization.Away.pairPolynomial, aeval_sub, aeval_mul,
      aeval_C, aeval_X, sub_eq_zero] using hz
  have hd := congrArg (KaehlerDifferential.D Λ S) hr
  simp only [Derivation.leibniz] at hd
  simp only [pairDifferentialFromAmbient, pairDifferentialRelation,
    LinearMap.coprod_apply, map_sub, KaehlerDifferential.mapBaseChange_tmul,
    KaehlerDifferential.map_D, one_smul, LinearMap.toSpanSingleton_apply]
  calc
    _ = (algebraMap R S x • KaehlerDifferential.D Λ S h.root +
        h.root • KaehlerDifferential.D Λ S (algebraMap R S x)) -
        KaehlerDifferential.D Λ S (algebraMap R S y) := by abel
    _ = 0 := sub_eq_zero.mpr hd

/-- The inverse candidate sends the presentation to the actual differential module. -/
def pairDifferentialFromPresentation : pairDifferentialPresentation h Λ →ₗ[S]
    KaehlerDifferential Λ S :=
  Submodule.liftQSpanSingleton (pairDifferentialRelation h Λ)
    (pairDifferentialFromAmbient h Λ) (pairDifferentialFromAmbient_relation h Λ)

@[simp]
theorem pairDifferentialFromPresentation_mk
    (z : pairDifferentialAmbient (R := R) (S := S) Λ) :
    pairDifferentialFromPresentation h Λ (pairDifferentialMk h Λ z) =
      KaehlerDifferential.mapBaseChange Λ R S z.1 +
        z.2 • KaehlerDifferential.D Λ S h.root := rfl

theorem pairDifferentialFromPresentation_base (η : KaehlerDifferential Λ R) :
    pairDifferentialFromPresentation h Λ (pairBaseDifferential h Λ η) =
      KaehlerDifferential.map Λ Λ R S η := by
  simp

@[simp]
theorem pairDifferentialFromPresentation_root :
    pairDifferentialFromPresentation h Λ (pairRootDifferential h Λ) =
      KaehlerDifferential.D Λ S h.root := by
  simp [pairRootDifferential]

/-- Linear maps from the presentation are fixed by coefficient differentials and `dT`. -/
theorem pairDifferentialPresentation_hom_ext
    {N : Type*} [AddCommGroup N] [Module S N]
    (f g : pairDifferentialPresentation h Λ →ₗ[S] N)
    (hR : ∀ r : R, f (pairBaseDifferential h Λ (KaehlerDifferential.D Λ R r)) =
      g (pairBaseDifferential h Λ (KaehlerDifferential.D Λ R r)))
    (hT : f (pairRootDifferential h Λ) = g (pairRootDifferential h Λ)) : f = g := by
  let : Module R N := Module.compHom N (algebraMap R S)
  let : Module Λ N := Module.compHom N (algebraMap Λ S)
  have : IsScalarTower R S N := IsScalarTower.of_algebraMap_smul fun _ _ => rfl
  have : IsScalarTower Λ S N := IsScalarTower.of_algebraMap_smul fun _ _ => rfl
  have : IsScalarTower Λ R N := IsScalarTower.of_algebraMap_smul fun a n => by
    change algebraMap R S (algebraMap Λ R a) • n = algebraMap Λ S a • n
    rw [← IsScalarTower.algebraMap_apply Λ R S]
  have he : (f.restrictScalars R).comp (pairBaseDifferential h Λ) =
      (g.restrictScalars R).comp (pairBaseDifferential h Λ) := by
    apply Derivation.liftKaehlerDifferential_unique
    apply Derivation.ext
    exact hR
  apply Submodule.linearMap_qext
  apply LinearMap.prod_ext
  · apply TensorProduct.AlgebraTensorModule.ext
    intro s η
    change f (pairDifferentialMk h Λ (s ⊗ₜ[R] η, 0)) =
      g (pairDifferentialMk h Λ (s ⊗ₜ[R] η, 0))
    simp only [pairDifferentialMk_tmul, map_smul]
    exact congrArg (s • ·) (LinearMap.congr_fun he η)
  · apply LinearMap.ext
    intro s
    change f (pairDifferentialMk h Λ (0, s)) = g (pairDifferentialMk h Λ (0, s))
    have hm : pairDifferentialMk h Λ (0, s) = s • pairRootDifferential h Λ := by
      rw [pairRootDifferential, ← map_smul]
      congr 1
      simp
    rw [hm]
    simpa only [map_smul] using congrArg (s • ·) hT

/-- The presentation maps compose to the identity on the original Kähler module. -/
theorem pairDifferentialFromTo :
    (pairDifferentialFromPresentation h Λ).comp (pairDifferentialToPresentation h Λ) =
      LinearMap.id := by
  apply Derivation.liftKaehlerDifferential_unique
  apply pair_derivation_ext h Λ
  · intro r
    simp
  · simp

/-- The presentation maps compose to the identity on the original quotient module. -/
theorem pairDifferentialToFrom :
    (pairDifferentialToPresentation h Λ).comp (pairDifferentialFromPresentation h Λ) =
      LinearMap.id := by
  apply pairDifferentialPresentation_hom_ext h Λ
  · intro r
    simp
  · simp

/-- The genuine Kähler module of the original algebra is the one-relation presentation. -/
def pairDifferentialEquiv : KaehlerDifferential Λ S ≃ₗ[S]
    pairDifferentialPresentation h Λ where
  __ := pairDifferentialToPresentation h Λ
  invFun := pairDifferentialFromPresentation h Λ
  left_inv z := LinearMap.congr_fun (pairDifferentialFromTo h Λ) z
  right_inv z := LinearMap.congr_fun (pairDifferentialToFrom h Λ) z

@[simp]
theorem pairDifferentialEquiv_D_base (r : R) :
    pairDifferentialEquiv h Λ (KaehlerDifferential.D Λ S (algebraMap R S r)) =
      pairDifferentialMk h Λ (1 ⊗ₜ[R] KaehlerDifferential.D Λ R r, 0) := by
  change pairDifferentialToPresentation h Λ _ = _
  simp

@[simp]
theorem pairDifferentialEquiv_D_root :
    pairDifferentialEquiv h Λ (KaehlerDifferential.D Λ S h.root) =
      pairDifferentialMk h Λ (0, 1) := by
  change pairDifferentialToPresentation h Λ _ = _
  simp [pairRootDifferential]

@[simp]
theorem pairDifferentialEquiv_symm_mk (z : pairDifferentialAmbient (R := R) (S := S) Λ) :
    (pairDifferentialEquiv h Λ).symm (pairDifferentialMk h Λ z) =
      KaehlerDifferential.mapBaseChange Λ R S z.1 +
        z.2 • KaehlerDifferential.D Λ S h.root := rfl

end Presentation

section Relative

/-- The actual exceptional equation ideal in the original chart algebra. -/
abbrev pairRelativeDifferentialIdeal : Ideal S := Ideal.span {algebraMap R S x}

/-- Projection of a relative presentation representative to its root coefficient modulo `x`. -/
def pairRelativeProjection : pairDifferentialAmbient (R := R) (S := S) R →ₗ[S]
    S ⧸ pairRelativeDifferentialIdeal (S := S) (x := x) :=
  (pairRelativeDifferentialIdeal (S := S) (x := x)).mkQ.comp
    (LinearMap.snd S (S ⊗[R] KaehlerDifferential R R) S)

/-- Modulo the exceptional equation, the root-coefficient projection kills the relation. -/
theorem pairRelativeProjection_relation :
    pairRelativeProjection (S := S) (x := x) (pairDifferentialRelation h R) = 0 := by
  apply (Submodule.Quotient.mk_eq_zero _).mpr
  exact Ideal.subset_span (Set.mem_singleton _)

/-- The root-coefficient projection descends through the original differential relation. -/
def pairRelativePresentationToQuotient : pairDifferentialPresentation h R →ₗ[S]
    S ⧸ pairRelativeDifferentialIdeal (S := S) (x := x) :=
  Submodule.liftQSpanSingleton (pairDifferentialRelation h R)
    (pairRelativeProjection (S := S) (x := x)) (pairRelativeProjection_relation h)

/-- Over the coefficient ring itself, only the exceptional equation remains in the relation. -/
theorem pairDifferentialRelation_self :
    pairDifferentialRelation h R = (0, algebraMap R S x) := by
  have hd (r : R) : KaehlerDifferential.D R R r = 0 := by
    simpa only [Algebra.algebraMap_self, RingHom.id_apply] using
      (KaehlerDifferential.D R R).map_algebraMap r
  dsimp only [pairDifferentialRelation]
  rw [hd x, hd y]
  simp

/-- A residue coefficient multiplies the class of the original root differential. -/
def pairRelativeQuotientToPresentation :
    S ⧸ pairRelativeDifferentialIdeal (S := S) (x := x) →ₗ[S]
      pairDifferentialPresentation h R :=
  Submodule.liftQSpanSingleton (algebraMap R S x)
    ((pairDifferentialMk h R).comp (LinearMap.inr S _ S)) (by
      change pairDifferentialMk h R (0, algebraMap R S x) = 0
      rw [← pairDifferentialRelation_self h]
      apply (Submodule.Quotient.mk_eq_zero _).mpr
      exact Submodule.subset_span (Set.mem_singleton _))

/-- With zero coefficient differentials, the same presentation is the quotient by `x`. -/
def pairRelativePresentationEquiv : pairDifferentialPresentation h R ≃ₗ[S]
    S ⧸ pairRelativeDifferentialIdeal (S := S) (x := x) where
  __ := pairRelativePresentationToQuotient h
  invFun := pairRelativeQuotientToPresentation h
  left_inv z := by
    let : Subsingleton (KaehlerDifferential R R) :=
      KaehlerDifferential.subsingleton_of_surjective (R := R) (S := R)
        Function.surjective_id
    obtain ⟨⟨η, s⟩, rfl⟩ := (S ∙ pairDifferentialRelation h R).mkQ_surjective z
    have hη : η = 0 := Subsingleton.elim _ _
    subst η
    rfl
  right_inv z := by
    obtain ⟨s, rfl⟩ := (pairRelativeDifferentialIdeal (S := S) (x := x)).mkQ_surjective z
    rfl

/-- Relative to the original coefficient ring, the same presentation is `S/(x) dT`. -/
def pairRelativeDifferentialEquiv : KaehlerDifferential R S ≃ₗ[S]
    S ⧸ pairRelativeDifferentialIdeal (S := S) (x := x) :=
  (pairDifferentialEquiv h R).trans (pairRelativePresentationEquiv h)

@[simp]
theorem pairRelativeDifferentialEquiv_D_root :
    pairRelativeDifferentialEquiv h (KaehlerDifferential.D R S h.root) = 1 := by
  change pairRelativePresentationEquiv h
    (pairDifferentialEquiv h R (KaehlerDifferential.D R S h.root)) = 1
  rw [pairDifferentialEquiv_D_root]
  rfl

theorem pairRelativeDifferentialEquiv_D_base (r : R) :
    pairRelativeDifferentialEquiv h (KaehlerDifferential.D R S (algebraMap R S r)) = 0 := by
  simp

@[simp]
theorem pairRelativeDifferentialEquiv_symm_mk (s : S) :
    (pairRelativeDifferentialEquiv h).symm (Ideal.Quotient.mk _ s) =
      s • KaehlerDifferential.D R S h.root := by
  change (pairDifferentialEquiv h R).symm (pairDifferentialMk h R (0, s)) = _
  simp

end Relative

end IsAdjoinRoot

namespace Localization.Away

variable {R : Type u} [CommRing R] (x y : R)

/-- The literal quotient chart carries its original polynomial presentation. -/
abbrev pairChartPresentation : IsAdjoinRoot (pairQuotient x y) (pairPolynomial x y) :=
  AdjoinRoot.isAdjoinRoot (pairPolynomial x y)

@[simp]
theorem pairChartPresentation_root :
    (pairChartPresentation x y).root = pairCoordinate x y := rfl

section RelativeBase

variable (Λ : Type w) [CommRing Λ] [Algebra Λ R]

/-- The differential presentation of the actual quotient chart over the original base. -/
abbrev pairKaehlerEquiv : KaehlerDifferential Λ (pairQuotient x y) ≃ₗ[pairQuotient x y]
    IsAdjoinRoot.pairDifferentialPresentation (pairChartPresentation x y) Λ :=
  IsAdjoinRoot.pairDifferentialEquiv (pairChartPresentation x y) Λ

@[simp]
theorem pairKaehlerEquiv_D_coordinate :
    pairKaehlerEquiv x y Λ (KaehlerDifferential.D Λ (pairQuotient x y)
      (pairCoordinate x y)) =
      IsAdjoinRoot.pairDifferentialMk (pairChartPresentation x y) Λ (0, 1) :=
  IsAdjoinRoot.pairDifferentialEquiv_D_root (pairChartPresentation x y) Λ

theorem pairKaehlerEquiv_D_base (r : R) :
    pairKaehlerEquiv x y Λ (KaehlerDifferential.D Λ (pairQuotient x y)
      (algebraMap R (pairQuotient x y) r)) =
      IsAdjoinRoot.pairDifferentialMk (pairChartPresentation x y) Λ
        (1 ⊗ₜ[R] KaehlerDifferential.D Λ R r, 0) :=
  IsAdjoinRoot.pairDifferentialEquiv_D_base (pairChartPresentation x y) Λ r

end RelativeBase

/-- The actual quotient chart's relative cotangent module is its exceptional quotient. -/
abbrev pairRelativeKaehlerEquiv :
    KaehlerDifferential R (pairQuotient x y) ≃ₗ[pairQuotient x y]
      pairQuotient x y ⧸ Ideal.span {algebraMap R (pairQuotient x y) x} :=
  IsAdjoinRoot.pairRelativeDifferentialEquiv (pairChartPresentation x y)

theorem pairRelativeKaehlerEquiv_D_coordinate :
    pairRelativeKaehlerEquiv x y
      (KaehlerDifferential.D R (pairQuotient x y) (pairCoordinate x y)) = 1 :=
  IsAdjoinRoot.pairRelativeDifferentialEquiv_D_root (pairChartPresentation x y)

theorem pairRelativeKaehlerEquiv_D_base (r : R) :
    pairRelativeKaehlerEquiv x y
      (KaehlerDifferential.D R (pairQuotient x y)
        (algebraMap R (pairQuotient x y) r)) = 0 :=
  IsAdjoinRoot.pairRelativeDifferentialEquiv_D_base (pairChartPresentation x y) r

theorem pairRelativeKaehlerEquiv_symm_mk (s : pairQuotient x y) :
    (pairRelativeKaehlerEquiv x y).symm (Ideal.Quotient.mk _ s) =
      s • KaehlerDifferential.D R (pairQuotient x y) (pairCoordinate x y) :=
  IsAdjoinRoot.pairRelativeDifferentialEquiv_symm_mk (pairChartPresentation x y) s

/-- The original reciprocal coordinate has the exact `-T⁻² dT` differential on the overlap. -/
theorem pairReciprocal_D_coordinate :
    KaehlerDifferential.D R (Localization.Away (pairCoordinate x y))
        (pairReciprocal x y (pairCoordinate y x)) =
      -(IsLocalization.Away.invSelf (S := Localization.Away (pairCoordinate x y))
          (pairCoordinate x y)) ^ 2 •
        KaehlerDifferential.D R (Localization.Away (pairCoordinate x y))
          (algebraMap (pairQuotient x y) (Localization.Away (pairCoordinate x y))
            (pairCoordinate x y)) := by
  rw [pairReciprocal_coordinate]
  have hinv :
      IsLocalization.Away.invSelf (S := Localization.Away (pairCoordinate x y))
          (pairCoordinate x y) *
        algebraMap (pairQuotient x y) (Localization.Away (pairCoordinate x y))
          (pairCoordinate x y) = 1 := by
    simpa only [mul_comm] using
      (IsLocalization.Away.mul_invSelf
        (S := Localization.Away (pairCoordinate x y)) (pairCoordinate x y))
  exact (KaehlerDifferential.D R (Localization.Away (pairCoordinate x y))).leibniz_of_mul_eq_one
    hinv

section Saturated

variable (hx : IsSMulRegular R x) (hy : IsSMulRegular (R ⧸ Ideal.span {x}) y)

/-- The presentation is transferred through the proved original saturated-chart isomorphism. -/
def saturatedPairPresentation :
    IsAdjoinRoot (saturatedChart R (Ideal.span {x, y}) x) (pairPolynomial x y) :=
  (pairChartPresentation x y).ofAlgEquiv (pairChartEquiv x y hx hy)

@[simp]
theorem saturatedPairPresentation_root :
    (saturatedPairPresentation x y hx hy).root =
      pairChartEquiv x y hx hy (pairCoordinate x y) := rfl

/-- The root of the transferred presentation is the literal fraction `y/x`. -/
theorem saturatedPairPresentation_root_coe :
    ((saturatedPairPresentation x y hx hy).root : Localization.Away x) = fraction x y :=
  pairChartEquiv_coordinate x y hx hy

variable (Λ : Type w) [CommRing Λ] [Algebra Λ R]

/-- The same genuine presentation on the actual saturated blowup algebra. -/
abbrev saturatedPairKaehlerEquiv :
    KaehlerDifferential Λ (saturatedChart R (Ideal.span {x, y}) x) ≃ₗ[
      saturatedChart R (Ideal.span {x, y}) x]
      IsAdjoinRoot.pairDifferentialPresentation (saturatedPairPresentation x y hx hy) Λ :=
  IsAdjoinRoot.pairDifferentialEquiv (saturatedPairPresentation x y hx hy) Λ

@[simp]
theorem saturatedPairKaehlerEquiv_D_coordinate :
    saturatedPairKaehlerEquiv x y hx hy Λ
      (KaehlerDifferential.D Λ (saturatedChart R (Ideal.span {x, y}) x)
        (pairChartEquiv x y hx hy (pairCoordinate x y))) =
      IsAdjoinRoot.pairDifferentialMk (saturatedPairPresentation x y hx hy) Λ (0, 1) :=
  IsAdjoinRoot.pairDifferentialEquiv_D_root (saturatedPairPresentation x y hx hy) Λ

theorem saturatedPairKaehlerEquiv_D_base (r : R) :
    saturatedPairKaehlerEquiv x y hx hy Λ
      (KaehlerDifferential.D Λ (saturatedChart R (Ideal.span {x, y}) x)
        (algebraMap R (saturatedChart R (Ideal.span {x, y}) x) r)) =
      IsAdjoinRoot.pairDifferentialMk (saturatedPairPresentation x y hx hy) Λ
        (1 ⊗ₜ[R] KaehlerDifferential.D Λ R r, 0) :=
  IsAdjoinRoot.pairDifferentialEquiv_D_base (saturatedPairPresentation x y hx hy) Λ r

/-- The exceptional quotient description on the same saturated chart. -/
abbrev saturatedPairRelativeKaehlerEquiv :
    KaehlerDifferential R (saturatedChart R (Ideal.span {x, y}) x) ≃ₗ[
      saturatedChart R (Ideal.span {x, y}) x]
      saturatedChart R (Ideal.span {x, y}) x ⧸
        Ideal.span {algebraMap R (saturatedChart R (Ideal.span {x, y}) x) x} :=
  IsAdjoinRoot.pairRelativeDifferentialEquiv (saturatedPairPresentation x y hx hy)

end Saturated

end Localization.Away
