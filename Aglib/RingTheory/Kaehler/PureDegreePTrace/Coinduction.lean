/-
Copyright (c) 2026 kangxyz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.RingTheory.Kaehler.PureDegreePTrace.IntegralClosure
public import Mathlib.Algebra.Category.ModuleCat.ChangeOfRings
public import Mathlib.LinearAlgebra.Dual.Lemmas

/-!
# The actual integral differential transpose in native coinduction

The forward map is the existing integralClosureTraceTranspose. Its original
pointwise source-multiplication law proves B-linearity in native coinduction.
The original double-dual coefficient and an explicitly supplied actual
coefficient isomorphism remain visible. No ordinary field trace is used.
-/

@[expose] public noncomputable section

open CategoryTheory Polynomial

universe u v w

namespace ModuleCat

/-- An original algebra-linear functional on B, read on the literal restricted
regular B-module. The scalar equation uses the original algebra map. -/
def originalFunctionalOnRestriction
    (A : Type u) (B : Type v) [CommRing A] [CommRing B] [Algebra A B]
    (W : ModuleCat.{w} A) (f : B →ₗ[A] W) :
    (restrictScalars (algebraMap A B)).obj (ModuleCat.of B B) →ₗ[A] W where
  toFun := f
  map_add' := f.map_add
  map_smul' := fun a (b : B) => by
    change f ((algebraMap A B a) * b) = a • f b
    simpa only [Algebra.smul_def] using f.map_smul a b

end ModuleCat

namespace KaehlerDifferential

variable (Λ A : Type u) (K : Type v) (L : Type w)
    [CommRing Λ] [CommRing A] [Field K] [Algebra A K]
    [Field L] [Algebra K L] [Algebra A L] [IsScalarTower A K L]
    [Algebra Λ A] [Algebra Λ K] [Algebra Λ L]
    [IsScalarTower Λ K L] [IsScalarTower Λ A L]
    [IsDomain A] [IsNoetherianRing A] [IsIntegrallyClosed A]
    [IsFractionRing A K] [IsScalarTower Λ A K]
    [FiniteDimensional K L] [IsPurelyInseparable K L]
    [Module.Finite A (integralClosure A L)]
    {p : ℕ} [CharP K p] [Fact p.Prime] {a : K}
    (n : ℕ) [Module.Finite A (⋀[A]^(n + 1) (KaehlerDifferential Λ A))]

local notation "B" => integralClosure A L
local notation "M" => (⋀[A]^(n + 1) (KaehlerDifferential Λ A))
local notation "N" => (⋀[B]^(n + 1) (KaehlerDifferential Λ B))
local notation "W" => Module.Dual A (Module.Dual A M)

local instance coinductionBaseFinitePresentation : Module.FinitePresentation A M :=
  Module.finitePresentation_of_finite A M

local instance coinductionBaseLocalized :
    IsLocalizedModule (nonZeroDivisors A) (mapExterior Λ A K (n + 1)) :=
  mapExterior_isLocalizedModule Λ A K (nonZeroDivisors A) (n + 1)

/-- The actual c_B, now B-linear into the literal native coinduced coefficient. -/
def integralClosureTraceCoinduced
    (hdegree : Module.finrank K L = p)
    (h : IsAdjoinRootMonic L ((X : K[X]) ^ p - C a)) :
    N →ₗ[B] (ModuleCat.coextendScalars (algebraMap A B)).obj (ModuleCat.of A W) := by
  let T := integralClosureTraceTranspose Λ A K L n hdegree h
  let E := ModuleCat.CoextendScalars.equiv (algebraMap A B) (ModuleCat.of A W)
  exact {
    toFun := fun ω => E.symm (ModuleCat.originalFunctionalOnRestriction A B (ModuleCat.of A W)
      (T ω))
    map_add' := fun ω η => by
      apply E.injective
      simp only [map_add, LinearEquiv.apply_symm_apply]
      refine LinearMap.ext fun (b : B) => ?_
      rfl
    map_smul' := fun b ω => by
      apply E.injective
      simp only [map_smul, LinearEquiv.apply_symm_apply]
      refine LinearMap.ext fun (c : B) => ?_
      change T (b • ω) c = T ω (c * b)
      exact integralClosureTraceTranspose_smul_apply Λ A K L n hdegree h ω b c }

/-- Native evaluation is exactly the original differential transpose value. -/
theorem integralClosureTraceCoinduced_evaluation
    (hdegree : Module.finrank K L = p)
    (h : IsAdjoinRootMonic L ((X : K[X]) ^ p - C a)) (ω : N) (b : B) :
    ModuleCat.CoextendScalars.equiv (algebraMap A B) (ModuleCat.of A W)
        (integralClosureTraceCoinduced Λ A K L n hdegree h ω) b =
      integralClosureTraceTranspose Λ A K L n hdegree h ω b := by
  rfl

/-- The original double-dual generic embedding still gives the actual differential trace. -/
theorem integralClosureTraceCoinduced_generic
    (hdegree : Module.finrank K L = p)
    (h : IsAdjoinRootMonic L ((X : K[X]) ^ p - C a)) (ω : N) (b : B) :
    let := finiteExteriorAtFraction Λ A K n;
    Module.Dual.doubleDualToFraction (K := K) (mapExterior Λ A K (n + 1))
        (ModuleCat.CoextendScalars.equiv (algebraMap A B) (ModuleCat.of A W)
          (integralClosureTraceCoinduced Λ A K L n hdegree h ω) b) =
      pureDegreePTraceExterior (Λ := Λ) h n
        (mapExterior Λ B L (n + 1) (b • ω)) := by
  let := finiteExteriorAtFraction Λ A K n
  rw [integralClosureTraceCoinduced_evaluation]
  exact integralClosureTraceTranspose_generic Λ A K L n hdegree h ω b

/-- Normalize by the actual raw rank-one basis followed by bidual evaluation.
The coefficient map is A-linear; coextension supplies its B-linear image. -/
def integralClosureTraceCoinducedOfBasis
    (hdegree : Module.finrank K L = p)
    (h : IsAdjoinRootMonic L ((X : K[X]) ^ p - C a))
    (Θ : A ≃ₗ[A] M) :
    N →ₗ[B] (ModuleCat.coextendScalars (algebraMap A B)).obj (ModuleCat.of A A) := by
  let : Module.IsReflexive A M := Module.equiv Θ
  let θ : ModuleCat.of A A ≅ ModuleCat.of A W :=
    (Θ.trans (Module.evalEquiv A M)).toModuleIso
  exact ((ModuleCat.coextendScalars (algebraMap A B)).map θ.inv).hom.comp
    (integralClosureTraceCoinduced Λ A K L n hdegree h)

/-- Normalized evaluation recovers the same raw basis and original bidual evaluation. -/
theorem integralClosureTraceCoinducedOfBasis_evaluation
    (hdegree : Module.finrank K L = p)
    (h : IsAdjoinRootMonic L ((X : K[X]) ^ p - C a))
    (Θ : A ≃ₗ[A] M) (ω : N) (b : B) :
    Module.Dual.eval A M
      (Θ (ModuleCat.CoextendScalars.equiv (algebraMap A B) (ModuleCat.of A A)
        (integralClosureTraceCoinducedOfBasis Λ A K L n hdegree h Θ ω) b)) =
      integralClosureTraceTranspose Λ A K L n hdegree h ω b := by
  let : Module.IsReflexive A M := Module.equiv Θ
  let θ : ModuleCat.of A A ≅ ModuleCat.of A W :=
    (Θ.trans (Module.evalEquiv A M)).toModuleIso
  have hval := ModuleCat.CoextendScalars.map_apply (algebraMap A B) θ.inv
    (integralClosureTraceCoinduced Λ A K L n hdegree h ω) b
  change θ.hom
      (ModuleCat.CoextendScalars.equiv (algebraMap A B) (ModuleCat.of A A)
        (((ModuleCat.coextendScalars (algebraMap A B)).map θ.inv)
          (integralClosureTraceCoinduced Λ A K L n hdegree h ω)) b) = _
  rw [hval, integralClosureTraceCoinduced_evaluation]
  exact ConcreteCategory.congr_hom θ.inv_hom_id
    (integralClosureTraceTranspose Λ A K L n hdegree h ω b)

/-- The same original base scalar carries every normalized coinduced coefficient
into the image. Native coinduction uses right multiplication on the original
normalization; no action of that ring on the base coefficient is introduced. -/
theorem integralClosureTraceCoinducedOfBasis_smul_mem_range
    (hdegree : Module.finrank K L = p)
    (h : IsAdjoinRootMonic L ((X : K[X]) ^ p - C a))
    (Θ : A ≃ₗ[A] M) (s : A)
    (hs : ∀ ψ : B →ₗ[A] W,
      s • ψ ∈ (integralClosureTraceTranspose Λ A K L n hdegree h).range)
    (φ : (ModuleCat.coextendScalars (algebraMap A B)).obj (ModuleCat.of A A)) :
    (algebraMap A B s) • φ ∈
      (integralClosureTraceCoinducedOfBasis Λ A K L n hdegree h Θ).range := by
  let : Module.IsReflexive A M := Module.equiv Θ
  let κ : A ≃ₗ[A] W := Θ.trans (Module.evalEquiv A M)
  let E := ModuleCat.CoextendScalars.equiv (algebraMap A B) (ModuleCat.of A A)
  have hG (r : A) (b : B) :
      E φ ((algebraMap A B r) * b) = r • E φ b := by
    have hmap := (E φ).map_smul r
      (show (ModuleCat.restrictScalars (algebraMap A B)).obj (ModuleCat.of B B) from b)
    change E φ ((algebraMap A B r) * b) = r • E φ b at hmap
    exact hmap
  let F : B →ₗ[A] A := {
    toFun := fun b => E φ b
    map_add' := fun b c => (E φ).map_add b c
    map_smul' := fun r b => by simpa only [Algebra.smul_def, RingHom.id_apply] using hG r b }
  let ψ : B →ₗ[A] W := κ.toLinearMap.comp F
  obtain ⟨ω, hω⟩ := hs ψ
  refine ⟨ω, ?_⟩
  apply E.injective
  refine LinearMap.ext fun (b : B) => ?_
  apply κ.injective
  calc
    κ (E (integralClosureTraceCoinducedOfBasis Λ A K L n hdegree h Θ ω) b) =
        integralClosureTraceTranspose Λ A K L n hdegree h ω b :=
      integralClosureTraceCoinducedOfBasis_evaluation Λ A K L n hdegree h Θ ω b
    _ = s • κ (E φ b) := LinearMap.congr_fun hω b
    _ = κ (s • E φ b) := (κ.map_smul s (E φ b)).symm
    _ = κ (E φ (b * algebraMap A B s)) := by
      rw [mul_comm b (algebraMap A B s), hG s b]
    _ = κ (E ((algebraMap A B s) • φ) b) :=
      congrArg κ (ModuleCat.CoextendScalars.smul_apply (algebraMap A B)
        (ModuleCat.of A A) φ (algebraMap A B s) b).symm

end KaehlerDifferential
