/-
Copyright (c) 2026 algebraic-geometry contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/

module

public import Aglib.RingTheory.KrullDimension.IntegralExtension
public import Mathlib.AlgebraicGeometry.Limits
public import Mathlib.AlgebraicGeometry.Morphisms.IsIso

/-!
# Stalk dimensions under integral extensions with going down

An integral ring extension with going down preserves dimensions of actual Spec stalks
at contracted primes. The finite-product version retains the supplied algebra equivalence
and each factor hypothesis. No domain, Noetherian or finite-dimensional premise is added.

## Extraction basis

Existing declarations from
`R5Lab/AlgebraicGeometry/FiniteEtale/Normalization/LocalDimension.lean`, source revision
`79307ff88f07d34fd5c3edb859f799c55e38f290`, SHA-256
`6a2e59621ddd5980c88c33794972285f67afb285c25e14ed51edf92ea74092ab`.
The source statements, binder universes, hypotheses and chosen maps are retained.
Direct Mathlib carriers/maps replace the recorded source wrappers; source-token correspondence
and those definitional substitutions are separate from native Lean validation.
-/

@[expose] public section

noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option linter.style.haveILetI false

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Opposite TopologicalSpace
open _root_.Ideal (height_eq_height_under)

namespace AlgebraicGeometry.Scheme

universe u

/-- Actual affine stalk dimensions agree under an integral extension with
going down. This uses the actual contraction, without a finiteness claim for
the localized ring map. -/
theorem ringKrullDim_stalk_Spec_eq_of_integral_of_goingDown
    (R B : Type u) [CommRing R] [CommRing B] [Algebra R B]
    [Algebra.IsIntegral R B] [Algebra.HasGoingDown R B] (x : PrimeSpectrum B) :
    ringKrullDim ((Spec (.of B)).presheaf.stalk x) =
      ringKrullDim ((Spec (.of R)).presheaf.stalk
        (Spec.map (CommRingCat.ofHom (algebraMap R B)) x)) := by
  let p := PrimeSpectrum.comap (algebraMap R B) x
  letI : Algebra B ((Spec (.of B)).presheaf.stalk x) := StructureSheaf.stalkAlgebra B x
  letI : IsLocalization.AtPrime ((Spec (.of B)).presheaf.stalk x) x.asIdeal :=
    StructureSheaf.IsLocalization.to_stalk B x
  letI : Algebra R ((Spec (.of R)).presheaf.stalk p) := StructureSheaf.stalkAlgebra R p
  letI : IsLocalization.AtPrime ((Spec (.of R)).presheaf.stalk p) p.asIdeal :=
    StructureSheaf.IsLocalization.to_stalk R p
  change ringKrullDim ((Spec (.of B)).presheaf.stalk x) =
    ringKrullDim ((Spec (.of R)).presheaf.stalk p)
  rw [IsLocalization.AtPrime.ringKrullDim_eq_height x.asIdeal,
    IsLocalization.AtPrime.ringKrullDim_eq_height p.asIdeal]
  exact congrArg (fun n : ℕ∞ => (n : WithBot ℕ∞)) (height_eq_height_under x.asIdeal)

/-- A finite product of integral going-down factors has the same actual
stalk dimension as the base at the point given by its algebra structure. -/
theorem ringKrullDim_stalk_Spec_eq_of_piEquiv
    (R B : Type u) [CommRing R] [CommRing B] [Algebra R B]
    {ι : Type u} [Finite ι] (Bᵢ : ι → Type u) [∀ i, CommRing (Bᵢ i)]
    [∀ i, Algebra R (Bᵢ i)] [∀ i, Algebra.IsIntegral R (Bᵢ i)]
    [∀ i, Algebra.HasGoingDown R (Bᵢ i)]
    (e : B ≃ₐ[R] ∀ i, Bᵢ i) (x : PrimeSpectrum B) :
    ringKrullDim ((Spec (.of B)).presheaf.stalk x) =
      ringKrullDim ((Spec (.of R)).presheaf.stalk
        (Spec.map (CommRingCat.ofHom (algebraMap R B)) x)) := by
  let φ : Spec (.of (∀ i, Bᵢ i)) ⟶ Spec (.of B) :=
    Spec.map (CommRingCat.ofHom e.toRingHom)
  haveI : IsIso φ := isIso_SpecMap_iff.mpr e.bijective
  obtain ⟨z, rfl⟩ := φ.surjective x
  obtain ⟨i, p, hp⟩ := PrimeSpectrum.exists_comap_evalRingHom_eq z
  rw [← hp]
  let ψ : Spec (.of (Bᵢ i)) ⟶ Spec (.of B) :=
    Spec.map (CommRingCat.ofHom (Pi.evalRingHom Bᵢ i)) ≫ φ
  haveI : IsOpenImmersion ψ := by dsimp [ψ]; infer_instance
  have hψ : ψ ≫ Spec.map (CommRingCat.ofHom (algebraMap R B)) =
      Spec.map (CommRingCat.ofHom (algebraMap R (Bᵢ i))) := by
    dsimp [ψ, φ]
    rw [Category.assoc, ← Spec.map_comp, ← Spec.map_comp]
    congr 1
    ext r
    exact congrFun (e.commutes r) i
  change ringKrullDim ((Spec (.of B)).presheaf.stalk (ψ p)) = _
  let ρ := (asIso (ψ.stalkMap p)).commRingCatIsoToRingEquiv
  calc
    ringKrullDim ((Spec (.of B)).presheaf.stalk (ψ p)) =
        ringKrullDim ((Spec (.of (Bᵢ i))).presheaf.stalk p) := ρ.ringKrullDim
    _ = _ := ?_
  have hpbase : Spec.map (CommRingCat.ofHom (algebraMap R B)) (ψ p) =
      Spec.map (CommRingCat.ofHom (algebraMap R (Bᵢ i))) p := by
    simpa only [Scheme.Hom.comp_apply] using congrArg (fun f => f p) hψ
  change ringKrullDim ((Spec (.of (Bᵢ i))).presheaf.stalk p) =
    ringKrullDim ((Spec (.of R)).presheaf.stalk
      (Spec.map (CommRingCat.ofHom (algebraMap R B)) (ψ p)))
  rw [hpbase]
  exact ringKrullDim_stalk_Spec_eq_of_integral_of_goingDown R (Bᵢ i) p

end AlgebraicGeometry.Scheme
