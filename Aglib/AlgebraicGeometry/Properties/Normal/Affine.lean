/-
Copyright (c) 2026 algebraic-geometry contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/

module

public import Mathlib.AlgebraicGeometry.FunctionField
public import Mathlib.AlgebraicGeometry.Limits
public import Mathlib.AlgebraicGeometry.Morphisms.IsIso
public import Mathlib.RingTheory.LocalProperties.IntegrallyClosed

/-!
# Affine sections and stalks of normal integral schemes

Normality of actual stalks yields integral closedness of nonempty affine sections without a
Noetherian hypothesis. Normal-domain Spec stalks and finite-product Spec stalks use canonical
localizations and actual factor open immersions; no nonempty product is assumed.

## Extraction basis

Existing declarations from
`R5Lab/AlgebraicGeometry/FiniteEtale/Normalization/GenericFullFaithfulness.lean`, source revision
`79307ff88f07d34fd5c3edb859f799c55e38f290`, SHA-256
`56316f6517043fcd7e709e55d04765986ce74140b7d0d4e98e59a4648ec25c47`.
Existing declarations from
`R5Lab/AlgebraicGeometry/FiniteEtale/Normalization/NormalStalks.lean`, source revision
`79307ff88f07d34fd5c3edb859f799c55e38f290`, SHA-256
`a419e35892f4760d1613685421bc25ce81ec13caca35a645dc1b8c91aa05c9f3`.
The source statements, binder universes, hypotheses and chosen maps are retained.
Direct Mathlib carriers/maps replace the recorded source wrappers; source-token correspondence
and those definitional substitutions are separate from native Lean validation.
-/

@[expose] public section

noncomputable section
set_option autoImplicit false
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option linter.style.haveILetI false

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Opposite TopologicalSpace

namespace AlgebraicGeometry.Scheme

universe u

variable (X : Scheme.{u}) [IsIntegral X]
  [∀ x : X, IsIntegrallyClosed (X.presheaf.stalk x)]

/-- Normality of the actual local rings gives normality of a nonempty affine
section ring. No Noetherianity is assumed. -/
theorem isIntegrallyClosed_sections_of_isAffineOpen (U : X.Opens) (hU : IsAffineOpen U)
    [Nonempty U] : IsIntegrallyClosed Γ(X, U) := by
  let (p : PrimeSpectrum Γ(X, U)) : Algebra Γ(X, U) (X.presheaf.stalk (hU.fromSpec p)) :=
    TopCat.Presheaf.algebra_section_stalk X.presheaf _
  have (P : Ideal Γ(X, U)) [hP : P.IsPrime] :
      IsLocalization.AtPrime (X.presheaf.stalk (hU.fromSpec ⟨P, hP⟩)) P :=
    hU.isLocalization_stalk' ⟨P, hP⟩ (hU.isoSpec.inv _).2
  exact IsIntegrallyClosed.of_isLocalization_maximal
    (fun (P : Ideal Γ(X, U)) [hP : P.IsMaximal] =>
      X.presheaf.stalk (hU.fromSpec ⟨P, hP.isPrime⟩)) (fun _ => inferInstance)

/-- Actual affine scheme stalks of a normal domain are normal domains,
using their canonical localizations at the actual primes. -/
theorem isIntegrallyClosed_and_isDomain_stalk_Spec (B : Type u) [CommRing B] [IsDomain B]
    [IsIntegrallyClosed B]
    (x : PrimeSpectrum B) :
    IsIntegrallyClosed ((Spec (.of B)).presheaf.stalk x) ∧
      IsDomain ((Spec (.of B)).presheaf.stalk x) := by
  letI : Algebra B ((Spec (.of B)).presheaf.stalk x) := StructureSheaf.stalkAlgebra B x
  have hl : IsLocalization.AtPrime ((Spec (.of B)).presheaf.stalk x) x.asIdeal :=
    StructureSheaf.IsLocalization.to_stalk B x
  letI : IsLocalization x.asIdeal.primeCompl ((Spec (.of B)).presheaf.stalk x) := hl
  refine ⟨?_, inferInstance⟩
  exact isIntegrallyClosed_of_isLocalization ((Spec (.of B)).presheaf.stalk x)
    x.asIdeal.primeCompl x.asIdeal.primeCompl_le_nonZeroDivisors

/-- A finite product of normal domains has normal domain scheme stalks.
Every actual prime is in an actual factor open immersion. No nonempty-index
hypothesis is used, so the empty product/empty spectrum is preserved. -/
theorem isIntegrallyClosed_and_isDomain_stalk_Spec_of_piEquiv (B : Type u) [CommRing B]
    {ι : Type u} [Finite ι] (Bᵢ : ι → Type u) [∀ i, CommRing (Bᵢ i)]
    [∀ i, IsDomain (Bᵢ i)] [∀ i, IsIntegrallyClosed (Bᵢ i)]
    (e : B ≃+* ∀ i, Bᵢ i) (x : PrimeSpectrum B) :
    IsIntegrallyClosed ((Spec (.of B)).presheaf.stalk x) ∧
      IsDomain ((Spec (.of B)).presheaf.stalk x) := by
  let φ : Spec (.of (∀ i, Bᵢ i)) ⟶ Spec (.of B) := Spec.map (CommRingCat.ofHom e.toRingHom)
  haveI : IsIso φ := isIso_SpecMap_iff.mpr e.bijective
  obtain ⟨z, rfl⟩ := φ.surjective x
  obtain ⟨i, p, hp⟩ := PrimeSpectrum.exists_comap_evalRingHom_eq z
  rw [← hp]
  let ψ : Spec (.of (Bᵢ i)) ⟶ Spec (.of B) :=
    Spec.map (CommRingCat.ofHom (Pi.evalRingHom Bᵢ i)) ≫ φ
  haveI : IsOpenImmersion ψ := by dsimp [ψ]; infer_instance
  haveI : IsIntegrallyClosed ((Spec (.of (Bᵢ i))).presheaf.stalk p) :=
    (isIntegrallyClosed_and_isDomain_stalk_Spec (Bᵢ i) p).1
  haveI : IsDomain ((Spec (.of (Bᵢ i))).presheaf.stalk p) :=
    (isIntegrallyClosed_and_isDomain_stalk_Spec (Bᵢ i) p).2
  change IsIntegrallyClosed ((Spec (.of B)).presheaf.stalk (ψ p)) ∧
    IsDomain ((Spec (.of B)).presheaf.stalk (ψ p))
  let ρ := (asIso (ψ.stalkMap p)).symm.commRingCatIsoToRingEquiv
  exact ⟨IsIntegrallyClosed.of_equiv ρ, ρ.symm.toMulEquiv.isDomain _⟩

end AlgebraicGeometry.Scheme
