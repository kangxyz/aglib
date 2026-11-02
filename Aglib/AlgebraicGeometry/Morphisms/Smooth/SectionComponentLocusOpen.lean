/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.Morphisms.Smooth.SectionComponentLocusConstructible
public import Aglib.AlgebraicGeometry.Morphisms.Smooth.SectionComponentLocusGenerization
public import Aglib.AlgebraicGeometry.Properties.ConstructibleOpen

/-! # The original section-component locus over a Noetherian affine base

The genuine constructibility and arbitrary-point generization arguments imply
openness through the original scheme affine-cover criterion. Noetherianity
of the original source also supplies retrocompactness. Arbitrary-base descent
and prescribed-point etale factorization are separate consumers.
-/

@[expose] public noncomputable section
open CategoryTheory

namespace AlgebraicGeometry.Scheme
universe u

/-- The original locus is open and retrocompact under the original
Noetherian affine-base smooth-family hypotheses. -/
theorem sectionComponentLocus_isOpen_isRetrocompact
    (R : Type u) [CommRing R] [IsNoetherianRing R]
    {X : Scheme.{u}} (f : X ⟶ Spec (.of R)) (n : ℕ)
    [SmoothOfRelativeDimension n f] [QuasiCompact f] [QuasiSeparated f]
    (σ : Spec (.of R) ⟶ X) (hσ : σ ≫ f = 𝟙 _) :
    IsOpen (sectionComponentLocus f σ hσ) ∧
      IsRetrocompact (sectionComponentLocus f σ hσ) := by
  let : Smooth f := SmoothOfRelativeDimension.smooth n f
  refine ⟨isOpen_of_isConstructible_of_stableUnderGeneralization
    (isConstructible_sectionComponentLocus R f n σ hσ)
    (sectionComponentLocus_stableUnderGeneralization f σ hσ), ?_⟩
  let : IsLocallyNoetherian X := LocallyOfFiniteType.isLocallyNoetherian f
  let : CompactSpace X := QuasiCompact.compactSpace_of_compactSpace f
  let : IsNoetherian X :=
    { toIsLocallyNoetherian := inferInstance, toCompactSpace := inferInstance }
  intro U _ _
  exact TopologicalSpace.NoetherianSpace.isCompact _

end AlgebraicGeometry.Scheme
