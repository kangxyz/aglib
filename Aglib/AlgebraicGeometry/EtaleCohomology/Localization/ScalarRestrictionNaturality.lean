/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.EtaleCohomology.Localization.ScalarRestrictionComplex

/-! # Naturality of the original scalar localization sequence comparison -/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry.Scheme.EtaleCohomology

open Coefficients

universe u

variable {U Z X : Scheme.{u}} (j : U ⟶ X) [IsOpenImmersion j]
  (i : Z ⟶ X) [IsClosedImmersion i]
  {Λ Γ : Type (u + 1)} [CommRing Λ] [CommRing Γ] (φ : Λ →+* Γ)
  (hcomp : Set.range j = (Set.range i)ᶜ)

/-- The actual sequence comparison is natural in the original complex map. -/
theorem moduleLocalizationComplexScalarRestrictionIso_naturality
    {K L : CochainComplex.Plus (ModuleSheaf X Γ)} (a : K ⟶ L) :
    (moduleRestrictScalars X φ).mapCochainComplexPlus.mapShortComplex.map
        (moduleLocalizationComplexMap j Γ i hcomp a) ≫
      (moduleLocalizationComplexScalarRestrictionIso j i φ hcomp L).hom =
    (moduleLocalizationComplexScalarRestrictionIso j i φ hcomp K).hom ≫
      moduleLocalizationComplexMap j Λ i hcomp
        ((moduleRestrictScalars X φ).mapCochainComplexPlus.map a) := by
  apply ShortComplex.hom_ext
  · exact (NatIso.mapCochainComplexPlus
      (moduleLocalizationScalarRestrictionFirstNatIso j φ)).hom.naturality a
  · exact (Category.comp_id _).trans (Category.id_comp _).symm
  · exact (NatIso.mapCochainComplexPlus
      (moduleLocalizationScalarRestrictionThirdNatIso i φ)).hom.naturality a

end AlgebraicGeometry.Scheme.EtaleCohomology
