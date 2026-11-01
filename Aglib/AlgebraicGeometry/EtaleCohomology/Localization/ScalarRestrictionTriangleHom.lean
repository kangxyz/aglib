/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.EtaleCohomology.Localization.ScalarRestrictionTriangle

/-! # The whole morphism of the original scalar localization triangle comparison -/

@[expose] public noncomputable section

open CategoryTheory

namespace AlgebraicGeometry.Scheme.EtaleCohomology

open Coefficients

universe u wΓ wΛ

variable {U Z X : Scheme.{u}} (j : U ⟶ X) [IsOpenImmersion j]
  (i : Z ⟶ X) [IsClosedImmersion i]
  {Λ Γ : Type (u + 1)} [CommRing Λ] [CommRing Γ] (φ : Λ →+* Γ)
  (hcomp : Set.range j = (Set.range i)ᶜ)
  [HasDerivedCategory.{wΓ} (ModuleSheaf X Γ)]
  [HasDerivedCategory.{wΛ} (ModuleSheaf X Λ)]

/-- The accepted original triangle comparison has this exact whole morphism. -/
theorem moduleLocalizationComplexTriangleScalarRestrictionIso_hom
    (K : CochainComplex.Plus (ModuleSheaf X Γ)) :
    (moduleLocalizationComplexTriangleScalarRestrictionIso j i φ hcomp K).hom =
      (DerivedCategory.Plus.mapTriangleOfSESPlusIso (moduleRestrictScalars X φ)
        (moduleLocalizationComplex_shortExact j Γ i hcomp K)).hom ≫
      DerivedCategory.Plus.triangleOfSESPlusMap
        (DerivedCategory.Plus.map_triangleOfSESPlus_shortExact (moduleRestrictScalars X φ)
          (moduleLocalizationComplex_shortExact j Γ i hcomp K))
        (moduleLocalizationComplex_shortExact j Λ i hcomp
          ((moduleRestrictScalars X φ).mapCochainComplexPlus.obj K))
        (moduleLocalizationComplexScalarRestrictionIso j i φ hcomp K).hom := rfl

end AlgebraicGeometry.Scheme.EtaleCohomology
