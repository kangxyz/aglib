/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.EtaleCohomology.Localization.ScalarRestrictionComplex
public import Aglib.AlgebraicGeometry.EtaleCohomology.Exceptional.Open.ModuleScalarRestrictionDerived
public import Aglib.Algebra.Homology.DerivedCategory.Plus.ShortExactMap

/-! # Scalar restriction of actual bounded-below localization triangles -/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits CategoryTheory.Pretriangulated

namespace AlgebraicGeometry.Scheme.EtaleCohomology

open Coefficients

universe u wΓ wΛ

variable {U Z X : Scheme.{u}} (j : U ⟶ X) [IsOpenImmersion j]
  (i : Z ⟶ X) [IsClosedImmersion i]
  {Λ Γ : Type (u + 1)} [CommRing Λ] [CommRing Γ] (φ : Λ →+* Γ)
  (hcomp : Set.range j = (Set.range i)ᶜ)
  [HasDerivedCategory.{wΓ} (ModuleSheaf X Γ)]
  [HasDerivedCategory.{wΛ} (ModuleSheaf X Λ)]

/-- Restriction of scalars preserves the actual localization D+ triangle of a
bounded-below complex, including its original cone connecting arrow. -/
def moduleLocalizationComplexTriangleScalarRestrictionIso
    (K : CochainComplex.Plus (ModuleSheaf X Γ)) :
    (moduleDerivedRestrictScalars X φ).mapTriangle.obj
        (moduleLocalizationComplexTriangle j Γ i hcomp K) ≅
      moduleLocalizationComplexTriangle j Λ i hcomp
        ((moduleRestrictScalars X φ).mapCochainComplexPlus.obj K) := by
  let hΓ := moduleLocalizationComplex_shortExact j Γ i hcomp K
  let hΛ := moduleLocalizationComplex_shortExact j Λ i hcomp
    ((moduleRestrictScalars X φ).mapCochainComplexPlus.obj K)
  let hR := DerivedCategory.Plus.map_triangleOfSESPlus_shortExact
    (moduleRestrictScalars X φ) hΓ
  let e := moduleLocalizationComplexScalarRestrictionIso j i φ hcomp K
  let f := DerivedCategory.Plus.triangleOfSESPlusMap hR hΛ e.hom
  letI hf : IsIso f := by
    apply Triangle.isIso_of_isIsos
    · change IsIso (DerivedCategory.Plus.triangleOfSESPlusMap hR hΛ e.hom).hom₁
      rw [DerivedCategory.Plus.triangleOfSESPlusMap_hom₁]
      change IsIso (DerivedCategory.Plus.Q.map ((ShortComplex.π₁).mapIso e).hom)
      infer_instance
    · change IsIso (DerivedCategory.Plus.triangleOfSESPlusMap hR hΛ e.hom).hom₂
      rw [DerivedCategory.Plus.triangleOfSESPlusMap_hom₂]
      change IsIso (DerivedCategory.Plus.Q.map ((ShortComplex.π₂).mapIso e).hom)
      infer_instance
    · change IsIso (DerivedCategory.Plus.triangleOfSESPlusMap hR hΛ e.hom).hom₃
      rw [DerivedCategory.Plus.triangleOfSESPlusMap_hom₃]
      change IsIso (DerivedCategory.Plus.Q.map ((ShortComplex.π₃).mapIso e).hom)
      infer_instance
  let ef := @asIso _ _ _ _ f hf
  exact DerivedCategory.Plus.mapTriangleOfSESPlusIso (moduleRestrictScalars X φ) hΓ ≪≫ ef

end AlgebraicGeometry.Scheme.EtaleCohomology
