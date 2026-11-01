/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module
public import Aglib.AlgebraicGeometry.EtaleCohomology.Localization.GeometricPullbackComplex
public import Aglib.AlgebraicGeometry.EtaleCohomology.Exceptional.Derived.DirectImage
public import Aglib.Algebra.Homology.DerivedCategory.Plus.ShortExactMap

/-! # Geometric inverse image preserves the original complete localization triangle -/
@[expose] public noncomputable section
open CategoryTheory CategoryTheory.Limits CategoryTheory.Pretriangulated
namespace AlgebraicGeometry.Scheme.EtaleCohomology
open Coefficients
universe u wX wX'
variable {U Z X U' Z' X' : Scheme.{u}}
  (j : U ⟶ X) (i : Z ⟶ X) (j' : U' ⟶ X') (i' : Z' ⟶ X')
  (f : X' ⟶ X) (g : U' ⟶ U) (k : Z' ⟶ Z)
  [IsOpenImmersion j] [IsOpenImmersion j'] [IsClosedImmersion i] [IsClosedImmersion i']
  (hj : IsPullback g j' j f) (hi : IsPullback k i' i f)
  (Λ : Type (u + 1)) [Ring Λ]
  (hc : Set.range j = (Set.range i)ᶜ) (hc' : Set.range j' = (Set.range i')ᶜ)
  [HasDerivedCategory.{wX} (ModuleSheaf X Λ)]
  [HasDerivedCategory.{wX'} (ModuleSheaf X' Λ)]

/-- Exact geometric inverse image preserves the actual complex localization triangle,
including the original cone connecting map, through the actual SES comparison. -/
def moduleLocalizationComplexTrianglePullbackIso
    (K : CochainComplex.Plus (ModuleSheaf X Λ)) :
    (moduleDerivedInverseImage Λ f).mapTriangle.obj
        (moduleLocalizationComplexTriangle j Λ i hc K) ≅
      moduleLocalizationComplexTriangle j' Λ i' hc'
        ((moduleInverseImage f Λ).mapCochainComplexPlus.obj K) := by
  let hS := moduleLocalizationComplex_shortExact j Λ i hc K
  let hT := moduleLocalizationComplex_shortExact j' Λ i' hc'
    ((moduleInverseImage f Λ).mapCochainComplexPlus.obj K)
  let hF := DerivedCategory.Plus.map_triangleOfSESPlus_shortExact (moduleInverseImage f Λ) hS
  let e := moduleLocalizationComplexPullbackIso j i j' i' f g k hj hi Λ hc hc' K
  let a := DerivedCategory.Plus.triangleOfSESPlusMap hF hT e.hom
  letI ha : IsIso a := by
    apply Triangle.isIso_of_isIsos
    · change IsIso (DerivedCategory.Plus.triangleOfSESPlusMap hF hT e.hom).hom₁
      rw [DerivedCategory.Plus.triangleOfSESPlusMap_hom₁]
      change IsIso (DerivedCategory.Plus.Q.map ((ShortComplex.π₁).mapIso e).hom)
      infer_instance
    · change IsIso (DerivedCategory.Plus.triangleOfSESPlusMap hF hT e.hom).hom₂
      rw [DerivedCategory.Plus.triangleOfSESPlusMap_hom₂]
      change IsIso (DerivedCategory.Plus.Q.map ((ShortComplex.π₂).mapIso e).hom)
      infer_instance
    · change IsIso (DerivedCategory.Plus.triangleOfSESPlusMap hF hT e.hom).hom₃
      rw [DerivedCategory.Plus.triangleOfSESPlusMap_hom₃]
      change IsIso (DerivedCategory.Plus.Q.map ((ShortComplex.π₃).mapIso e).hom)
      infer_instance
  exact DerivedCategory.Plus.mapTriangleOfSESPlusIso (moduleInverseImage f Λ) hS ≪≫
    @asIso _ _ _ _ a ha

/-- The complete original triangle comparison retains this whole original morphism. -/
theorem moduleLocalizationComplexTrianglePullbackIso_hom
    (K : CochainComplex.Plus (ModuleSheaf X Λ)) :
    (moduleLocalizationComplexTrianglePullbackIso j i j' i' f g k hj hi Λ hc hc' K).hom =
      (DerivedCategory.Plus.mapTriangleOfSESPlusIso (moduleInverseImage f Λ)
        (moduleLocalizationComplex_shortExact j Λ i hc K)).hom ≫
      DerivedCategory.Plus.triangleOfSESPlusMap
        (DerivedCategory.Plus.map_triangleOfSESPlus_shortExact (moduleInverseImage f Λ)
          (moduleLocalizationComplex_shortExact j Λ i hc K))
        (moduleLocalizationComplex_shortExact j' Λ i' hc'
          ((moduleInverseImage f Λ).mapCochainComplexPlus.obj K))
        (moduleLocalizationComplexPullbackIso j i j' i' f g k hj hi Λ hc hc' K).hom := rfl
end AlgebraicGeometry.Scheme.EtaleCohomology
