/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.Algebra.Homology.DerivedCategory.Plus.ShortExactMapNatural

/-! # Whole SES squares induce the original exact triangle comparison square -/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits CategoryTheory.Pretriangulated

universe u v u' v' w w'

namespace DerivedCategory.Plus

variable {C : Type u} [Category.{v} C] [Abelian C] [HasDerivedCategory.{w} C]
  [EnoughInjectives C]
  {D : Type u'} [Category.{v'} D] [Abelian D] [HasDerivedCategory.{w'} D]
  (F : C ⥤ D) [F.Additive] [PreservesFiniteLimits F] [PreservesFiniteColimits F]
  {S T : ShortComplex (CochainComplex.Plus C)}
  {S' T' : ShortComplex (CochainComplex.Plus D)}
  (hS : (S.map (CochainComplex.Plus.ι C)).ShortExact)
  (hT : (T.map (CochainComplex.Plus.ι C)).ShortExact)
  (hS' : (S'.map (CochainComplex.Plus.ι D)).ShortExact)
  (hT' : (T'.map (CochainComplex.Plus.ι D)).ShortExact)

/-- A commuting square of entire original sequences induces its entire triangle square. -/
theorem mapTriangleOfSESPlusIso_square
    (eS : S.map F.mapCochainComplexPlus ≅ S')
    (eT : T.map F.mapCochainComplexPlus ≅ T') (f : S ⟶ T) (f' : S' ⟶ T')
    (h : F.mapCochainComplexPlus.mapShortComplex.map f ≫ eT.hom = eS.hom ≫ f') :
    F.rightDerivedFunctorPlus.mapTriangle.map (triangleOfSESPlusMap hS hT f) ≫
        (mapTriangleOfSESPlusIso F hT).hom ≫
          triangleOfSESPlusMap (map_triangleOfSESPlus_shortExact F hT) hT' eT.hom =
    ((mapTriangleOfSESPlusIso F hS).hom ≫
      triangleOfSESPlusMap (map_triangleOfSESPlus_shortExact F hS) hS' eS.hom) ≫
        triangleOfSESPlusMap hS' hT' f' := by
  rw [← Category.assoc, mapTriangleOfSESPlusIso_naturality, Category.assoc, Category.assoc]
  apply congrArg (fun k => (mapTriangleOfSESPlusIso F hS).hom ≫ k)
  apply Triangle.hom_ext
  · change (triangleOfSESPlusMap _ _ _).hom₁ ≫
      (triangleOfSESPlusMap _ _ _).hom₁ =
        (triangleOfSESPlusMap _ _ _).hom₁ ≫ (triangleOfSESPlusMap _ _ _).hom₁
    simp only [triangleOfSESPlusMap_hom₁]
    exact (DerivedCategory.Plus.Q.map_comp
      (F.mapCochainComplexPlus.mapShortComplex.map f).τ₁ eT.hom.τ₁).symm.trans
        ((congrArg (fun t => DerivedCategory.Plus.Q.map t.τ₁) h).trans
          (DerivedCategory.Plus.Q.map_comp eS.hom.τ₁ f'.τ₁))
  · change (triangleOfSESPlusMap _ _ _).hom₂ ≫
      (triangleOfSESPlusMap _ _ _).hom₂ =
        (triangleOfSESPlusMap _ _ _).hom₂ ≫ (triangleOfSESPlusMap _ _ _).hom₂
    simp only [triangleOfSESPlusMap_hom₂]
    exact (DerivedCategory.Plus.Q.map_comp
      (F.mapCochainComplexPlus.mapShortComplex.map f).τ₂ eT.hom.τ₂).symm.trans
        ((congrArg (fun t => DerivedCategory.Plus.Q.map t.τ₂) h).trans
          (DerivedCategory.Plus.Q.map_comp eS.hom.τ₂ f'.τ₂))
  · change (triangleOfSESPlusMap _ _ _).hom₃ ≫
      (triangleOfSESPlusMap _ _ _).hom₃ =
        (triangleOfSESPlusMap _ _ _).hom₃ ≫ (triangleOfSESPlusMap _ _ _).hom₃
    simp only [triangleOfSESPlusMap_hom₃]
    exact (DerivedCategory.Plus.Q.map_comp
      (F.mapCochainComplexPlus.mapShortComplex.map f).τ₃ eT.hom.τ₃).symm.trans
        ((congrArg (fun t => DerivedCategory.Plus.Q.map t.τ₃) h).trans
          (DerivedCategory.Plus.Q.map_comp eS.hom.τ₃ f'.τ₃))

end DerivedCategory.Plus
