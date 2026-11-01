/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.Algebra.Homology.DerivedCategory.Plus.ShortExactMapNaturality

/-! # Naturality of the exact original SES triangle comparison -/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits CategoryTheory.Pretriangulated

universe u v u' v' w w'

namespace DerivedCategory.Plus

variable {C : Type u} [Category.{v} C] [Abelian C] [HasDerivedCategory.{w} C]
  [EnoughInjectives C]
  {D : Type u'} [Category.{v'} D] [Abelian D] [HasDerivedCategory.{w'} D]
  (F : C ⥤ D) [F.Additive] [PreservesFiniteLimits F] [PreservesFiniteColimits F]
  {S T : ShortComplex (CochainComplex.Plus C)}
  (hS : (S.map (CochainComplex.Plus.ι C)).ShortExact)
  (hT : (T.map (CochainComplex.Plus.ι C)).ShortExact)

/-- The exact comparison is natural as an entire triangle, including the third arrow. -/
theorem mapTriangleOfSESPlusIso_naturality (f : S ⟶ T) :
    F.rightDerivedFunctorPlus.mapTriangle.map (triangleOfSESPlusMap hS hT f) ≫
      (mapTriangleOfSESPlusIso F hT).hom =
    (mapTriangleOfSESPlusIso F hS).hom ≫
      triangleOfSESPlusMap (map_triangleOfSESPlus_shortExact F hS)
        (map_triangleOfSESPlus_shortExact F hT)
          (F.mapCochainComplexPlus.mapShortComplex.map f) := by
  apply Triangle.hom_ext
  · apply DerivedCategory.Plus.ι.map_injective
    change DerivedCategory.Plus.ι.map
      (F.rightDerivedFunctorPlus.map (triangleOfSESPlusMap hS hT f).hom₁ ≫
        (mapTriangleOfSESPlusIso F hT).hom.hom₁) =
      DerivedCategory.Plus.ι.map ((mapTriangleOfSESPlusIso F hS).hom.hom₁ ≫
        (triangleOfSESPlusMap (map_triangleOfSESPlus_shortExact F hS)
          (map_triangleOfSESPlus_shortExact F hT)
            (F.mapCochainComplexPlus.mapShortComplex.map f)).hom₁)
    refine (DerivedCategory.Plus.ι.map_comp _ _).trans
      (Eq.trans ?_ (DerivedCategory.Plus.ι.map_comp _ _).symm)
    simp only [triangleOfSESPlusMap_hom₁, mapTriangleOfSESPlusIso_hom₁_ι]
    change (F.rightDerivedFunctorPlus ⋙ DerivedCategory.Plus.ι).map
        (DerivedCategory.Plus.Q.map f.τ₁) ≫
      F.rightDerivedFunctorPlusCompιIso.hom.app (DerivedCategory.Plus.Q.obj T.X₁) ≫
        F.mapDerivedCategoryFactors.hom.app T.X₁.obj =
      (F.rightDerivedFunctorPlusCompιIso.hom.app (DerivedCategory.Plus.Q.obj S.X₁) ≫
        F.mapDerivedCategoryFactors.hom.app S.X₁.obj) ≫
          DerivedCategory.Q.map ((F.mapHomologicalComplex (.up ℤ)).map f.τ₁.hom)
    exact ((F.rightDerivedFunctorPlusCompιIso.hom.naturality_assoc
      (DerivedCategory.Plus.Q.map f.τ₁) _).trans
        (congrArg (fun k => F.rightDerivedFunctorPlusCompιIso.hom.app
          (DerivedCategory.Plus.Q.obj S.X₁) ≫ k)
            (F.mapDerivedCategoryFactors.hom.naturality f.τ₁.hom))).trans
              (Category.assoc _ _ _).symm
  · apply DerivedCategory.Plus.ι.map_injective
    change DerivedCategory.Plus.ι.map
      (F.rightDerivedFunctorPlus.map (triangleOfSESPlusMap hS hT f).hom₂ ≫
        (mapTriangleOfSESPlusIso F hT).hom.hom₂) =
      DerivedCategory.Plus.ι.map ((mapTriangleOfSESPlusIso F hS).hom.hom₂ ≫
        (triangleOfSESPlusMap (map_triangleOfSESPlus_shortExact F hS)
          (map_triangleOfSESPlus_shortExact F hT)
            (F.mapCochainComplexPlus.mapShortComplex.map f)).hom₂)
    refine (DerivedCategory.Plus.ι.map_comp _ _).trans
      (Eq.trans ?_ (DerivedCategory.Plus.ι.map_comp _ _).symm)
    simp only [triangleOfSESPlusMap_hom₂, mapTriangleOfSESPlusIso_hom₂_ι]
    change (F.rightDerivedFunctorPlus ⋙ DerivedCategory.Plus.ι).map
        (DerivedCategory.Plus.Q.map f.τ₂) ≫
      F.rightDerivedFunctorPlusCompιIso.hom.app (DerivedCategory.Plus.Q.obj T.X₂) ≫
        F.mapDerivedCategoryFactors.hom.app T.X₂.obj =
      (F.rightDerivedFunctorPlusCompιIso.hom.app (DerivedCategory.Plus.Q.obj S.X₂) ≫
        F.mapDerivedCategoryFactors.hom.app S.X₂.obj) ≫
          DerivedCategory.Q.map ((F.mapHomologicalComplex (.up ℤ)).map f.τ₂.hom)
    exact ((F.rightDerivedFunctorPlusCompιIso.hom.naturality_assoc
      (DerivedCategory.Plus.Q.map f.τ₂) _).trans
        (congrArg (fun k => F.rightDerivedFunctorPlusCompιIso.hom.app
          (DerivedCategory.Plus.Q.obj S.X₂) ≫ k)
            (F.mapDerivedCategoryFactors.hom.naturality f.τ₂.hom))).trans
              (Category.assoc _ _ _).symm
  · apply DerivedCategory.Plus.ι.map_injective
    change DerivedCategory.Plus.ι.map
      (F.rightDerivedFunctorPlus.map (triangleOfSESPlusMap hS hT f).hom₃ ≫
        (mapTriangleOfSESPlusIso F hT).hom.hom₃) =
      DerivedCategory.Plus.ι.map ((mapTriangleOfSESPlusIso F hS).hom.hom₃ ≫
        (triangleOfSESPlusMap (map_triangleOfSESPlus_shortExact F hS)
          (map_triangleOfSESPlus_shortExact F hT)
            (F.mapCochainComplexPlus.mapShortComplex.map f)).hom₃)
    refine (DerivedCategory.Plus.ι.map_comp _ _).trans
      (Eq.trans ?_ (DerivedCategory.Plus.ι.map_comp _ _).symm)
    simp only [triangleOfSESPlusMap_hom₃, mapTriangleOfSESPlusIso_hom₃_ι]
    change (F.rightDerivedFunctorPlus ⋙ DerivedCategory.Plus.ι).map
        (DerivedCategory.Plus.Q.map f.τ₃) ≫
      F.rightDerivedFunctorPlusCompιIso.hom.app (DerivedCategory.Plus.Q.obj T.X₃) ≫
        F.mapDerivedCategoryFactors.hom.app T.X₃.obj =
      (F.rightDerivedFunctorPlusCompιIso.hom.app (DerivedCategory.Plus.Q.obj S.X₃) ≫
        F.mapDerivedCategoryFactors.hom.app S.X₃.obj) ≫
          DerivedCategory.Q.map ((F.mapHomologicalComplex (.up ℤ)).map f.τ₃.hom)
    exact ((F.rightDerivedFunctorPlusCompιIso.hom.naturality_assoc
      (DerivedCategory.Plus.Q.map f.τ₃) _).trans
        (congrArg (fun k => F.rightDerivedFunctorPlusCompιIso.hom.app
          (DerivedCategory.Plus.Q.obj S.X₃) ≫ k)
            (F.mapDerivedCategoryFactors.hom.naturality f.τ₃.hom))).trans
              (Category.assoc _ _ _).symm

end DerivedCategory.Plus
