/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.Algebra.Homology.DerivedCategory.Plus.ShortExact
public import Aglib.Algebra.Homology.DerivedCategory.RightDerivedFunctorPlus.ExactFunctor

/-!
# Exact functors preserve the original short-exact-complex triangle

The comparison retains Mathlib's actual connecting arrow. The bounded-below
comparison is descended only through the fully faithful bounded-below inclusion,
not through the exact functor itself.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits CategoryTheory.Pretriangulated

universe u v u' v' w w'

namespace DerivedCategory

variable {C : Type u} [Category.{v} C] [Abelian C] [HasDerivedCategory.{w} C]
  {D : Type u'} [Category.{v'} D] [Abelian D] [HasDerivedCategory.{w'} D]
  (F : C ⥤ D) [F.Additive] [PreservesFiniteLimits F] [PreservesFiniteColimits F]

/-- The native exact-derived comparison on an entire original short-exact triangle. -/
def mapTriangleOfSESIso {S : ShortComplex (CochainComplex C ℤ)} (hS : S.ShortExact) :
    F.mapDerivedCategory.mapTriangle.obj (triangleOfSES hS) ≅
      triangleOfSES (hS.map_of_exact (F.mapHomologicalComplex (.up ℤ))) := by
  refine Triangle.isoMk _ _ (F.mapDerivedCategoryFactors.app S.X₁)
    (F.mapDerivedCategoryFactors.app S.X₂) (F.mapDerivedCategoryFactors.app S.X₃)
    ?_ ?_ ?_
  · exact F.mapDerivedCategoryFactors.hom.naturality S.f
  · exact F.mapDerivedCategoryFactors.hom.naturality S.g
  · change (F.mapDerivedCategory.map (triangleOfSESδ hS) ≫
      (F.mapDerivedCategory.commShiftIso (1 : ℤ)).hom.app (Q.obj S.X₁)) ≫
        (shiftFunctor (DerivedCategory D) (1 : ℤ)).map
          (F.mapDerivedCategoryFactors.hom.app S.X₁) =
      F.mapDerivedCategoryFactors.hom.app S.X₃ ≫
        triangleOfSESδ (hS.map_of_exact (F.mapHomologicalComplex (.up ℤ)))
    rw [CategoryTheory.DerivedCategory.map_triangleOfSESδ]
    simp only [Category.assoc, Iso.inv_hom_id_app]
    let e := (shiftFunctor (DerivedCategory D) (1 : ℤ)).mapIso
      (F.mapDerivedCategoryFactors.app S.X₁)
    change F.mapDerivedCategoryFactors.hom.app S.X₃ ≫
      triangleOfSESδ (hS.map_of_exact (F.mapHomologicalComplex (.up ℤ))) ≫
        e.inv ≫ 𝟙 _ ≫ e.hom = _
    rw [Category.id_comp, e.inv_hom_id]
    exact congrArg (fun k => F.mapDerivedCategoryFactors.hom.app S.X₃ ≫ k)
      (Category.comp_id
        (triangleOfSESδ (hS.map_of_exact (F.mapHomologicalComplex (.up ℤ)))))

namespace Plus

variable [EnoughInjectives C]
  {S : ShortComplex (CochainComplex.Plus C)}
  (hS : (S.map (CochainComplex.Plus.ι C)).ShortExact)

include hS in
omit [EnoughInjectives C] [HasDerivedCategory C] [HasDerivedCategory D] in
/-- Exactness on the actual bounded-below termwise image. -/
theorem map_triangleOfSESPlus_shortExact :
    ((S.map F.mapCochainComplexPlus).map (CochainComplex.Plus.ι D)).ShortExact :=
  hS.map_of_exact (F.mapHomologicalComplex (.up ℤ))

/-- The exact right-derived functor preserves the original entire D+ SES triangle,
including its actual connecting arrow. -/
def mapTriangleOfSESPlusIso :
    F.rightDerivedFunctorPlus.mapTriangle.obj (triangleOfSESPlus hS) ≅
      triangleOfSESPlus (map_triangleOfSESPlus_shortExact F hS) :=
  (DerivedCategory.Plus.ι (C := D)).mapTriangle.preimageIso
    ((Functor.mapTriangleCompIso F.rightDerivedFunctorPlus DerivedCategory.Plus.ι).symm.app _ ≪≫
      (Functor.mapTriangleIso F.rightDerivedFunctorPlusCompιIso).app _ ≪≫
      (Functor.mapTriangleCompIso DerivedCategory.Plus.ι F.mapDerivedCategory).app _ ≪≫
      F.mapDerivedCategory.mapTriangle.mapIso (triangleOfSESPlusιIso hS) ≪≫
      mapTriangleOfSESIso F hS ≪≫
      (triangleOfSESPlusιIso (map_triangleOfSESPlus_shortExact F hS)).symm)

end Plus
end DerivedCategory
