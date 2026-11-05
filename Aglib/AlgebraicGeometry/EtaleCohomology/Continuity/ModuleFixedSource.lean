/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.EtaleCohomology.Continuity.ModuleConeCoefficients
public import Aglib.CategoryTheory.Filtered.SystemConstructions

/-! # An original fixed module coefficient pulled through a scheme system

The original inverse-image triangles define the system. At a common scheme
cone its actual coefficient diagram is canonically constant with the original
pulled-back coefficient, using native adjunction coherence.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite

namespace AlgebraicGeometry.Scheme.EtaleCohomology.Continuity.NativeModule

universe u r uI vI

variable (R : Type r) [Ring R] {I : Type uI} [Category.{vI} I]
    (X : I ⥤ Scheme.{u}ᵒᵖ) (b : Cone X) (F : Coefficient R b.pt.unop)

/-- The unchanged coefficient is pulled along the actual structural maps. -/
def pullbackCoefficientSystem : DiagramCoefficientSystem R X :=
  InjectiveSystem.System.fixedSource (schemeAdjunctionData R) X
    (schemeAdjunctionData_coherent R) b F

variable (c : Cocone X) (l : b.pt ⟶ c.pt)
    (hl : ∀ i, b.π.app i ≫ c.ι.app i = l)

/-- Original triangles identify the actual coefficient diagram with the
constant diagram on the actual pullback at the cone point. -/
def pullbackConeCoefficientIso :
    (Functor.const I).obj ((inverseImage R l.unop).obj F) ≅
      coneCoefficientFunctor R X c (pullbackCoefficientSystem R X b F) := by
  apply (schemeAdjunctionData R).fixedCoefficientIso
    (schemeAdjunctionData_coherent R) X b c l hl F
    (coneCoefficientFunctor R X c (pullbackCoefficientSystem R X b F))
    (fun _ => rfl)
  intro i j a
  have ht : (diagramConeAdjunctionData R X c).leftTriangle a =
      (schemeAdjunctionData R).triangleIso (c.ι.app i) (X.map a) (c.ι.app j) (c.w a) :=
    ((schemeAdjunctionData R).triangleIso_eq_leftAdjointCompIso
      (c.ι.app i) (X.map a) (c.ι.app j) (c.w a)).symm
  change ((diagramConeAdjunctionData R X c).leftTriangle a).hom.app _ ≫
      (inverseImage R (c.ι.app j).unop).map
        ((pullbackCoefficientSystem R X b F).leftMap (diagramAdjunctionData R X) a) =
    (𝟙 _) ≫ (schemeAdjunctionData R).triangleCoefficientMap
      (X.map a) (c.ι.app i) (c.ι.app j) (c.w a)
      (((schemeAdjunctionData R).triangleIso (b.π.app j) (b.π.app i)
        (X.map a) (b.w a)).inv.app F) ≫ (𝟙 _)
  rw [ht, Category.id_comp, Category.comp_id]
  exact congrArg
    (fun k => ((schemeAdjunctionData R).triangleIso (c.ι.app i) (X.map a)
      (c.ι.app j) (c.w a)).hom.app _ ≫ (inverseImage R (c.ι.app j).unop).map k)
    (InjectiveSystem.System.fixedSource_leftMap (schemeAdjunctionData R) X
      (schemeAdjunctionData_coherent R) b F a)

variable [IsConnected I]
    [HasColimit (coneCoefficientFunctor R X c (pullbackCoefficientSystem R X b F))]

/-- The actual native coefficient colimit is the original fixed pullback. -/
def pullbackLimitCoefficientIso :
    colimit (coneCoefficientFunctor R X c (pullbackCoefficientSystem R X b F)) ≅
      (inverseImage R l.unop).obj F :=
  constantDiagramColimitIso (pullbackConeCoefficientIso R X b F c l hl)

/-- Original insertion maps have the original inverse triangle value. -/
@[reassoc]
theorem pullbackLimitCoefficientIso_ι (i : I) :
    colimit.ι (coneCoefficientFunctor R X c (pullbackCoefficientSystem R X b F)) i ≫
        (pullbackLimitCoefficientIso R X b F c l hl).hom =
      (pullbackConeCoefficientIso R X b F c l hl).inv.app i :=
  constantDiagramColimitIso_ι _ i

end AlgebraicGeometry.Scheme.EtaleCohomology.Continuity.NativeModule
