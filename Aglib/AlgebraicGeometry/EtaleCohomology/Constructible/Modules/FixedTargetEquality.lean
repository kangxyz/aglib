/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.EtaleCohomology.Constructible.Modules.FixedTargetHom
public import Aglib.CategoryTheory.Filtered.FixedSourceUnits

/-! # Eventual equality of actual fixed-ring model arrows

Original adjunction units normalize the same native right-tail Hom cocone.
Consequently equality after the original limit pullback is witnessed by
literal equality after one original later structural pullback.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite

namespace AlgebraicGeometry.Scheme.EtaleCohomology.Continuity.NativeModule

universe u

variable (R : Type (u + 1)) [Ring R]
    {I : Type u} [SmallCategory I]
    (X : I ⥤ Scheme.{u}ᵒᵖ) (i : I)
    (r : (Functor.const I).obj (X.obj i) ⟶ X) (hr : r.app i = 𝟙 (X.obj i))


/-- The original fixed model pulled along its actual structural cone. -/
abbrev baseSystem (B : Coefficient R (X.obj i).unop) :=
  pullbackCoefficientSystem R X (Cone.mk (X.obj i) r) B

private def baseIdentityIso :
    inverseImage R (r.app i).unop ≅ 𝟭 (Coefficient R (X.obj i).unop) :=
  eqToIso (congrArg (schemeAdjunctionData R).left hr) ≪≫
    (schemeAdjunctionData R).leftIdIso (X.obj i)

private def baseStageIso (B : Coefficient R (X.obj i).unop) (a : Under i) :
    (baseSystem R X i r B).obj a.right ≅ (inverseImage R (X.map a.hom).unop).obj B :=
  eqToIso (congrArg (fun q : X.obj i ⟶ X.obj a.right => (inverseImage R q.unop).obj B)
    (InjectiveSystem.AdjunctionData.fixedBaseCone_leg X i r hr a.hom))

private def baseUnit (B : Coefficient R (X.obj i).unop) (a : Under i) :
    B ⟶ (diagramRightTail R X (baseSystem R X i r B) i).obj a :=
  (baseIdentityIso R X i r hr).inv.app B ≫ (baseSystem R X i r B).map a.hom

private theorem baseUnit_naturality (B : Coefficient R (X.obj i).unop)
    {a b : Under i} (q : a ⟶ b) :
    baseUnit R X i r hr B a ≫ (diagramRightTail R X (baseSystem R X i r B) i).map q =
      baseUnit R X i r hr B b := by
  exact InjectiveSystem.System.rightTailTransition_unit
    (diagramAdjunctionData R X) (baseSystem R X i r B)
    a.hom q.right b.hom (Under.w q) ((baseIdentityIso R X i r hr).inv.app B)

private theorem baseUnit_value (B : Coefficient R (X.obj i).unop) (a : Under i) :
    baseUnit R X i r hr B a ≫
      (directImage R (X.map a.hom).unop).map (baseStageIso R X i r hr B a).hom =
        (imageAdjunction R (X.map a.hom).unop).unit.app B := by
  have h := (schemeAdjunctionData R).fixedSourceTriangle_unit (schemeAdjunctionData_coherent R)
    (r.app i) hr (X.map a.hom) (r.app a.right) ((Cone.mk (X.obj i) r).w a.hom)
    (InjectiveSystem.AdjunctionData.fixedBaseCone_leg X i r hr a.hom) B
  exact (Category.assoc ((baseIdentityIso R X i r hr).inv.app B)
    ((baseSystem R X i r B).map a.hom)
    ((directImage R (X.map a.hom).unop).map (baseStageIso R X i r hr B a).hom)).trans h

variable [IsFiltered I] (c : Cocone X)

local instance : IsConnected I := IsFiltered.isConnected I

include hr in
private theorem baseFac (j : I) : r.app j ≫ c.ι.app j = c.ι.app i := by
  exact FixedModelData.baseCone_fac X i r hr c j

variable (B : Coefficient R (X.obj i).unop)
    [HasColimit (coneCoefficientFunctor R X c (baseSystem R X i r B))]

private def baseLimitIso :
    colimit (coneCoefficientFunctor R X c (baseSystem R X i r B)) ≅
      (inverseImage R (c.ι.app i).unop).obj B :=
  FixedModelData.limitIso R X i r hr c B

private theorem baseUnit_point (a : Under i) :
    baseUnit R X i r hr B a ≫ (diagramRightTailCocone R X c (baseSystem R X i r B) i).ι.app a ≫
      (directImage R (c.ι.app i).unop).map (baseLimitIso R X i r hr c B).hom =
        (imageAdjunction R (c.ι.app i).unop).unit.app B := by
  let F := baseSystem R X i r B
  let P := diagramConeAdjunctionData R X c
  let E := baseLimitIso R X i r hr c B
  have hleg : F.map a.hom ≫ (diagramRightTailCocone R X c F i).ι.app a =
      P.adjointLeg F i := (P.adjointLeg_naturality F a.hom).symm
  have hins : colimit.ι (coneCoefficientFunctor R X c F) i ≫ E.hom =
      ((schemeAdjunctionData R).triangleIso (c.ι.app i) (r.app i)
        (c.ι.app i) (baseFac X i r hr c i)).inv.app B :=
    FixedModelData.limitIso_ι R X i r hr c B i
  have hunit := (schemeAdjunctionData R).fixedSourceTriangle_unit
    (schemeAdjunctionData_coherent R) (r.app i) hr (c.ι.app i) (c.ι.app i)
    (baseFac X i r hr c i) rfl B
  let e : B ⟶ F.obj i := (baseIdentityIso R X i r hr).inv.app B
  let L := (diagramRightTailCocone R X c F i).ι.app a
  let V := (directImage R (c.ι.app i).unop).map E.hom
  have hstart : (e ≫ F.map a.hom) ≫ L ≫ V = e ≫ P.adjointLeg F i ≫ V :=
    (Category.assoc e (F.map a.hom) (L ≫ V)).trans
      (congrArg (fun k => e ≫ k)
        ((Category.assoc (F.map a.hom) L V).symm.trans
          (congrArg (fun k => k ≫ V) hleg)))
  have hn := (imageAdjunction R (c.ι.app i).unop).homEquiv_naturality_right
    (colimit.ι (coneCoefficientFunctor R X c F) i) E.hom
  have hend : e ≫ P.adjointLeg F i ≫ V =
      e ≫ (imageAdjunction R (c.ι.app i).unop).homEquiv _ _
        (((schemeAdjunctionData R).triangleIso (c.ι.app i) (r.app i)
          (c.ι.app i) (baseFac X i r hr c i)).inv.app B) :=
    congrArg (fun k => e ≫ k)
      (hn.symm.trans (congrArg ((imageAdjunction R (c.ι.app i).unop).homEquiv _ _) hins))
  change e ≫ (imageAdjunction R (c.ι.app i).unop).homEquiv _ _
      (((schemeAdjunctionData R).triangleIso (c.ι.app i) (r.app i)
        (c.ι.app i) (baseFac X i r hr c i)).inv.app B) ≫
      (directImage R (c.ι.app i).unop).map
        (𝟙 ((inverseImage R (c.ι.app i).unop).obj B)) = _ at hunit
  have hu := (congrArg (fun k => e ≫
      (imageAdjunction R (c.ι.app i).unop).homEquiv _ _
        (((schemeAdjunctionData R).triangleIso (c.ι.app i) (r.app i)
          (c.ι.app i) (baseFac X i r hr c i)).inv.app B) ≫ k)
      ((directImage R (c.ι.app i).unop).map_id
        ((inverseImage R (c.ι.app i).unop).obj B)))
  have hu' := congrArg (fun k => e ≫ k)
    (Category.comp_id ((imageAdjunction R (c.ι.app i).unop).homEquiv _ _
      (((schemeAdjunctionData R).triangleIso (c.ι.app i) (r.app i)
        (c.ι.app i) (baseFac X i r hr c i)).inv.app B)))
  exact hstart.trans (hend.trans ((hu.trans hu').symm.trans hunit))

include hr in
/-- Equality of original limit pullbacks descends to an actual later map. -/
theorem baseHom_eventually_equal (hc : IsColimit c)
    [∀ {j k} (a : j ⟶ k), IsAffineHom (X.map a).unop]
    (A : Coefficient R (X.obj i).unop)
    (hA : Constructible.Modules.NativeFreePresentation.finiteColimitStages R (X.obj i).unop A)
    (f g : A ⟶ B)
    (h : (inverseImage R (c.ι.app i).unop).map f =
      (inverseImage R (c.ι.app i).unop).map g) :
    ∃ a : Under i, (inverseImage R (X.map a.hom).unop).map f =
      (inverseImage R (X.map a.hom).unop).map g := by
  let F := baseSystem R X i r B
  exact AdjointStageHom.eventually_equal_of_units
    (Stages := fun a : Under i => Coefficient R (X.obj a.right).unop)
    (inverseImage R (c.ι.app i).unop) (directImage R (c.ι.app i).unop)
    (imageAdjunction R (c.ι.app i).unop)
    (fun a => inverseImage R (X.map a.hom).unop)
    (fun a => directImage R (X.map a.hom).unop)
    (fun a => imageAdjunction R (X.map a.hom).unop)
    (diagramRightTail R X F i) (diagramRightTailCocone R X c F i)
    (baseUnit R X i r hr B) (fun {_ _} q => baseUnit_naturality R X i r hr B q)
    ((directImage R (c.ι.app i).unop).mapIso (baseLimitIso R X i r hr c B))
    (baseUnit_point R X i r hr c B)
    (fun a => (directImage R (X.map a.hom).unop).map (baseStageIso R X i r hr B a).hom)
    (baseUnit_value R X i r hr B)
    (fun a f g hfg =>
      Constructible.Modules.NativeFreePresentation.originalRightTailHom_eventually_equal
        R X c F hc i A hA a f g hfg)
    (Under.mk (𝟙 i)) f g h

end AlgebraicGeometry.Scheme.EtaleCohomology.Continuity.NativeModule
