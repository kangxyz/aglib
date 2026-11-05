/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.EtaleCohomology.Constructible.Modules.HomContinuity

/-! # Original native module maps and eventual relations

Representatives in the actual right-tail Hom colimit are transposed through
the original image adjunction. Equality of two original representatives is
witnessed after an actual later index arrow in that same system.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite

namespace AlgebraicGeometry.Scheme.EtaleCohomology.Constructible.Modules.NativeFreePresentation

universe u

open Continuity.NativeModule

variable (R : Type (u + 1)) [Ring R]
    {I : Type u} [SmallCategory I] (X : I ⥤ Scheme.{u}ᵒᵖ) (c : Cocone X)
    (F : Continuity.NativeModule.DiagramCoefficientSystem R X)
    [HasColimit (Continuity.NativeModule.coneCoefficientFunctor R X c F)]

/-- The literal original coefficient triangle sends a stage arrow to the cone. -/
def originalTriangleMap {i j : I} (a : i ⟶ j)
    {A : Continuity.NativeModule.Coefficient R (X.obj i).unop}
    (β : (Continuity.NativeModule.inverseImage R (X.map a).unop).obj A ⟶ F.obj j) :
    (Continuity.NativeModule.inverseImage R (c.ι.app i).unop).obj A ⟶
      (Continuity.NativeModule.inverseImage R (c.ι.app j).unop).obj (F.obj j) :=
  ((Continuity.NativeModule.diagramConeAdjunctionData R X c).leftTriangle a).hom.app A ≫
    (Continuity.NativeModule.inverseImage R (c.ι.app j).unop).map β

/-- The original adjunction mate of a triangle composite is its actual
right-tail leg, not merely an isomorphic replacement diagram. -/
theorem adjoint_originalRightTailLeg (i : I) (a : Under i)
    (A : Continuity.NativeModule.Coefficient R (X.obj i).unop)
    (k : A ⟶ (Continuity.NativeModule.diagramRightTail R X F i).obj a) :
    (Continuity.NativeModule.imageAdjunction R (c.ι.app i).unop).homEquiv _ _
      (originalTriangleMap R X c F a.hom
        (((Continuity.NativeModule.imageAdjunction R (X.map a.hom).unop).homEquiv _ _).symm k) ≫
        colimit.ι (Continuity.NativeModule.coneCoefficientFunctor R X c F) a.right) =
      k ≫ (Continuity.NativeModule.diagramRightTailCocone R X c F i).ι.app a := by
  let P := Continuity.NativeModule.diagramConeAdjunctionData R X c
  have h := Adjunction.RepresentedCoherence.homEquiv_comp
    (Continuity.NativeModule.imageAdjunction R (X.map a.hom).unop)
    (P.adj a.right) (P.adj i)
    (P.leftTriangle a.hom).hom (P.rightTriangle a.hom).hom (P.conjugate a.hom)
    A (F.obj a.right) (colimit (Continuity.NativeModule.coneCoefficientFunctor R X c F))
    (((Continuity.NativeModule.imageAdjunction R (X.map a.hom).unop).homEquiv _ _).symm k)
    (colimit.ι (Continuity.NativeModule.coneCoefficientFunctor R X c F) a.right)
  let e := (Continuity.NativeModule.imageAdjunction R (X.map a.hom).unop).homEquiv
    A (F.obj a.right)
  have he : e (e.symm k) = k := e.apply_symm_apply k
  have hleg := congrArg (fun z => z ≫
    (Continuity.NativeModule.diagramRightTailCocone R X c F i).ι.app a) he
  have ha := congrArg ((P.adj i).homEquiv A
    (colimit (Continuity.NativeModule.coneCoefficientFunctor R X c F)))
    (Category.assoc ((P.leftTriangle a.hom).hom.app A)
      ((P.left a.right).map (e.symm k))
      (colimit.ι (Continuity.NativeModule.coneCoefficientFunctor R X c F) a.right))
  exact ha.trans (h.trans hleg)

variable [IsFiltered I]
    [∀ {j k} (a : j ⟶ k), IsAffineHom (X.map a).unop] (hc : IsColimit c)

include hc in
/-- Every original limit arrow out of a native finite stage comes from a
later original coefficient, with the actual triangle equality. -/
theorem exists_originalRightTailHom (i : I)
    (A : Continuity.NativeModule.Coefficient R (X.obj i).unop)
    (hA : finiteColimitStages R (X.obj i).unop A)
    (γ : (Continuity.NativeModule.inverseImage R (c.ι.app i).unop).obj A ⟶
      colimit (Continuity.NativeModule.coneCoefficientFunctor R X c F)) :
    ∃ (a : Under i)
      (β : (Continuity.NativeModule.inverseImage R (X.map a.hom).unop).obj A ⟶ F.obj a.right),
      originalTriangleMap R X c F a.hom β ≫
        colimit.ι (Continuity.NativeModule.coneCoefficientFunctor R X c F) a.right = γ := by
  let C := Continuity.NativeModule.diagramRightTailCocone R X c F i
  let Γ := (Continuity.NativeModule.imageAdjunction R (c.ι.app i).unop).homEquiv _ _ γ
  have hC := isColimitHomRightTail R X c hc F i A hA
  obtain ⟨a, k, hk⟩ := Types.jointly_surjective_of_isColimit hC Γ
  change k ≫ C.ι.app a = Γ at hk
  refine ⟨a,
    ((Continuity.NativeModule.imageAdjunction R (X.map a.hom).unop).homEquiv _ _).symm k, ?_⟩
  apply ((Continuity.NativeModule.imageAdjunction R (c.ι.app i).unop).homEquiv _ _).injective
  exact (adjoint_originalRightTailLeg R X c F i a A k).trans hk

include hc in
/-- Actual right-tail representatives with the same limit image become equal
after one actual later arrow in that same original diagram. -/
theorem originalRightTailHom_eventually_equal (i : I)
    (A : Continuity.NativeModule.Coefficient R (X.obj i).unop)
    (hA : finiteColimitStages R (X.obj i).unop A) (a : Under i)
    (f g : A ⟶ (Continuity.NativeModule.diagramRightTail R X F i).obj a)
    (h : f ≫ (Continuity.NativeModule.diagramRightTailCocone R X c F i).ι.app a =
      g ≫ (Continuity.NativeModule.diagramRightTailCocone R X c F i).ι.app a) :
    ∃ (b : Under i) (q : a ⟶ b),
      f ≫ (Continuity.NativeModule.diagramRightTail R X F i).map q =
        g ≫ (Continuity.NativeModule.diagramRightTail R X F i).map q := by
  have hC := isColimitHomRightTail R X c hc F i A hA
  exact (Types.FilteredColimit.isColimit_eq_iff' (ht := hC) (x := f) (y := g)).1 h

end AlgebraicGeometry.Scheme.EtaleCohomology.Constructible.Modules.NativeFreePresentation
