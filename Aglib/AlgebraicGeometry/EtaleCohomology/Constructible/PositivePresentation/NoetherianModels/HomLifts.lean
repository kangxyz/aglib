/-
Copyright (c) 2026 kangxyz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.EtaleCohomology.Constructible.PositivePresentation.NoetherianModels.HomCocones
public import Aglib.AlgebraicGeometry.EtaleCohomology.Stalk.PullbackLimitCoefficient
public import Mathlib.CategoryTheory.Filtered.Connected

/-! # Original maps and relations from the bounded Hom cocone

Native Hom-cocone representatives are transposed through the original
inverse/direct-image adjunction. The exact native right-tail leg then gives
the original coefficient triangle at the limit. Eventual equality uses the
same original Hom functor and its actual transitions.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite

namespace AlgebraicGeometry.Scheme.EtaleCohomology.Constructible.PositivePresentation
namespace NoetherianModels

universe u

attribute [local instance] hasSheafifyLarge TorsionZMod.hasSheafifyStandard
  Cardinal.fact_isRegular_aleph0

open Continuity

variable {I : Type u} [SmallCategory I]
  (X : I ⥤ Scheme.{u}ᵒᵖ) (c : Cocone X) (F : DiagramCoefficientSystem X)
  [HasColimit (coneCoefficientFunctor X c F)]

/-- Transposing a representative followed by the literal original right-tail
leg is exactly the original coefficient-triangle composition. -/
theorem adjoint_originalRightTailLeg (i : I) (a : Under i)
    (A : AbelianSheaf.{u, u + 1} (X.obj i).unop)
    (k : A ⟶ (diagramRightTail X F i).obj a) :
    (inverseImageAdjunction (c.ι.app i).unop).homEquiv _ _
      (triangleCoefficientMap (X.map a.hom).unop (c.ι.app i).unop
        (c.ι.app a.right).unop (coneSquare X c a.hom)
        (((inverseImageAdjunction (X.map a.hom).unop).homEquiv _ _).symm k) ≫
          colimit.ι (coneCoefficientFunctor X c F) a.right) =
      k ≫ (diagramRightTailCocone X F c i).ι.app a := by
  have h := triangleCoefficientMap_homEquiv (X.map a.hom).unop
    (c.ι.app i).unop (c.ι.app a.right).unop (coneSquare X c a.hom)
    (((inverseImageAdjunction (X.map a.hom).unop).homEquiv _ _).symm k)
    (colimit.ι (coneCoefficientFunctor X c F) a.right)
  let e := (inverseImageAdjunction (X.map a.hom).unop).homEquiv A (F.obj a.right)
  have he : e (e.symm k) = k := e.apply_symm_apply k
  have hleg := congrArg (fun z => z ≫ (diagramRightTailCocone X F c i).ι.app a) he
  simpa only [diagramRightTailCocone_ι_app, diagramAdjointLeg,
    diagramDirectImageTriangle, Category.assoc] using h.trans hleg

variable [IsFiltered I]
  [∀ {j k} (a : j ⟶ k), IsAffineHom (X.map a).unop]
  (hc : IsColimit c) (n : ℕ) (hF : ∀ i, n • 𝟙 (F.obj i) = 0)

include hc hF

/-- Every original map from the limit pullback of a native canonical stage
to the actual limit coefficient comes from an actual later-stage map. -/
theorem exists_originalRightTailHom (i : I)
    (A : BoundedPresentation.Coefficient (X.obj i).unop n)
    (hA : BoundedPresentation.finiteColimitStages (X.obj i).unop n A)
    (γ : (inverseImage (c.ι.app i).unop).obj A.obj ⟶
      colimit (coneCoefficientFunctor X c F)) :
    ∃ (a : Under i)
      (β : (inverseImage (X.map a.hom).unop).obj A.obj ⟶ F.obj a.right),
      triangleCoefficientMap (X.map a.hom).unop (c.ι.app i).unop
        (c.ι.app a.right).unop (coneSquare X c a.hom) β ≫
          colimit.ι (coneCoefficientFunctor X c F) a.right = γ := by
  let C := boundedRightTailCocone X F n hF c i
  let Γ : A ⟶ C.pt := ObjectProperty.homMk
    ((inverseImageAdjunction (c.ι.app i).unop).homEquiv _ _ γ)
  have hC := isColimitBoundedHomRightTail X F n hF c hc i A hA
  obtain ⟨a, k, hk⟩ := Types.jointly_surjective_of_isColimit hC Γ
  change k ≫ C.ι.app a = Γ at hk
  let β := ((inverseImageAdjunction (X.map a.hom).unop).homEquiv _ _).symm k.hom
  refine ⟨a, β, ?_⟩
  apply ((inverseImageAdjunction (c.ι.app i).unop).homEquiv _ _).injective
  exact (adjoint_originalRightTailLeg X c F i a A.obj k.hom).trans
    (congrArg (fun f => f.hom) hk)

/-- Two representatives with the same original limit image become equal
after one actual original transition in that same right-image Hom diagram. -/
theorem originalRightTailHom_eventually_equal (i : I)
    (A : BoundedPresentation.Coefficient (X.obj i).unop n)
    (hA : BoundedPresentation.finiteColimitStages (X.obj i).unop n A)
    (a : Under i) (f g : A.obj ⟶ (diagramRightTail X F i).obj a)
    (h : f ≫ (diagramRightTailCocone X F c i).ι.app a =
      g ≫ (diagramRightTailCocone X F c i).ι.app a) :
    ∃ (b : Under i) (q : a ⟶ b),
      f ≫ (diagramRightTail X F i).map q = g ≫ (diagramRightTail X F i).map q := by
  let C := boundedRightTailCocone X F n hF c i
  let f' : A ⟶ (boundedRightTail X F n hF i).obj a := ObjectProperty.homMk f
  let g' : A ⟶ (boundedRightTail X F n hF i).obj a := ObjectProperty.homMk g
  have hC := isColimitBoundedHomRightTail X F n hF c hc i A hA
  have h' :
      ((coyoneda.obj (op A)).mapCocone C).ι.app a f' =
        ((coyoneda.obj (op A)).mapCocone C).ι.app a g' := by
    change f' ≫ C.ι.app a = g' ≫ C.ι.app a
    apply ObjectProperty.hom_ext
    exact h
  obtain ⟨b, q, hq⟩ :=
    (Types.FilteredColimit.isColimit_eq_iff' (ht := hC) (x := f') (y := g')).1 h'
  change f' ≫ (boundedRightTail X F n hF i).map q =
    g' ≫ (boundedRightTail X F n hF i).map q at hq
  exact ⟨b, q, congrArg (fun f => f.hom) hq⟩

end NoetherianModels
end AlgebraicGeometry.Scheme.EtaleCohomology.Constructible.PositivePresentation
