/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.CategoryTheory.Sites.Point.Over
public import Aglib.AlgebraicGeometry.EtaleCohomology.Stalk.EtaleSliceCategory
public import Mathlib.AlgebraicGeometry.Sites.EtalePoint

/-! # Original geometric germs under actual étale restriction

The genuine étale slice equivalence identifies pointed neighborhoods on the
chart with the native slice point. Cofinality then identifies the original
presheaf fibres, retaining every original germ map. No inverse-image
comparison isomorphism is used without its map equation.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite

namespace AlgebraicGeometry.Scheme.EtaleCohomology

universe u v w

variable {X S : Scheme.{u}} (f : S ⟶ X) [Etale f]
  {Ω : Type u} [Field Ω] [IsSepClosed Ω] (η : Spec (.of Ω) ⟶ S)

/-- The original geometric point, regarded on the actual chart over its base. -/
def etaleRestrictionChartPoint :
    (pointSmallEtale (η ≫ f)).fiber.obj (Scheme.Etale.mk f) :=
  Over.homMk η rfl

/-- The genuine slice equivalence preserves the given geometric point. -/
def etaleRestrictionPointFiberIso :
    (pointSmallEtale η).fiber ≅ etaleSliceBackward (Scheme.Etale.mk f) ⋙
      ((pointSmallEtale (η ≫ f)).over (etaleRestrictionChartPoint f η)).fiber :=
  NatIso.ofComponents (fun V => Equiv.toIso
    { toFun := fun t => by
        let t' : Over.mk η ⟶ (Etale.forget S).obj V := t
        refine ⟨Over.homMk t'.left ?_, ?_⟩
        · exact (Category.assoc t'.left V.hom f).symm.trans
            (congrArg (fun q => q ≫ f) (Over.w t'))
        · apply (FunctorToTypes.mem_fromOverSubfunctor_iff
            (pointSmallEtale (η ≫ f)).fiber (etaleRestrictionChartPoint f η) _).mpr
          apply Over.OverMorphism.ext
          exact Over.w t'
      invFun := fun t => by
        have ht := (FunctorToTypes.mem_fromOverSubfunctor_iff
          (pointSmallEtale (η ≫ f)).fiber (etaleRestrictionChartPoint f η) _).mp t.2
        let t' : Over.mk (η ≫ f) ⟶
            (Etale.forget X).obj ((siteEtalePostcompose f).obj V) := t.1
        exact Over.homMk t'.left (congrArg Over.Hom.left ht)
      left_inv := fun t => by apply Over.OverMorphism.ext; rfl
      right_inv := fun t => by apply Subtype.ext; apply Over.OverMorphism.ext; rfl })
    (by
      intro V W g
      ext t
      apply Subtype.ext
      apply Over.OverMorphism.ext
      rfl)

local instance : (etaleSliceBackward (Scheme.Etale.mk f)).IsEquivalence :=
  inferInstanceAs (etaleSliceEquivalence (Scheme.Etale.mk f)).inverse.IsEquivalence

/-- The native equivalences lift the genuine étale slice equivalence to its
pointed neighborhood categories. -/
def etaleRestrictionPointElementsEquivalence :
    (pointSmallEtale η).fiber.Elements ≌
      ((pointSmallEtale (η ≫ f)).over (etaleRestrictionChartPoint f η)).fiber.Elements :=
  (Functor.Elements.structuredArrowEquivalence (pointSmallEtale η).fiber).trans
    ((StructuredArrow.mapNatIso (etaleRestrictionPointFiberIso f η)).trans
      (((StructuredArrow.pre PUnit (etaleSliceBackward (Scheme.Etale.mk f))
        ((pointSmallEtale (η ≫ f)).over
          (etaleRestrictionChartPoint f η)).fiber).asEquivalence).trans
        (Functor.Elements.structuredArrowEquivalence
          ((pointSmallEtale (η ≫ f)).over
            (etaleRestrictionChartPoint f η)).fiber).symm))

/-- The original chart-pointed neighborhoods map to the original base neighborhoods. -/
def etaleRestrictionPointElementsForget :
    (pointSmallEtale η).fiber.Elements ⥤ (pointSmallEtale (η ≫ f)).fiber.Elements :=
  (etaleRestrictionPointElementsEquivalence f η).functor ⋙
    (pointSmallEtale (η ≫ f)).overElementsForget (etaleRestrictionChartPoint f η)

instance : (etaleRestrictionPointElementsForget f η).Initial := by
  unfold etaleRestrictionPointElementsForget
  infer_instance

variable {A : Type v} [Category.{w} A] [HasColimitsOfSize.{u, u} A]

/-- Actual étale presheaf restriction preserves the original geometric fibre. -/
def etaleRestrictionPresheafFiberIso (P : X.Etaleᵒᵖ ⥤ A) :
    (pointSmallEtale η).presheafFiber.obj ((siteEtalePostcompose f).op ⋙ P) ≅
      (pointSmallEtale (η ≫ f)).presheafFiber.obj P :=
  Functor.Final.colimitIso (etaleRestrictionPointElementsForget f η).op
    ((Functor.Elements.π (pointSmallEtale (η ≫ f)).fiber).op ⋙ P)

/-- The comparison retains the literal original germ at every chart neighborhood. -/
@[reassoc (attr := simp)]
theorem toPresheafFiber_etaleRestrictionPresheafFiberIso_hom
    (P : X.Etaleᵒᵖ ⥤ A) (V : S.Etale) (t : (pointSmallEtale η).fiber.obj V) :
    (pointSmallEtale η).toPresheafFiber V t ((siteEtalePostcompose f).op ⋙ P) ≫
        (etaleRestrictionPresheafFiberIso f η P).hom =
      (pointSmallEtale (η ≫ f)).toPresheafFiber
        ((siteEtalePostcompose f).obj V)
        (Over.homMk t.left (by
          let t' : Over.mk η ⟶ (Etale.forget S).obj V := t
          exact (Category.assoc t'.left V.hom f).symm.trans
            (congrArg (fun q => q ≫ f) (Over.w t')))) P :=
  Functor.Final.ι_colimitIso_hom (etaleRestrictionPointElementsForget f η).op
    ((Functor.Elements.π (pointSmallEtale (η ≫ f)).fiber).op ⋙ P)
    (op ((pointSmallEtale η).fiber.elementsMk V t))

end AlgebraicGeometry.Scheme.EtaleCohomology
