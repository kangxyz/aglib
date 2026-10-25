/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.EtaleCohomology.Stalk.FibreProductStalk
public import Mathlib.Algebra.Category.Grp.FilteredColimits

/-! # Every original stalk class has a fibre-product cohomology representative

The original stalk is the actual presheaf fibre of the resized cohomology
diagram. Filtered-colimit preservation supplies a representative, which is
then returned in the original, unresized scheme cohomology group.
-/

@[expose] public noncomputable section

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open CategoryTheory CategoryTheory.Limits Opposite

namespace AlgebraicGeometry.Scheme.EtaleCohomology

universe u w s e v

attribute [local instance] hasSheafifyLarge

variable {X S : Scheme.{u}} (f : X ⟶ S)
  [HasExt.{w} (AbelianSheaf.{u, u + 1} X)]
  [∀ U : S.Etale, HasExt.{s} (Sheaf ((Scheme.smallEtaleTopology X).over
    ((siteBaseChange f).obj U)) AddCommGrpCat.{u + 1})]
  [∀ U : S.Etale, HasExt.{e} (AbelianSheaf.{u, u + 1} (pullback U.hom f))]
  (F : AbelianSheaf.{u, u + 1} X) (q : ℕ)
  {Ω : Type u} [Field Ω] [IsSepClosed Ω] (η : Spec (.of Ω) ⟶ S)

/-- Every original higher-image stalk class is the original germ of an actual
unresized fibre-product cohomology class. -/
theorem exists_fibreProductCohomologyGerm
    (z : ((pointSmallEtale η).sheafFiber (A := AddCommGrpCat.{u + 1})).obj
      ((higherDirectImage f q).obj F)) :
    ∃ (U : S.Etale) (p : (pointSmallEtale η).fiber.obj U)
      (y : Sheaf.H.{e} ((inverseImage (pullback.snd U.hom f)).obj F) q),
      fibreProductCohomologyGerm f U F q η p y = z := by
  let : PreservesFilteredColimitsOfSize.{u, u} (CategoryTheory.forget AddCommGrpCat.{u + 1}) :=
    preservesFilteredColimitsOfSize_of_univLE.{u + 1, u + 1}
      (CategoryTheory.forget AddCommGrpCat.{u + 1})
  let E := fibreProductCohomologyStalkIso f F q η
  obtain ⟨U, p, t, ht⟩ := (pointSmallEtale η).toPresheafFiber_jointly_surjective
    (P := smallFibreProductCohomologyPresheaf f F q) (E.inv z)
  refine ⟨U, p, Shrink.addEquiv t, ?_⟩
  calc
    fibreProductCohomologyGerm f U F q η p (Shrink.addEquiv t) =
        E.hom ((pointSmallEtale η).toPresheafFiber U p
          (smallFibreProductCohomologyPresheaf f F q)
          (Shrink.addEquiv.symm (Shrink.addEquiv t))) :=
      (germ_fibreProductCohomologyStalkIso_apply f F q η U p (Shrink.addEquiv t)).symm
    _ = E.hom ((pointSmallEtale η).toPresheafFiber U p
        (smallFibreProductCohomologyPresheaf f F q) t) := by
      rw [AddEquiv.symm_apply_apply]
    _ = E.hom (E.inv z) := congrArg E.hom ht
    _ = z := ConcreteCategory.congr_hom E.inv_hom_id z

/-- Original fibre-product germs determine functions into any universe. -/
theorem fibreProductCohomologyGerm_funext {A : Type v}
    {a b : ((pointSmallEtale η).sheafFiber (A := AddCommGrpCat.{u + 1})).obj
      ((higherDirectImage f q).obj F) → A}
    (h : ∀ (U : S.Etale) (p : (pointSmallEtale η).fiber.obj U)
      (y : Sheaf.H.{e} ((inverseImage (pullback.snd U.hom f)).obj F) q),
      a (fibreProductCohomologyGerm f U F q η p y) =
        b (fibreProductCohomologyGerm f U F q η p y)) : a = b := by
  funext z
  obtain ⟨U, p, y, rfl⟩ := exists_fibreProductCohomologyGerm f F q η z
  exact h U p y

end AlgebraicGeometry.Scheme.EtaleCohomology
