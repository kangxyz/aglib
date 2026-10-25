/-
Copyright (c) 2026 kangxyz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.EtaleCohomology.Stalk.FibreProductStalk

/-! # Original fibre-product cohomology germs under pointed restriction

The actual fibre-product cohomology presheaf and the native point-colimit
relation identify the germs of an original class and its original restriction.
No inverse-limit continuity or replacement cohomology is used.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite

namespace AlgebraicGeometry.Scheme.EtaleCohomology

universe u w s e

attribute [local instance] hasSheafifyLarge

variable {X S : Scheme.{u}} (f : X ⟶ S)
  [HasExt.{w} (AbelianSheaf.{u, u + 1} X)]
  [∀ U : S.Etale, HasExt.{s} (Sheaf ((Scheme.smallEtaleTopology X).over
    ((siteBaseChange f).obj U)) AddCommGrpCat.{u + 1})]
  [∀ U : S.Etale, HasExt.{e} (AbelianSheaf.{u, u + 1} (pullback U.hom f))]
  (F : AbelianSheaf.{u, u + 1} X) (q : ℕ)

/-- Resizing retains the original fibre-product cohomology restriction map. -/
theorem smallFibreProductCohomologyPresheaf_map_shrink_symm
    {U V : S.Etale} (g : V ⟶ U)
    (x : Sheaf.H.{e} ((inverseImage (pullback.snd U.hom f)).obj F) q) :
    (smallFibreProductCohomologyPresheaf f F q).map g.op (Shrink.addEquiv.symm x) =
      Shrink.addEquiv.symm (fibreProductCohomologyRestriction f g F q x) := by
  change Shrink.addEquiv.symm (fibreProductCohomologyRestriction f g F q
    (Shrink.addEquiv (Shrink.addEquiv.symm x))) = _
  rw [AddEquiv.apply_symm_apply]

variable {Ω : Type u} [Field Ω] [IsSepClosed Ω] (η : Spec (.of Ω) ⟶ S)

/-- Restriction along an actual étale chart arrow preserves its original higher-image germ. -/
theorem fibreProductCohomologyGerm_restriction_map
    {U V : S.Etale} (g : V ⟶ U) (p : (pointSmallEtale η).fiber.obj V)
    (x : Sheaf.H.{e} ((inverseImage (pullback.snd U.hom f)).obj F) q) :
    fibreProductCohomologyGerm f V F q η p
        (fibreProductCohomologyRestriction f g F q x) =
      fibreProductCohomologyGerm f U F q η ((pointSmallEtale η).fiber.map g p) x := by
  have hpoint := ConcreteCategory.congr_hom
    ((pointSmallEtale η).toPresheafFiber_w g p
      (smallFibreProductCohomologyPresheaf f F q)) (Shrink.addEquiv.symm x)
  have hmap := congrArg
    ((pointSmallEtale η).toPresheafFiber V p
      (smallFibreProductCohomologyPresheaf f F q))
    (smallFibreProductCohomologyPresheaf_map_shrink_symm f F q g x)
  exact (germ_fibreProductCohomologyStalkIso_apply f F q η V p
    (fibreProductCohomologyRestriction f g F q x)).symm.trans
      ((congrArg (fibreProductCohomologyStalkIso f F q η).hom
        (hmap.symm.trans hpoint)).trans
        (germ_fibreProductCohomologyStalkIso_apply f F q η U
          ((pointSmallEtale η).fiber.map g p) x))

/-- An arbitrary pointed étale morphism gives equal original fibre-product cohomology germs. -/
theorem fibreProductCohomologyGerm_restriction
    {U V : S.Etale} (g : V ⟶ U)
    (pV : (pointSmallEtale η).fiber.obj V) (pU : (pointSmallEtale η).fiber.obj U)
    (hp : (pointSmallEtale η).fiber.map g pV = pU)
    (x : Sheaf.H.{e} ((inverseImage (pullback.snd U.hom f)).obj F) q) :
    fibreProductCohomologyGerm f V F q η pV
        (fibreProductCohomologyRestriction f g F q x) =
      fibreProductCohomologyGerm f U F q η pU x :=
  (fibreProductCohomologyGerm_restriction_map f F q η g pV x).trans
    (congrArg (fun p ↦ fibreProductCohomologyGerm f U F q η p x) hp)

end AlgebraicGeometry.Scheme.EtaleCohomology
