/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.Sites.EtaleLocalZero
public import Aglib.AlgebraicGeometry.EtaleCohomology.Stalk.FibreProductGermRestriction

/-! # Fixed-degree higher-image zero from original pointed class effacement

The original fibre-product cohomology presheaf and its original restriction
maps pass local annihilation through resizing and actual sheafification.
The existing sheafification comparison then kills the native higher image in
that one degree. No vanishing in other degrees or geometric effacement is
assumed to have been proved by this formal converter.
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

/-- Genuine pointed local zero of every original class in one specified degree
makes the original higher direct image zero in that same degree. -/
theorem higherDirectImage_isZero_of_pointed_local_class_zero
    (F : AbelianSheaf.{u, u + 1} X) (q : ℕ)
    (H : ∀ (U : S.Etale)
      (c : Sheaf.H.{e} ((inverseImage (pullback.snd U.hom f)).obj F) q) (x : U.left),
      ∃ (V : S.Etale) (a : V ⟶ U) (y : V.left),
        a.left y = x ∧ fibreProductCohomologyRestriction f a F q c = 0) :
    IsZero ((higherDirectImage f q).obj F) := by
  let P := Stalk.originalFibreProductCohomologyPresheaf f F q
  have hz := Scheme.Etale.isZero_sheafification_of_pointed_localZero
    (resizeAdditiveDiagram.{u + 1} P) (fun U c x => by
      let E : Shrink.{u + 1} (P.obj (op U)) ≃+ P.obj (op U) := Shrink.addEquiv
      obtain ⟨d, rfl⟩ := E.symm.surjective c
      obtain ⟨V, a, y, hy, hc⟩ := H U d x
      refine ⟨V, a, y, hy, ?_⟩
      have hc' : P.map a.op d = 0 := hc
      have h := resizeAdditiveDiagram_map_shrink_symm.{u + 1} P a.op d
      -- The two original resize expressions differ only by the opaque equivShrink carrier.
      set_option backward.isDefEq.respectTransparency false in
        simpa only [E, hc', map_zero] using h)
  exact hz.of_iso (fibreProductCohomologySheafificationIso f F q).symm

end AlgebraicGeometry.Scheme.EtaleCohomology
