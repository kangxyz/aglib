/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.EtaleCohomology.Stalk.FibreProductRestrictionCanonical
public import
  Aglib.AlgebraicGeometry.EtaleCohomology.Fields.TwoFieldEffacement.OriginalClassZeroTransport

/-! # Original class zeros on a target refinement kill native restriction

The actual base-change square identifies the original site restriction with
pullback through the literal iterated fibre product. No coefficient, class,
or higher image is replaced. The fixed-degree higher-image converter can
therefore consume geometric target refinements directly.
-/

@[expose] public noncomputable section
open CategoryTheory CategoryTheory.Limits
namespace AlgebraicGeometry.Scheme.EtaleCohomology
universe u
attribute [local instance] hasSheafifyLarge HasExt.standard

/-- Zero on the literal target-refined family kills the original restriction. -/
theorem fibreProductCohomologyRestriction_eq_zero_of_target_pullback
    {X S : Scheme.{u}} (f : X ⟶ S) {U V : S.Etale} (g : V ⟶ U)
    (F : AbelianSheaf.{u, u + 1} X) (q : ℕ)
    (c : Sheaf.H.{u + 2} ((inverseImage (pullback.snd U.hom f)).obj F) q)
    (hc : cohomologyPullback.{u, u + 2, u + 2}
      (pullback.snd g.left (pullback.fst U.hom f)) _ q c = 0) :
    fibreProductCohomologyRestriction f g F q c = 0 := by
  let k : pullback V.hom f ⟶ pullback U.hom f := ((siteBaseChange f).map g).left
  have hk : k ≫ pullback.snd U.hom f = pullback.snd V.hom f :=
    siteBaseChange_map_snd f g
  have ht : k ≫ pullback.fst U.hom f = pullback.fst V.hom f ≫ g.left :=
    siteBaseChange_map_fst f g
  have Houter : IsPullback (k ≫ pullback.snd U.hom f)
      (pullback.fst V.hom f) f (g.left ≫ U.hom) := by
    rw [hk, MorphismProperty.Over.w g]
    exact (IsPullback.of_hasPullback V.hom f).flip
  have H := Houter.of_right ht (IsPullback.of_hasPullback U.hom f).flip
  have hz := TwoFieldEffacement.original_class_zero_of_map_law
    H.flip.isoPullback.hom (pullback.snd g.left (pullback.fst U.hom f)) k
    H.flip.isoPullback_hom_snd _ q c hc
  rw [fibreProductCohomologyRestriction_apply_canonical, hz, map_zero]

end AlgebraicGeometry.Scheme.EtaleCohomology
