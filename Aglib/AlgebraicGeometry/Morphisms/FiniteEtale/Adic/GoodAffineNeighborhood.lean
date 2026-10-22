/-
Copyright (c) 2026 kangxyz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.Morphisms.Etale.FiniteStalkNeighborhood
public import Aglib.AlgebraicGeometry.Morphisms.FiniteEtale.Adic.GoodAffineGluing

/-!
# Good affine section neighborhoods from etale stalk base changes

A finite affine section algebra which is etale after target-stalk base change
is good on an actual smaller affine open. Original cartesian restriction
squares identify that smaller piece with the original smaller section algebra.
-/

@[expose] public noncomputable section

set_option autoImplicit false
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace

namespace AlgebraicGeometry.Scheme.FiniteEtale.AffineAlgebraGluing

universe u
variable {X : Scheme.{u}} (F : X.Opensᵒᵖ ⥤ CommRingCat.{u}) (η : X.presheaf ⟶ F)
  (hcart : ∀ (U V : X.Opens) (_hU : IsAffineOpen U) (_hV : IsAffineOpen V)
    (h : U ≤ V), IsPullback (Spec.map (F.map (homOfLE h).op))
      (Spec.map (η.app (op U))) (Spec.map (η.app (op V)))
      (Spec.map (X.presheaf.map (homOfLE h).op)))

include hcart in
/-- An etale open restriction of a chart has an etale original section
algebra on its image in the ambient scheme. -/
theorem isGood_image {U : X.Opens} (hU : IsAffineOpen U)
    (W : U.toScheme.Opens) (hW : IsAffineOpen W)
    (hEt : Etale (toOpen F η U hU ∣_ W)) : IsGood F η (U.ι ''ᵁ W) := by
  let V : X.Opens := U.ι ''ᵁ W
  have hV : IsAffineOpen V := hW.image_of_isOpenImmersion U.ι
  let p := toOpen F η U hU
  let q := toOpen F η V hV
  let e := U.ι.isoImage W
  have H := restriction_isPullback F η hV hU (U.ι_image_le W)
    (hcart V U hV hU (U.ι_image_le W))
  have H' : IsPullback (Spec.map (F.map (homOfLE (U.ι_image_le W)).op))
      (q ≫ e.inv) p W.ι := by
    apply H.of_iso (Iso.refl _) (Iso.refl _) e.symm (Iso.refl _)
    · simp
    · simp [q]
    · simp [p]
    · simp [e]
  have hp : Etale (pullback.snd p W.ι) := by
    apply (MorphismProperty.cancel_left_of_respectsIso @Etale
      (isPullback_morphismRestrict p W).flip.isoPullback.hom _).mp
    simpa only [IsPullback.isoPullback_hom_snd] using hEt
  have hq : Etale (q ≫ e.inv) := by
    rw [← H'.isoPullback_hom_snd]
    infer_instance
  have : Etale q :=
    (MorphismProperty.cancel_right_of_respectsIso @Etale q e.inv).mp hq
  have : Etale (Spec.map (η.app (op V))) :=
    (MorphismProperty.cancel_right_of_respectsIso @Etale
      (Spec.map (η.app (op V))) hV.isoSpec.inv).mp ‹Etale q›
  exact ⟨hV, (HasRingHomProperty.Spec_iff (P := @Etale)).mp inferInstance⟩

include hcart in
/-- Actual target-stalk etaleness gives a good affine neighborhood in the
ambient scheme, via the original section restriction square. -/
theorem exists_goodOpen_of_etale_stalkBaseChange
    (U : X.Opens) (hU : IsAffineOpen U) (x : U.toScheme)
    [IsFinite (toOpen F η U hU)] [LocallyOfFinitePresentation (toOpen F η U hU)]
    (hx : Etale (pullback.snd (toOpen F η U hU) (U.toScheme.fromSpecStalk x))) :
    ∃ V : X.Opens, IsGood F η V ∧ x.val ∈ V ∧ V ≤ U := by
  obtain ⟨W, hW, hxW, _, hEt⟩ :=
    (toOpen F η U hU).exists_affine_etale_target_neighborhood_of_finite x hx ⊤ trivial
  exact ⟨U.ι ''ᵁ W, isGood_image F η hcart hU W hW hEt,
    ⟨x, hxW, rfl⟩, U.ι_image_le W⟩

include hcart in
/-- Finite section algebras whose stalk base changes are etale at the
closed fibre give a good affine basis covering the whole proper model. -/
theorem goodOpen_cover_of_etale_closedFiber_stalks
    {R : Type u} [CommRing R] [IsLocalRing R]
    (f : X ⟶ Spec (.of R)) [UniversallyClosed f]
    (hfinite : ∀ (U : X.Opens) (hU : IsAffineOpen U), IsFinite (toOpen F η U hU))
    (hfp : ∀ (U : X.Opens) (hU : IsAffineOpen U),
      LocallyOfFinitePresentation (toOpen F η U hU))
    (hstalk : ∀ x ∈ Set.range (LocalRing.ResidueFiber.projection f),
      ∃ (U : X.Opens) (hU : IsAffineOpen U) (hxU : x ∈ U),
        Etale (pullback.snd (toOpen F η U hU)
          (U.toScheme.fromSpecStalk ⟨x, hxU⟩))) :
    ∀ x : X, ∃ U, IsGood F η U ∧ x ∈ U := by
  apply goodOpen_cover_of_closedFiber F η f
  intro x hx
  obtain ⟨U, hU, hxU, hEt⟩ := hstalk x hx
  have := hfinite U hU
  have := hfp U hU
  obtain ⟨V, hV, hxV, _⟩ :=
    exists_goodOpen_of_etale_stalkBaseChange F η hcart U hU ⟨x, hxU⟩ hEt
  exact ⟨V, hV, hxV⟩

end AlgebraicGeometry.Scheme.FiniteEtale.AffineAlgebraGluing
