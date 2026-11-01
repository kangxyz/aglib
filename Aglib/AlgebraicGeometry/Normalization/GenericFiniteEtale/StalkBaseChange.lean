/-
Copyright (c) 2026 kangxyz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.Normalization.GenericFiniteEtale.FlatPreimmersionBaseChange

/-! # Original generic normalization at an actual target stalk

The comparison recognizes the unchanged normal pullback by its original open
cover. No smoothness or finite-presentation hypothesis is placed on the stalk
map, and no second generic-field or normalization model is introduced.
-/

@[expose] public noncomputable section

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry.Scheme.FiniteEtale.GenericNormalization.OpenRecovery

universe u

variable {X U V : Scheme.{u}} [IsIntegral X] [IsLocallyNoetherian X]
  [∀ x : X, IsIntegrallyClosed (X.presheaf.stalk x)] [IsIntegral U] [IsIntegral V]
  (j : U ⟶ X) [IsOpenImmersion j] (x : X)
  (jR : V ⟶ Spec (X.presheaf.stalk x)) [IsOpenImmersion jR]
  (g : V ⟶ U) (H : IsPullback g jR j (X.fromSpecStalk x))
  (Y : FiniteEtale U) [IsIntegral Y.obj.left]

local notation "q" => genericMap j Y.obj.hom
local notation "b" => X.fromSpecStalk x
local notation "pR" => pullback.snd Y.obj.hom g

omit [IsLocallyNoetherian X] [∀ x : X, IsIntegrallyClosed (X.presheaf.stalk x)] in
/-- The actual target-stalk spectrum contains the original generic point. -/
theorem stalk_generic_mem_range : genericPoint X ∈ Set.range b := by
  rw [Scheme.range_fromSpecStalk]
  exact (genericPoint_spec X).specializes trivial

local instance : Flat b := Scheme.fromSpecStalk_flat X x

omit [IsLocallyNoetherian X] [∀ x : X, IsIntegrallyClosed (X.presheaf.stalk x)]
  [IsIntegral V] [IsOpenImmersion jR] in
include H in
/-- The original generic point belongs to the image of the actual restricted
stalk map. This does not assert local finite presentation. -/
theorem stalkComplement_generic_mem_range : genericPoint U ∈ Set.range g :=
  flatPreimmersionComplement_generic_mem_range j b (stalk_generic_mem_range x) jR g H

omit [IsLocallyNoetherian X] [∀ x : X, IsIntegrallyClosed (X.presheaf.stalk x)]
  [IsIntegral V] [IsOpenImmersion jR] in
include H in
/-- The literal restricted cover is integral. -/
theorem stalkBaseChange_cover_isIntegral :
    IsIntegral ((FiniteEtale.baseChange g).obj Y).obj.left :=
  flatPreimmersionBaseChange_cover_isIntegral j b (stalk_generic_mem_range x) jR g H Y

/-- The actual open-cover map into the original target-stalk pullback. -/
def stalkBaseChangeInclusion :
    pullback Y.obj.hom g ⟶ pullback (q).fromNormalization b :=
  flatPreimmersionBaseChangeInclusion j b jR g H Y

omit [IsLocallyNoetherian X] [IsIntegral V] [IsOpenImmersion jR]
  [IsIntegral Y.obj.left] in
@[reassoc (attr := simp)] theorem stalkBaseChangeInclusion_fst :
    stalkBaseChangeInclusion j x jR g H Y ≫ pullback.fst (q).fromNormalization b =
      pullback.fst Y.obj.hom g ≫ inclusion j Y.obj.hom :=
  flatPreimmersionBaseChangeInclusion_fst j b jR g H Y

omit [IsLocallyNoetherian X] [IsIntegral V] [IsOpenImmersion jR]
  [IsIntegral Y.obj.left] in
@[reassoc (attr := simp)] theorem stalkBaseChangeInclusion_snd :
    stalkBaseChangeInclusion j x jR g H Y ≫ pullback.snd (q).fromNormalization b =
      pR ≫ jR :=
  flatPreimmersionBaseChangeInclusion_snd j b jR g H Y

omit [IsLocallyNoetherian X] [IsIntegral V] [IsOpenImmersion jR]
  [IsIntegral Y.obj.left] in
/-- The same actual restricted cover is the base-open pullback of the unchanged
normalization's target-stalk pullback. -/
theorem stalkBaseChangeInclusion_isPullback :
    IsPullback (stalkBaseChangeInclusion j x jR g H Y) pR
      (pullback.snd (q).fromNormalization b) jR :=
  flatPreimmersionBaseChangeInclusion_isPullback j b jR g H Y

/-- The original normalization pullback has integral normal source. -/
theorem stalkBaseChange_integral_normal :
    IsIntegral (pullback (q).fromNormalization b) ∧
      NormalStalks (pullback (q).fromNormalization b) :=
  flatPreimmersionBaseChange_integral_normal j b (stalk_generic_mem_range x) Y

local instance stalkBaseChange_targetIntegral : IsIntegral (pullback (q).fromNormalization b) :=
  (stalkBaseChange_integral_normal j x Y).1

local instance stalkBaseChange_originalFinite : IsFinite (q).fromNormalization :=
  fromNormalization_isFinite j Y.obj.hom

local instance stalkBaseChange_inclusionOpen :
    IsOpenImmersion (stalkBaseChangeInclusion j x jR g H Y) :=
  MorphismProperty.of_isPullback (stalkBaseChangeInclusion_isPullback j x jR g H Y).flip
    inferInstance

/-- The comparison is constructed from the actual dense open and normal
pullback; it is not a normalization base-change hypothesis. -/
def stalkBaseChangeIso :
    (genericMap jR pR).normalization ≅ pullback (q).fromNormalization b :=
  flatPreimmersionBaseChangeIso j b (stalk_generic_mem_range x) jR g H Y

@[reassoc (attr := simp)] theorem stalkBaseChangeIso_hom_over :
    (stalkBaseChangeIso j x jR g H Y).hom ≫ pullback.snd (q).fromNormalization b =
      (genericMap jR pR).fromNormalization :=
  flatPreimmersionBaseChangeIso_hom_over j b (stalk_generic_mem_range x) jR g H Y

@[reassoc (attr := simp)] theorem stalkBaseChangeIso_hom_generic :
    (genericMap jR pR).toNormalization ≫ (stalkBaseChangeIso j x jR g H Y).hom =
      genericToCover jR pR ≫ stalkBaseChangeInclusion j x jR g H Y :=
  flatPreimmersionBaseChangeIso_hom_generic j b (stalk_generic_mem_range x) jR g H Y

local instance stalkBaseChange_baseNormal :
    ∀ z : Spec (X.presheaf.stalk x),
      IsIntegrallyClosed ((Spec (X.presheaf.stalk x)).presheaf.stalk z) :=
  fun z => (isIntegrallyClosed_and_isDomain_stalk_Spec (X.presheaf.stalk x) z).1

/-- The original covering-source comparison is retained on the nose. -/
@[reassoc (attr := simp)] theorem inclusion_stalkBaseChangeIso_hom :
    inclusion jR pR ≫ (stalkBaseChangeIso j x jR g H Y).hom =
      stalkBaseChangeInclusion j x jR g H Y :=
  inclusion_flatPreimmersionBaseChangeIso_hom j b (stalk_generic_mem_range x) jR g H Y

omit [IsLocallyNoetherian X] [∀ x : X, IsIntegrallyClosed (X.presheaf.stalk x)]
  [IsOpenImmersion jR] in
include H in
/-- Connected base change retains Galoisness and the exact original deck order. -/
theorem stalkBaseChange_galois_card [CategoryTheory.PreGaloisCategory.IsGalois Y] :
    CategoryTheory.PreGaloisCategory.IsGalois ((FiniteEtale.baseChange g).obj Y) ∧
      Nat.card (Aut ((FiniteEtale.baseChange g).obj Y)) = Nat.card (Aut Y) :=
  flatPreimmersionBaseChange_galois_card j b (stalk_generic_mem_range x) jR g H Y

/-- The original whole section, not a newly chosen point, determines the local
section and its original closed-point comparison. -/
theorem exists_stalkBaseChangeSection {D : Type u} [CommRing D] [IsLocalRing D]
    (s : Spec (.of D) ⟶ (q).normalization)
    (r : Spec (.of D) ⟶ Spec (X.presheaf.stalk x))
    (hs : s ≫ (q).fromNormalization = r ≫ b) :
    ∃ sR : Spec (.of D) ⟶ (genericMap jR pR).normalization,
      sR ≫ (genericMap jR pR).fromNormalization = r ∧
      sR ≫ (stalkBaseChangeIso j x jR g H Y).hom ≫
        pullback.fst (q).fromNormalization b = s ∧
      ((stalkBaseChangeIso j x jR g H Y).hom ≫
        pullback.fst (q).fromNormalization b) (sR (IsLocalRing.closedPoint D)) =
          s (IsLocalRing.closedPoint D) :=
  exists_flatPreimmersionBaseChangeSection j b (stalk_generic_mem_range x) jR g H Y s r hs

end AlgebraicGeometry.Scheme.FiniteEtale.GenericNormalization.OpenRecovery
