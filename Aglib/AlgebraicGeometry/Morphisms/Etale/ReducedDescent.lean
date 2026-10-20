/-
Copyright (c) 2026 kangxyz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.Morphisms.Etale.Reduced
public import Aglib.AlgebraicGeometry.Morphisms.Smooth.Reduced
public import Mathlib.AlgebraicGeometry.Morphisms.Etale
public import Aglib.AlgebraicGeometry.Morphisms.Flat.GenericFiberCriteria

/-!
# Reduced flat charts and literal base changes

Source: `lean/R5Lab/Aglib/AlgebraicGeometry/Morphisms/Etale/ReducedDescent.lean`.
Frozen R5 revision: `f8a3314ddecffcada2ec721d26d56a937bed9690`.
SHA-256: `2e5fb28af59c0cbddc8e881980798898af4a58216f99cb417afaef199b888d7b`.
Native objects and proved suppliers replace application provenance and redundant premises.
-/

@[expose] public section


noncomputable section
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory Limits AlgebraicGeometry
universe u v

section AlgebraicGeometry.Scheme

noncomputable section
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory Limits AlgebraicGeometry
namespace AlgebraicGeometry.Scheme

/-- Reducedness descends at an actual point through the injective stalk
homomorphism of an actual flat chart. -/
theorem reduced_stalk_of_flat_chart {X Y : Scheme.{u}} (g : Y ⟶ X)
    [Flat g] [IsReduced Y] (y : Y) : _root_.IsReduced (X.presheaf.stalk (g y)) :=
  _root_.isReduced_of_injective (g.stalkMap y).hom
    (AlgebraicGeometry.Flat.flat_stalkMap_injective g y)

/-- A genuinely covering pointwise family of reduced flat charts proves
reducedness of the same target scheme. -/
theorem reduced_of_pointwise_flat_cover (X : Scheme.{u})
    (hcover : ∀ x : X, ∃ (Y : Scheme.{u}) (g : Y ⟶ X) (y : Y),
      g y = x ∧ Flat g ∧ IsReduced Y) : IsReduced X := by
  have (x : X) : _root_.IsReduced (X.presheaf.stalk x) := by
    obtain ⟨Y, g, y, rfl, hg, hY⟩ := hcover x
    let := hg
    let := hY
    exact reduced_stalk_of_flat_chart g y
  exact isReduced_of_isReduced_stalk X

end AlgebraicGeometry.Scheme

end -- noncomputable section
end AlgebraicGeometry.Scheme

section ReducedFibreBaseChange

noncomputable section
open CategoryTheory Limits AlgebraicGeometry
namespace AlgebraicGeometry.Scheme
variable {X Y B K : Scheme.{u}} (f : X ⟶ Y) (b : Y ⟶ B) (r : K ⟶ B)

/-- The map between the two base changes induced by the morphism `f` over `B`. -/
def baseChangeMap : pullback (f ≫ b) r ⟶ pullback b r :=
  (pullbackRightPullbackFstIso b r f).inv ≫ pullback.snd f (pullback.fst b r)

@[reassoc (attr := simp)] lemma baseChangeMap_fst :
    baseChangeMap f b r ≫ pullback.fst b r = pullback.fst (f ≫ b) r ≫ f := by
  simp [baseChangeMap]

@[reassoc (attr := simp)] lemma baseChangeMap_snd :
    baseChangeMap f b r ≫ pullback.snd b r = pullback.snd (f ≫ b) r := by
  simp [baseChangeMap]

lemma baseChangeMap_isPullback :
    IsPullback (pullback.fst (f ≫ b) r) (baseChangeMap f b r) f (pullback.fst b r) := by
  apply IsPullback.of_iso_pullback ⟨(baseChangeMap_fst f b r).symm⟩
    (pullbackRightPullbackFstIso b r f).symm
  · simp
  · rfl

instance baseChangeMap_etale [Etale f] : Etale (baseChangeMap f b r) := by
  dsimp [baseChangeMap]
  infer_instance

lemma isReduced_baseChange [Etale f] [IsReduced (pullback b r)]
    [IsLocallyNoetherian (pullback b r)] : IsReduced (pullback (f ≫ b) r) :=
  Etale.isReduced (baseChangeMap f b r)

/-- An actual structure-map equality transports reducedness without replacing
or merely matching the support of either coefficient fibre. -/
lemma isReduced_baseChange_of_comp_eq [Etale f] [IsReduced (pullback b r)]
    [IsLocallyNoetherian (pullback b r)] (a : X ⟶ B) (h : a = f ≫ b) :
    IsReduced (pullback a r) := by
  subst a
  exact isReduced_baseChange f b r

end AlgebraicGeometry.Scheme

end -- noncomputable section
end ReducedFibreBaseChange
