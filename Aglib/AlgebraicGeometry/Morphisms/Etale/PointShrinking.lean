/-
Copyright (c) 2026 kangxyz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.Morphisms.FormallyUnramified.Immersions
public import Mathlib.AlgebraicGeometry.Morphisms.Etale
public import Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion
public import Mathlib.AlgebraicGeometry.IdealSheaf.Functorial
public import Mathlib.AlgebraicGeometry.PullbackCarrier

/-!
# Actual pointed etale shrinking

Source: `lean/R5Lab/Aglib/AlgebraicGeometry/Morphisms/Etale/PointShrinking.lean`.
Frozen R5 revision: `f8a3314ddecffcada2ec721d26d56a937bed9690`.
SHA-256: `ba1c14bf2c4d53a4af740ff6a13caf40172c01f8386d6316c65fcf7c7fe498a6`.
Native objects and proved suppliers replace application provenance and redundant premises.
-/

@[expose] public section


open CategoryTheory Limits AlgebraicGeometry Polynomial
open scoped Polynomial
universe u

section EtalePointShrinking


noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory Limits AlgebraicGeometry TopologicalSpace
namespace AlgebraicGeometry.Etale.PointShrinking

lemma section_openImmersion {P E : Scheme.{u}} (s : P ⟶ E) (t : E ⟶ P)
    [Etale t] (h : s ≫ t = 𝟙 P) : IsOpenImmersion s :=
  IsOpenImmersion.of_section_formallyUnramified s t h

variable {P X Y : Scheme.{u}} (p : P ⟶ X) (f : X ⟶ Y) (q : P ⟶ Y)
  (h : p ≫ f = q)

/-- The actual rational section in the full closed fibre. -/
def fiberSection : P ⟶ pullback f q := pullback.lift p (𝟙 P) (by simpa using h)

-- Retain the etale-map and closed-centre guards of the original full-fibre shrinking interface;
-- the first projection equation is the formal pullback identity.
@[nolint unusedArguments, reassoc (attr := simp)]
lemma fiberSection_fst [Etale f] [IsClosedImmersion q] :
    fiberSection p f q h ≫ pullback.fst f q = p := by
  simp [fiberSection]
-- Retain the etale-map and closed-centre guards of the original rational fibre-section
-- interface; the second projection equation is the formal pullback identity.
@[nolint unusedArguments, reassoc (attr := simp)]
lemma fiberSection_snd [Etale f] [IsClosedImmersion q] :
    fiberSection p f q h ≫ pullback.snd f q = 𝟙 P := by
  simp [fiberSection]

variable [Etale f] [IsClosedImmersion q]

instance fiberSection_open : IsOpenImmersion (fiberSection p f q h) :=
  section_openImmersion _ (pullback.snd f q) (fiberSection_snd p f q h)

/-- Remove the entire complementary closed subset of the full closed fibre. -/
def shrinkOpen : X.Opens :=
  ⟨(pullback.fst f q '' (Set.range (fiberSection p f q h))ᶜ)ᶜ,
    ((pullback.fst f q).isClosedMap _
      (fiberSection p f q h).isOpenEmbedding.isOpen_range.isClosed_compl).isOpen_compl⟩

lemma fiber_preimage_shrinkOpen :
    (pullback.fst f q) ⁻¹ᵁ shrinkOpen p f q h = (fiberSection p f q h).opensRange := by
  ext z
  change (pullback.fst f q) z ∉
    pullback.fst f q '' (Set.range (fiberSection p f q h))ᶜ ↔ _
  rw [(pullback.fst f q).isClosedEmbedding.injective.mem_set_image]
  exact not_not

lemma range_subset_shrinkOpen : Set.range p ⊆ shrinkOpen p f q h := by
  rintro _ ⟨z, rfl⟩
  have hz : fiberSection p f q h z ∈ (pullback.fst f q) ⁻¹ᵁ shrinkOpen p f q h := by
    rw [fiber_preimage_shrinkOpen]
    exact ⟨z, rfl⟩
  change (pullback.fst f q) (fiberSection p f q h z) ∈ shrinkOpen p f q h at hz
  rw [← Scheme.Hom.comp_apply, fiberSection_fst] at hz
  exact hz

variable (U : X.Opens) (hpU : Set.range p ⊆ U) (hU : U ≤ shrinkOpen p f q h)

/-- The same point factored through the retained actual open subset. -/
def restrictedPoint : P ⟶ U.toScheme :=
  IsOpenImmersion.lift U.ι p (by simpa only [Scheme.Opens.range_ι] using hpU)

@[reassoc (attr := simp)] lemma restrictedPoint_triangle :
    restrictedPoint p U hpU ≫ U.ι = p := IsOpenImmersion.lift_fac _ _ _

include h hpU hU

lemma fiber_preimage_subopen : (pullback.fst f q) ⁻¹ᵁ U = (fiberSection p f q h).opensRange := by
  apply le_antisymm
  · exact ((pullback.fst f q).preimage_mono hU).trans_eq (fiber_preimage_shrinkOpen p f q h)
  · rintro _ ⟨z, rfl⟩
    change (pullback.fst f q) (fiberSection p f q h z) ∈ U
    rw [← Scheme.Hom.comp_apply, fiberSection_fst]
    exact hpU (Set.mem_range_self z)

/-- The FULL inverse-image closed subscheme on U is exactly P, by an actual
cartesian square. This is stronger than equality of supports. -/
lemma point_isPullback :
    IsPullback (restrictedPoint p U hpU) (𝟙 P) (U.ι ≫ f) q := by
  have H : IsPullback (restrictedPoint p U hpU) (fiberSection p f q h)
      U.ι (pullback.fst f q) :=
    IsOpenImmersion.isPullback _ _ _ _
      (by simp only [fiberSection_fst, restrictedPoint_triangle])
      (by simpa only [Scheme.Opens.opensRange_ι] using fiber_preimage_subopen p f q h U hpU hU)
  simpa only [fiberSection_snd] using H.paste_vert (IsPullback.of_hasPullback f q)

lemma restrictedPoint_closedImmersion : IsClosedImmersion (restrictedPoint p U hpU) :=
  MorphismProperty.of_isPullback (P := @IsClosedImmersion)
    (point_isPullback p f q h U hpU hU).flip inferInstance

/-- Exact ideal-sheaf equality follows from the proved cartesian centre square. -/
lemma centre_comap : q.ker.comap (U.ι ≫ f) = (restrictedPoint p U hpU).ker := by
  let H := point_isPullback p f q h U hpU hU
  rw [← Scheme.IdealSheafData.ker_fst_of_isClosedImmersion,
    ← Scheme.Hom.ker_comp_of_isIso H.isoPullback.hom, H.isoPullback_hom_fst]

end AlgebraicGeometry.Etale.PointShrinking

end
end EtalePointShrinking

section CommonPointShrinking


noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory Limits AlgebraicGeometry
namespace AlgebraicGeometry.Etale.PointShrinking.Common
variable {P X Y Z : Scheme.{u}} (p : P ⟶ X)
  (f : X ⟶ Y) (q : P ⟶ Y) (h : p ≫ f = q)
  (g : X ⟶ Z) (r : P ⟶ Z) (k : p ≫ g = r)
  [Etale f] [Etale g] [IsClosedImmersion q] [IsClosedImmersion r]

/-- The intersection of the two actual shrinking neighborhoods, retaining both closed-fibre
sections. -/
def commonOpen : X.Opens := shrinkOpen p f q h ⊓ shrinkOpen p g r k

lemma contains : Set.range p ⊆ commonOpen p f q h g r k := by
  intro x hx
  exact ⟨range_subset_shrinkOpen p f q h hx, range_subset_shrinkOpen p g r k hx⟩

/-- The original map p factored through the common open neighborhood. -/
def point : P ⟶ (commonOpen p f q h g r k).toScheme :=
  restrictedPoint p _ (contains p f q h g r k)

@[reassoc (attr := simp)] lemma point_triangle :
    point p f q h g r k ≫ (commonOpen p f q h g r k).ι = p :=
  restrictedPoint_triangle _ _ _

/-- Restrict the original etale map f to the same common open neighborhood. -/
def toLeft : (commonOpen p f q h g r k).toScheme ⟶ Y :=
  (commonOpen p f q h g r k).ι ≫ f

/-- Restrict the original etale map g to the same common open neighborhood. -/
def toRight : (commonOpen p f q h g r k).toScheme ⟶ Z :=
  (commonOpen p f q h g r k).ι ≫ g

instance toLeft_etale : Etale (toLeft p f q h g r k) := by dsimp [toLeft]; infer_instance
instance toRight_etale : Etale (toRight p f q h g r k) := by dsimp [toRight]; infer_instance

lemma left_isPullback : IsPullback (point p f q h g r k) (𝟙 P) (toLeft p f q h g r k) q :=
  point_isPullback p f q h _ (contains p f q h g r k) inf_le_left

lemma right_isPullback : IsPullback (point p f q h g r k) (𝟙 P) (toRight p f q h g r k) r :=
  point_isPullback p g r k _ (contains p f q h g r k) inf_le_right

instance point_closedImmersion : IsClosedImmersion (point p f q h g r k) :=
  restrictedPoint_closedImmersion p f q h _ (contains p f q h g r k) inf_le_left

/-- The kernel ideal sheaf of the actual point factored through the common open neighborhood. -/
def center : (commonOpen p f q h g r k).toScheme.IdealSheafData :=
  (point p f q h g r k).ker

lemma left_center : q.ker.comap (toLeft p f q h g r k) = center p f q h g r k :=
  centre_comap p f q h _ (contains p f q h g r k) inf_le_left

lemma right_center : r.ker.comap (toRight p f q h g r k) = center p f q h g r k :=
  centre_comap p g r k _ (contains p f q h g r k) inf_le_right

lemma center_eq : q.ker.comap (toLeft p f q h g r k) = r.ker.comap (toRight p f q h g r k) :=
  (left_center p f q h g r k).trans (right_center p f q h g r k).symm

end AlgebraicGeometry.Etale.PointShrinking.Common

end
end CommonPointShrinking
