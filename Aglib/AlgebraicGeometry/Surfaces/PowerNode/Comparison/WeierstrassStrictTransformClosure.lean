/-
Copyright (c) 2026 kangxyz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.Surfaces.PowerNode.Comparison.StrictTransformClosure
public import Aglib.AlgebraicGeometry.Surfaces.PowerNode.Comparison.WeierstrassExceptional
public import Aglib.AlgebraicGeometry.EllipticCurve.Weierstrass.ResidueFiber

/-!
Native extraction from the R5 local-model source
`CyclicModelComparison.StrictTransformClosure`.
R5 revision: `f8a3314ddecffcada2ec721d26d56a937bed9690`.
Source SHA-256:
`5933a29200aaaa2ea2da9f33a05e06372d03ad6b9c19af9a44048bd25fe432c2`.
Original Weierstrass sections source20–192 and539–810 only: the actual unchanged punctured open,
  its canonical scheme-theoretic image, strict/exceptional coverage and strict-component
  maximality. The final fibre is transparently the shared literal residue pullback; all original
  equation, chart, DVR and four blowup-family premises remain explicit.
Conditional blowup families remain explicit inputs.
-/

@[expose] public section

open CategoryTheory Limits AlgebraicGeometry Polynomial
open scoped Polynomial
open AlgebraicGeometry.Scheme AlgebraicGeometry.Scheme.PowerNode
open AlgebraicGeometry.Scheme.Hom.Range AlgebraicGeometry.Scheme.Pullback.Fibre

section WeierstrassStrictTransform

/-! The genuine strict transform in the literal special fibre of the SAME
finite pointed modification. Its punctured open is the actual inverse image
of the original special cubic minus the original residue node. -/
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory Limits AlgebraicGeometry AlgebraicGeometry.Scheme.Blowup IsLocalRing
open WeierstrassCurve.CriticalNeighborhood WeierstrassCurve.Projective
universe u
namespace AlgebraicGeometry.Scheme.PowerNode.PointedEtale

variable {R : Type u} [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]
  {W : WeierstrassCurve R} {x y : ResidueField R}
variable (M : WeierstrassCurve.CriticalNeighborhood W x y) (π : R) (hπ : Irreducible π) (n : ℕ)
  (hn : 0 < n)
  (a : M.Carrierˣ) (ha : M.translated.a₆ = (a : M.Carrier) * algebraMap R M.Carrier (π ^ n))
  (he : (W.map (IsLocalRing.residue R)).toAffine.Equation x y)
  (ρ : ResidueField R) (hρ : WeierstrassCurve.CriticalNeighborhood.SplitTangent (W := W) (x := x)
    (y := y) ρ)
  (hex : NoetherianBlowupExistence.{u}) (hp : NoetherianBlowupProper.{u})
  (hatlas : BlowupAffineAtlas.{u}) (hbc : BlowupFlatBaseChange.{u})
local notation "f" => modification M π hπ n hn a ha he ρ hρ hex hp hatlas hbc
local notation "r" => Spec.map (CommRingCat.ofHom (IsLocalRing.residue R))

/-- The literal closed fibre of the same Run source and structural map. -/
abbrev finalSpecialFibre : Scheme.{u} :=
  Scheme.LocalRing.ResidueFiber.obj (f ≫ structureMap W)

/-- The morphism from the modification's residue-field fibre to the original Weierstrass special
fibre. -/
def finalSpecialMap : finalSpecialFibre M π hπ n hn a ha he ρ hρ hex hp hatlas hbc ⟶ specialFibre
  W :=
  (pullbackRightPullbackFstIso (structureMap W) r f).inv ≫ pullback.snd f (pullback.fst
    (structureMap W) r)

@[reassoc (attr := simp)] lemma finalSpecialMap_fst :
    finalSpecialMap M π hπ n hn a ha he ρ hρ hex hp hatlas hbc ≫ pullback.fst _ _ =
      pullback.fst _ _ ≫ f := by simp [finalSpecialMap]
@[reassoc (attr := simp)] lemma finalSpecialMap_snd :
    finalSpecialMap M π hπ n hn a ha he ρ hρ hex hp hatlas hbc ≫ pullback.snd _ _ = pullback.snd _
      _ := by
  simp [finalSpecialMap]

lemma finalSpecialMap_square :
    IsPullback (pullback.fst (f ≫ structureMap W) r)
      (finalSpecialMap M π hπ n hn a ha he ρ hρ hex hp hatlas hbc) f
      (pullback.fst (structureMap W) r) := by
  apply IsPullback.of_iso_pullback ⟨(finalSpecialMap_fst M π hπ n hn a ha he ρ hρ hex hp hatlas
    hbc).symm⟩
    (pullbackRightPullbackFstIso (structureMap W) r f).symm
  · simp
  · rfl

/-- The original cubic with the actual original residue node removed. -/
def originalPuncturedOpen : (specialFibre W).Opens :=
  pullback.fst (structureMap W) r ⁻¹ᵁ residueNodeComplement W x y he

/-- The actual inverse-image open in the SAME final special fibre. -/
def strictPuncturedOpen : (finalSpecialFibre M π hπ n hn a ha he ρ hρ hex hp hatlas hbc).Opens :=
  finalSpecialMap M π hπ n hn a ha he ρ hρ hex hp hatlas hbc ⁻¹ᵁ originalPuncturedOpen he

instance strictPunctured_unchanged : IsIso
    (finalSpecialMap M π hπ n hn a ha he ρ hρ hex hp hatlas hbc ∣_ originalPuncturedOpen he) :=
  Scheme.Hom.isIso_restrict_of_isPullback
    (finalSpecialMap_square M π hπ n hn a ha he ρ hρ hex hp hatlas hbc).flip _

/-- Nonemptiness uses the actual infinity section, which avoids the affine node. -/
lemma originalPunctured_nonempty : Nonempty (originalPuncturedOpen he).toScheme := by
  let s : Spec (.of (ResidueField R)) ⟶ specialFibre W :=
    pullback.lift (r ≫ infinitySection W) (𝟙 _) (by simp [Category.assoc,
      infinitySection_structure])
  refine ⟨⟨s (closedPoint (ResidueField R)), ?_⟩⟩
  change pullback.fst (structureMap W) r (s (closedPoint (ResidueField R))) ∈
    residueNodeComplement W x y he
  have hs : s ≫ pullback.fst (structureMap W) r = r ≫ infinitySection W := by simp [s]
  change (s ≫ pullback.fst (structureMap W) r) _ ∈ _
  rw [hs]
  exact infinitySection_range_subset_nodeComplement W x y he ⟨r (closedPoint (ResidueField R)), rfl⟩

instance originalPunctured_integral : IsIntegral (originalPuncturedOpen he).toScheme := by
  let := specialFibre_isIntegral W
  let := originalPunctured_nonempty he
  exact isIntegral_of_isOpenImmersion (originalPuncturedOpen he).ι

instance strictPunctured_integral : IsIntegral
    (strictPuncturedOpen M π hπ n hn a ha he ρ hρ hex hp hatlas hbc).toScheme :=
  IsIntegral.of_isIso (inv (finalSpecialMap M π hπ n hn a ha he ρ hρ hex hp hatlas hbc ∣_
    originalPuncturedOpen he))

instance finalSpecialFibre_noetherian : IsLocallyNoetherian
    (finalSpecialFibre M π hπ n hn a ha he ρ hρ hex hp hatlas hbc) := by
  have : IsClosedImmersion r :=
    IsClosedImmersion.spec_of_surjective _ (IsLocalRing.residue_surjective (R := R))
  exact LocallyOfFiniteType.isLocallyNoetherian (pullback.fst (f ≫ structureMap W) r)

/-- The genuine reduced closed strict transform, constructed as the image of
its integral punctured open, and proved to have exactly the closure support. -/
abbrev strictTransform : Scheme.{u} :=
  AlgebraicGeometry.Scheme.Hom.image (strictPuncturedOpen M π hπ n hn a ha he ρ hρ hex hp hatlas
    hbc).ι

/-- The scheme-theoretic image inclusion of the strict punctured open into the final special
fibre. -/
abbrev strictTransformInclusion : strictTransform M π hπ n hn a ha he ρ hρ hex hp hatlas hbc ⟶
    finalSpecialFibre M π hπ n hn a ha he ρ hρ hex hp hatlas hbc :=
  AlgebraicGeometry.Scheme.Hom.imageι (strictPuncturedOpen M π hπ n hn a ha he ρ hρ hex hp hatlas
    hbc).ι

instance strictTransform_integral : IsIntegral (strictTransform M π hπ n hn a ha he ρ hρ hex hp
  hatlas hbc) :=
  inferInstanceAs (IsIntegral (AlgebraicGeometry.Scheme.Hom.image
    (strictPuncturedOpen M π hπ n hn a ha he ρ hρ hex hp hatlas hbc).ι))

lemma strictTransform_support : Set.range (strictTransformInclusion M π hπ n hn a ha he ρ hρ hex
  hp hatlas hbc) =
    closure (strictPuncturedOpen M π hπ n hn a ha he ρ hρ hex hp hatlas hbc : Set _) := by
  simpa only [Scheme.Opens.range_ι] using AlgebraicGeometry.Scheme.Hom.Image.inclusion_range
    (strictPuncturedOpen M π hπ n hn a ha he ρ hρ hex hp hatlas hbc).ι

instance strictTransform_proper : IsProper
    (strictTransformInclusion M π hπ n hn a ha he ρ hρ hex hp hatlas hbc ≫ pullback.snd (f ≫
      structureMap W) r) := by
  infer_instance

end AlgebraicGeometry.Scheme.PowerNode.PointedEtale

end -- noncomputable section
end WeierstrassStrictTransform

section WeierstrassPunctureAvoidance

/-! The literal punctured open in the same final special fibre maps into
its original residue-node complement. In particular, its total-scheme image
is disjoint from the actual original point map, with no additional premise. -/
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory Limits AlgebraicGeometry AlgebraicGeometry.Scheme.Blowup IsLocalRing
open WeierstrassCurve.CriticalNeighborhood WeierstrassCurve.Projective
universe u
namespace AlgebraicGeometry.Scheme.PowerNode.PointedEtale
variable {R : Type u} [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]
  {W : WeierstrassCurve R} {x y : ResidueField R}
variable (M : WeierstrassCurve.CriticalNeighborhood W x y) (π : R) (hπ : Irreducible π) (n : ℕ)
  (hn : 0 < n)
  (a : M.Carrierˣ) (ha : M.translated.a₆ = (a : M.Carrier) * algebraMap R M.Carrier (π ^ n))
  (he : (W.map (IsLocalRing.residue R)).toAffine.Equation x y)
  (ρ : ResidueField R) (hρ : WeierstrassCurve.CriticalNeighborhood.SplitTangent (W := W) (x := x)
    (y := y) ρ)
  (hex : NoetherianBlowupExistence.{u}) (hp : NoetherianBlowupProper.{u})
  (hatlas : BlowupAffineAtlas.{u}) (hbc : BlowupFlatBaseChange.{u})
local notation "f" => modification M π hπ n hn a ha he ρ hρ hex hp hatlas hbc
local notation "r" => Spec.map (CommRingCat.ofHom (IsLocalRing.residue R))
local notation "Y" => finalSpecialFibre M π hπ n hn a ha he ρ hρ hex hp hatlas hbc
local notation "V" => strictPuncturedOpen M π hπ n hn a ha he ρ hρ hex hp hatlas hbc
local notation "j" => Scheme.Opens.ι (X := Y) V
local notation "q" => finalSpecialMap M π hπ n hn a ha he ρ hρ hex hp hatlas hbc

/-- The punctured image lands in the complement in the ORIGINAL total scheme,
using exactly the structural triangle of the actual final special-fibre map. -/
lemma strictPunctured_original_range_subset :
    Set.range (j ≫ pullback.fst (f ≫ structureMap W) r ≫ f) ⊆
      (residueNodeComplement W x y he : Set (scheme W)) := by
  rintro _ ⟨z, rfl⟩
  have hz := z.property
  change (q ≫ pullback.fst (structureMap W) r) z.val ∈
    residueNodeComplement W x y he at hz
  rw [finalSpecialMap_fst] at hz
  exact hz

/-- No new disjointness hypothesis: the actual punctured open avoids the
range of the original residue point map after the actual modification. -/
lemma strictPunctured_original_disjoint :
    Disjoint (Set.range (j ≫ pullback.fst (f ≫ structureMap W) r ≫ f))
      (Set.range (residueNodeMap W x y he)) :=
  (originalComplement_disjoint he).mono_left
    (strictPunctured_original_range_subset M π hπ n hn a ha he ρ hρ hex hp hatlas hbc)

/-- The point in the preceding theorem is literally the initial pointed
chart's global point, the target needed by the first retained middle chart. -/
lemma strictPunctured_initialPoint_disjoint :
    Disjoint (Set.range (j ≫ pullback.fst (f ≫ structureMap W) r ≫ f))
      (Set.range (initialChart M π hπ n hn a ha he ρ hρ).globalPoint) :=
  strictPunctured_original_disjoint M π hπ n hn a ha he ρ hρ hex hp hatlas hbc

end AlgebraicGeometry.Scheme.PowerNode.PointedEtale

end -- noncomputable section
end WeierstrassPunctureAvoidance

section WeierstrassSpecialFibreCover

/-! Canonical exceptional map into the SAME final special fibre and actual
strict-plus-exceptional coverage. No P1, cycle, or irreducible-component
maximality assertion is used. -/
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory Limits AlgebraicGeometry AlgebraicGeometry.Scheme.Blowup IsLocalRing
open WeierstrassCurve.CriticalNeighborhood WeierstrassCurve.Projective
universe u
namespace AlgebraicGeometry.Scheme.PowerNode.PointedEtale
variable {R : Type u} [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]
  {W : WeierstrassCurve R} {x y : ResidueField R}
variable (M : WeierstrassCurve.CriticalNeighborhood W x y) (π : R) (hπ : Irreducible π) (n : ℕ)
  (hn : 0 < n)
  (a : M.Carrierˣ) (ha : M.translated.a₆ = (a : M.Carrier) * algebraMap R M.Carrier (π ^ n))
  (he : (W.map (IsLocalRing.residue R)).toAffine.Equation x y)
  (ρ : ResidueField R) (hρ : WeierstrassCurve.CriticalNeighborhood.SplitTangent (W := W) (x := x)
    (y := y) ρ)
  (hex : NoetherianBlowupExistence.{u}) (hp : NoetherianBlowupProper.{u})
  (hatlas : BlowupAffineAtlas.{u}) (hbc : BlowupFlatBaseChange.{u})
local notation "f" => modification M π hπ n hn a ha he ρ hρ hex hp hatlas hbc
local notation "r" => Spec.map (CommRingCat.ofHom (IsLocalRing.residue R))
local notation "EE" => Resolution.resolve π hπ hex hp hatlas n
local notation "p" => NextCenter.origin π hπ n hn
local notation "e" => originalExceptionalMap M π hπ n hn a ha he ρ hρ hex hp hatlas hbc
local notation "q" => finalSpecialMap M π hπ n hn a ha he ρ hρ hex hp hatlas hbc
local notation "i" => strictTransformInclusion M π hπ n hn a ha he ρ hρ hex hp hatlas hbc
local notation "V" => strictPuncturedOpen M π hπ n hn a ha he ρ hρ hex hp hatlas hbc

/-- Exact original-point-complement range, needed by the actual outer
closure chart comparison rather than only its disjointness direction. -/
lemma strictPunctured_original_range_eq :
    Set.range (Scheme.Opens.ι V) =
      (pullback.fst (f ≫ structureMap W) r ≫ f) ⁻¹'
        (Set.range (residueNodeMap W x y he))ᶜ := by
  rw [Scheme.Opens.range_ι]
  ext z
  change (q ≫ pullback.fst (structureMap W) r) z ≠ residueNode W x y he ↔ _
  rw [finalSpecialMap_fst]
  constructor
  · intro hz h
    obtain ⟨w, hw⟩ := h
    apply hz
    exact hw.symm.trans (congrArg (residueNodeMap W x y he)
      (Subsingleton.elim w (closedPoint (ResidueField R))))
  · intro hz h
    exact hz ⟨closedPoint (ResidueField R), h.symm⟩

/-- The literal original residue node in its own special fibre. -/
def originalSpecialNode : Spec (.of (ResidueField R)) ⟶ specialFibre W :=
  pullback.lift (residueNodeMap W x y he) (𝟙 _)
    (by simpa using residueNodeMap_structure W x y he)

@[reassoc (attr := simp)] lemma originalSpecialNode_fst :
    originalSpecialNode he ≫ pullback.fst (structureMap W) r = residueNodeMap W x y he :=
  pullback.lift_fst ..
@[reassoc (attr := simp)] lemma originalSpecialNode_snd :
    originalSpecialNode he ≫ pullback.snd (structureMap W) r = 𝟙 _ := pullback.lift_snd ..

/-- The whole actual exceptional scheme, with its existing original-residue
projection, mapped into the literal final special fibre. -/
def originalExceptionalToSpecial : pullback (EE).map p ⟶
    finalSpecialFibre M π hπ n hn a ha he ρ hρ hex hp hatlas hbc :=
  pullback.lift e (pullback.snd (EE).map p) (by
    rw [← Category.assoc, (originalExceptionalMap_square M π hπ n hn a ha he ρ hρ hex hp hatlas
      hbc).w,
      Category.assoc, residueNodeMap_structure])

@[reassoc (attr := simp)] lemma originalExceptionalToSpecial_fst :
    originalExceptionalToSpecial M π hπ n hn a ha he ρ hρ hex hp hatlas hbc ≫
      pullback.fst (f ≫ structureMap W) r = e := pullback.lift_fst ..
@[reassoc (attr := simp)] lemma originalExceptionalToSpecial_snd :
    originalExceptionalToSpecial M π hπ n hn a ha he ρ hρ hex hp hatlas hbc ≫
      pullback.snd (f ≫ structureMap W) r = pullback.snd (EE).map p := pullback.lift_snd ..

@[reassoc] lemma originalExceptionalToSpecial_original :
    originalExceptionalToSpecial M π hπ n hn a ha he ρ hρ hex hp hatlas hbc ≫ q =
      pullback.snd (EE).map p ≫ originalSpecialNode he := by
  apply pullback.hom_ext
  · simp only [Category.assoc, finalSpecialMap_fst, originalExceptionalToSpecial_fst_assoc,
      originalSpecialNode_fst]
    exact (originalExceptionalMap_square M π hπ n hn a ha he ρ hρ hex hp hatlas hbc).w
  · simp

lemma originalExceptionalToSpecial_square :
    IsPullback (originalExceptionalToSpecial M π hπ n hn a ha he ρ hρ hex hp hatlas hbc)
      (pullback.snd (EE).map p) q (originalSpecialNode he) := by
  have H : IsPullback
      (originalExceptionalToSpecial M π hπ n hn a ha he ρ hρ hex hp hatlas hbc ≫
        pullback.fst (f ≫ structureMap W) r)
      (pullback.snd (EE).map p) f
      (originalSpecialNode he ≫ pullback.fst (structureMap W) r) := by
    simpa only [originalExceptionalToSpecial_fst, originalSpecialNode_fst] using
      originalExceptionalMap_square M π hπ n hn a ha he ρ hρ hex hp hatlas hbc
  exact H.of_right (originalExceptionalToSpecial_original M π hπ n hn a ha he ρ hρ hex hp hatlas
    hbc)
    (finalSpecialMap_square M π hπ n hn a ha he ρ hρ hex hp hatlas hbc)

instance originalExceptionalToSpecial_closedImmersion : IsClosedImmersion
    (originalExceptionalToSpecial M π hπ n hn a ha he ρ hρ hex hp hatlas hbc) := by
  let : IsClosedImmersion (originalSpecialNode he) := by
    have : IsClosedImmersion (originalSpecialNode he ≫ pullback.fst (structureMap W) r) := by
      rw [originalSpecialNode_fst]
      infer_instance
    exact IsClosedImmersion.of_comp _ (pullback.fst (structureMap W) r)
  exact MorphismProperty.of_isPullback (P := @IsClosedImmersion)
    (originalExceptionalToSpecial_square M π hπ n hn a ha he ρ hρ hex hp hatlas hbc).flip
      inferInstance

/-- Actual support coverage of the SAME final fibre by the constructed strict
closure and the whole exceptional scheme, before classifying either one. -/
lemma strict_exceptional_special_cover
    (z : finalSpecialFibre M π hπ n hn a ha he ρ hρ hex hp hatlas hbc) :
    z ∈ Set.range i ∨ z ∈ Set.range
      (originalExceptionalToSpecial M π hπ n hn a ha he ρ hρ hex hp hatlas hbc) := by
  have : IsClosedImmersion r :=
    IsClosedImmersion.spec_of_surjective _ (IsLocalRing.residue_surjective (R := R))
  by_cases hz : (q ≫ pullback.fst (structureMap W) r) z ∈ Set.range (residueNodeMap W x y he)
  · right
    rw [Scheme.Pullback.Transport.range_eq_preimage_of_isPullback
      (originalExceptionalToSpecial_square M π hπ n hn a ha he ρ hρ hex hp hatlas hbc)]
    change q z ∈ Set.range (originalSpecialNode he)
    rw [← originalSpecialNode_fst he] at hz
    exact (map_mem_range_comp_iff _ _ (pullback.fst (structureMap W) r).injective (q z)).mp hz
  · left
    rw [strictTransform_support]
    apply subset_closure
    change (q ≫ pullback.fst (structureMap W) r) z ≠ residueNode W x y he
    intro h
    exact hz ⟨closedPoint (ResidueField R), h.symm⟩

end AlgebraicGeometry.Scheme.PowerNode.PointedEtale

end -- noncomputable section
end WeierstrassSpecialFibreCover

section WeierstrassExceptionalP1Cover

/-! Actual P1 maps into the same original Run's whole special fibre, and full
strict-plus-P1 coverage. Strict maximality is proved globally; exceptional
maximality in the whole fibre is deliberately not asserted here. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory Limits AlgebraicGeometry AlgebraicGeometry.Scheme.Blowup IsLocalRing
open WeierstrassCurve.CriticalNeighborhood WeierstrassCurve.Projective
open AlgebraicGeometry.Scheme.ProjectiveLine (projectiveP1)
universe u
namespace AlgebraicGeometry.Scheme.PowerNode.PointedEtale
variable {R : Type u} [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]
  {W : WeierstrassCurve R} {x y : ResidueField R}
variable (M : WeierstrassCurve.CriticalNeighborhood W x y) (π : R) (hπ : Irreducible π) (q : ℕ)
  (a : M.Carrierˣ) (ha : M.translated.a₆ = (a : M.Carrier) * algebraMap R M.Carrier (π ^ (q + 1)))
  (he : (W.map (IsLocalRing.residue R)).toAffine.Equation x y)
  (ρ : ResidueField R) (hρ : WeierstrassCurve.CriticalNeighborhood.SplitTangent (W := W) (x := x)
    (y := y) ρ)
  (hex : NoetherianBlowupExistence.{u}) (hp : NoetherianBlowupProper.{u})
  (hatlas : BlowupAffineAtlas.{u}) (hbc : BlowupFlatBaseChange.{u})
local notation "k" => ResidueField R
local notation "Y" => finalSpecialFibre M π hπ (q + 1) (Nat.succ_pos _) a ha he ρ hρ hex hp hatlas
  hbc
local notation "f" => modification M π hπ (q + 1) (Nat.succ_pos _) a ha he ρ hρ hex hp hatlas hbc
local notation "e" => originalExceptionalToSpecial M π hπ (q + 1) (Nat.succ_pos _) a ha he ρ hρ
  hex hp hatlas hbc
local notation "i" => strictTransformInclusion M π hπ (q + 1) (Nat.succ_pos _) a ha he ρ hρ hex hp
  hatlas hbc
local notation "V" => strictPuncturedOpen M π hπ (q + 1) (Nat.succ_pos _) a ha he ρ hρ hex hp
  hatlas hbc
local notation "r" => Spec.map (CommRingCat.ofHom (IsLocalRing.residue R))

/-- The indexed literal exceptional projective line mapped into the final Weierstrass special
fibre. -/
def originalExceptionalP1 (j : Fin q) : projectiveP1 k ⟶ Y :=
  Resolution.exceptionalP1 π hπ hex hp hatlas q j ≫ e

instance originalExceptionalP1_closed (j : Fin q) : IsClosedImmersion
    (originalExceptionalP1 M π hπ q a ha he ρ hρ hex hp hatlas hbc j) := by
  dsimp [originalExceptionalP1]
  infer_instance

@[reassoc (attr := simp)] lemma originalExceptionalP1_base (j : Fin q) :
    originalExceptionalP1 M π hπ q a ha he ρ hρ hex hp hatlas hbc j ≫
      pullback.snd (f ≫ structureMap W) r = AlgebraicGeometry.Scheme.ProjectiveLine.structureMap k
        := by
  simp only [originalExceptionalP1, Category.assoc, originalExceptionalToSpecial_snd]
  exact Resolution.exceptionalP1_base π hπ hex hp hatlas q j

@[reassoc] lemma originalExceptionalP1_original (j : Fin q) :
    originalExceptionalP1 M π hπ q a ha he ρ hρ hex hp hatlas hbc j ≫
      pullback.fst (f ≫ structureMap W) r ≫ f =
        AlgebraicGeometry.Scheme.ProjectiveLine.structureMap k ≫ residueNodeMap W x y he := by
  simp only [originalExceptionalP1, Category.assoc, originalExceptionalToSpecial_fst_assoc]
  rw [(originalExceptionalMap_square M π hπ (q + 1) (Nat.succ_pos _) a ha he ρ hρ hex hp hatlas
    hbc).w]
  exact Resolution.exceptionalP1_base_assoc π hπ hex hp hatlas q j (residueNodeMap W x y he)

lemma originalExceptionalP1_range_irreducible (j : Fin q) :
    IsIrreducible (Set.range (originalExceptionalP1 M π hπ q a ha he ρ hρ hex hp hatlas hbc j)) :=
      by
  simpa only [Set.image_univ] using (IrreducibleSpace.isIrreducible_univ (projectiveP1 k)).image
    (originalExceptionalP1 M π hπ q a ha he ρ hρ hex hp hatlas hbc j)
    (originalExceptionalP1 M π hπ q a ha he ρ hρ hex hp hatlas hbc j).continuous.continuousOn

lemma originalExceptionalP1_pairwise_not_subset (j l : Fin q) (hjl : j ≠ l) :
    ¬ Set.range (originalExceptionalP1 M π hπ q a ha he ρ hρ hex hp hatlas hbc j) ⊆
      Set.range (originalExceptionalP1 M π hπ q a ha he ρ hρ hex hp hatlas hbc l) :=
  Scheme.Pullback.Fibre.not_subset_postcompose _ _ e (e).injective
    (Resolution.exceptionalP1_pairwise_not_subset π hπ hex hp hatlas q j l hjl)

/-- A whole-fibre cover by actual strict and P1 scheme maps, derived without
supplying a component family or component count as a premise. -/
lemma strict_exceptionalP1_special_cover (hq : 0 < q) (z : Y) :
    z ∈ Set.range i ∨ ∃ j : Fin q,
      z ∈ Set.range (originalExceptionalP1 M π hπ q a ha he ρ hρ hex hp hatlas hbc j) := by
  rcases strict_exceptional_special_cover M π hπ (q + 1) (Nat.succ_pos _) a ha he ρ hρ hex hp
    hatlas hbc z
      with hs | ⟨p,hpoint⟩
  · exact Or.inl hs
  · obtain ⟨j,t,ht⟩ := Resolution.exceptionalP1_cover π hπ hex hp hatlas q hq p
    exact Or.inr ⟨j,t,(congrArg e ht).trans hpoint⟩

lemma strict_not_subset_originalExceptionalP1 (j : Fin q) :
    ¬ Set.range i ⊆ Set.range (originalExceptionalP1 M π hπ q a ha he ρ hρ hex hp hatlas hbc j) :=
      by
  intro H
  obtain ⟨v⟩ := (inferInstance : Nonempty (V).toScheme)
  have hv : v.val ∈ Set.range i := by
    rw [strictTransform_support]
    exact subset_closure v.property
  obtain ⟨p,hpoint⟩ := H hv
  have hd := strictPunctured_original_disjoint M π hπ (q + 1) (Nat.succ_pos _) a ha he ρ hρ hex hp
    hatlas hbc
  apply Set.disjoint_left.mp hd ⟨v,rfl⟩
  refine ⟨AlgebraicGeometry.Scheme.ProjectiveLine.structureMap k p,?_⟩
  have ht := congrArg (fun g : projectiveP1 k ⟶ scheme W => g p)
    (originalExceptionalP1_original M π hπ q a ha he ρ hρ hex hp hatlas hbc j)
  change (residueNodeMap W x y he) _ = (pullback.fst (f ≫ structureMap W) r ≫ f) v.val
  rw [← hpoint]
  exact ht.symm

/-- Each maximal whole-fibre component is one of the actual supplied maps;
this statement alone does not claim every exceptional P1 is maximal. -/
lemma irreducible_subset_strict_or_exceptionalP1 (hq : 0 < q)
    {s : Set Y} (hs : IsIrreducible s) :
    s ⊆ Set.range i ∨ ∃ j : Fin q,
      s ⊆ Set.range (originalExceptionalP1 M π hπ q a ha he ρ hρ hex hp hatlas hbc j) := by
  classical
  let F : Option (Fin q) → Set Y := fun
    | none => Set.range i
    | some j => Set.range (originalExceptionalP1 M π hπ q a ha he ρ hρ hex hp hatlas hbc j)
  let t := Finset.univ.image F
  have ht : ∀ z ∈ t, IsClosed z := by
    intro z hz
    obtain ⟨j,_,rfl⟩ := Finset.mem_image.mp hz
    cases j with
    | none => exact (i).isClosedEmbedding.isClosed_range
    | some j => exact (originalExceptionalP1 M π hπ q a ha he ρ hρ hex hp hatlas hbc
      j).isClosedEmbedding.isClosed_range
  have hc : s ⊆ ⋃₀ (t : Set (Set Y)) := by
    intro z _
    rcases strict_exceptionalP1_special_cover M π hπ q a ha he ρ hρ hex hp hatlas hbc hq z with hz
      | ⟨j,hz⟩
    · exact ⟨F none,Finset.mem_image.mpr ⟨none,Finset.mem_univ _,rfl⟩,hz⟩
    · exact ⟨F (some j),Finset.mem_image.mpr ⟨some j,Finset.mem_univ _,rfl⟩,hz⟩
  obtain ⟨z,hz,hsz⟩ := isIrreducible_iff_sUnion_isClosed.mp hs t ht hc
  obtain ⟨j,_,rfl⟩ := Finset.mem_image.mp hz
  cases j with
  | none => exact Or.inl hsz
  | some j => exact Or.inr ⟨j,hsz⟩

/-- The actual strict transform is maximal in the WHOLE final special fibre. -/
lemma strictTransform_mem_irreducibleComponents (hq : 0 < q) :
    Set.range i ∈ irreducibleComponents Y := by
  have hi : IsIrreducible (Set.range i) := by
    simpa only [Set.image_univ] using
      (IrreducibleSpace.isIrreducible_univ (strictTransform M π hπ (q + 1) (Nat.succ_pos _) a ha
        he ρ hρ hex hp hatlas hbc)).image
        i (i).continuous.continuousOn
  refine ⟨hi,?_⟩
  intro s hs his
  rcases irreducible_subset_strict_or_exceptionalP1 M π hπ q a ha he ρ hρ hex hp hatlas hbc hq hs
    with H | ⟨j,H⟩
  · exact H
  · exact False.elim (strict_not_subset_originalExceptionalP1 M π hπ q a ha he ρ hρ hex hp hatlas
    hbc j (his.trans H))

end AlgebraicGeometry.Scheme.PowerNode.PointedEtale

end -- noncomputable section
end WeierstrassExceptionalP1Cover
