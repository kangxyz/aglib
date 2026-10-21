/-
Copyright (c) 2026 kangxyz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.Morphisms.Proper.BirationalDVR
public import Aglib.AlgebraicGeometry.Properties.Normal.Basic
public import Aglib.AlgebraicGeometry.Stalk.Dimension
public import Mathlib.AlgebraicGeometry.Morphisms.IsIso
public import Mathlib.AlgebraicGeometry.Noetherian
public import Mathlib.RingTheory.DiscreteValuationRing.TFAE

/-!
# The isomorphism locus of a proper birational surface morphism

The actual target isomorphism locus is the union of all target opens on which
the original restriction is an isomorphism. Isomorphisms are local at the
target, so the restriction to that union is itself an isomorphism.

On an integral normal Noetherian target of dimension at most two, every
nonclosed point has a valuation-ring stalk. The proper birational valuation
extension theorem puts every such point in the actual isomorphism locus.
The closed complement is finite by Noetherianity and scheme sobriety.

This supplies the isomorphism-locus step in Stacks Tags 0BFP and 0C5R. It does
not assert a factorization into point blowups or a contraction theorem.
-/

@[expose] public noncomputable section

set_option autoImplicit false
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open CategoryTheory CategoryTheory.Limits TopologicalSpace

namespace AlgebraicGeometry.Scheme

universe u

/-- The maximal target open on which the original morphism is an isomorphism. -/
def Hom.targetIsomorphismLocus {X Y : Scheme.{u}} (f : X ⟶ Y) : Y.Opens :=
  ⨆ U : {U : Y.Opens // IsIso (f ∣_ U)}, U.val

/-- Every actual isomorphism restriction is contained in the target locus. -/
theorem Hom.le_targetIsomorphismLocus {X Y : Scheme.{u}} (f : X ⟶ Y)
    (U : Y.Opens) (hU : IsIso (f ∣_ U)) : U ≤ f.targetIsomorphismLocus :=
  le_iSup_of_le ⟨U, hU⟩ le_rfl

/-- The original morphism is an isomorphism after restriction to its target locus. -/
theorem Hom.isIso_restrict_targetIsomorphismLocus {X Y : Scheme.{u}} (f : X ⟶ Y) :
    IsIso (f ∣_ f.targetIsomorphismLocus) := by
  let L := f.targetIsomorphismLocus
  apply IsZariskiLocalAtTarget.of_forall_exists_morphismRestrict
    (P := .isomorphisms Scheme)
  intro y
  have hy : y.1 ∈ f.targetIsomorphismLocus := y.2
  simp only [Hom.targetIsomorphismLocus, Opens.mem_iSup] at hy
  obtain ⟨U, hyU⟩ := hy
  let W : L.toScheme.Opens := L.ι ⁻¹ᵁ U.val
  refine ⟨W, hyU, ?_⟩
  have hU : U.val ≤ L := f.le_targetIsomorphismLocus U.val U.property
  have himage : L.ι ''ᵁ W = U.val := by
    change L.ι ''ᵁ (L.ι ⁻¹ᵁ U.val) = U.val
    rw [Hom.image_preimage_eq_opensRange_inf, Opens.opensRange_ι, inf_eq_right.mpr hU]
  have hsingle : IsIso (f ∣_ L.ι ''ᵁ W) :=
    ((MorphismProperty.isomorphisms Scheme).arrow_mk_iso_iff
      (morphismRestrictEq f himage)).mpr U.property
  exact ((MorphismProperty.isomorphisms Scheme).arrow_mk_iso_iff
    (morphismRestrictRestrict f L W)).mpr hsingle

private theorem coheight_le_two_of_topologicalKrullDim_le_two
    (Y : Scheme.{u}) (hdim : topologicalKrullDim Y ≤ 2) (y : Y) :
    Order.coheight y ≤ 2 := by
  rw [topologicalKrullDim_eq_iSup_stalk] at hdim
  have hy := (le_iSup (fun z : Y => ringKrullDim (Y.presheaf.stalk z)) y).trans hdim
  rw [ringKrullDim_stalk_eq_coheight] at hy
  exact WithBot.coe_le_coe.mp hy

/-- A nonclosed point of a scheme of dimension at most two has stalk dimension
at most one; a strict specialization would otherwise give a chain of length three. -/
theorem coheight_le_one_of_not_isClosed_singleton_of_dimension_le_two
    (Y : Scheme.{u}) (hdim : topologicalKrullDim Y ≤ 2) (y : Y)
    (hy : ¬IsClosed ({y} : Set Y)) : Order.coheight y ≤ 1 := by
  have hnot : ¬closure ({y} : Set Y) ⊆ {y} := by
    intro h
    exact hy (isClosed_of_closure_subset h)
  obtain ⟨z, hz, hzne⟩ := Set.not_subset.mp hnot
  have hzy : z ≤ y := specializes_iff_mem_closure.mpr hz
  have hzne' : z ≠ y := by simpa only [Set.mem_singleton_iff] using hzne
  have hlt : z < y := lt_iff_le_not_ge.mpr
    ⟨hzy, fun hyz => hzne' (Specializes.antisymm hyz hzy).eq⟩
  have hsum : Order.coheight y + 1 ≤ 2 :=
    (Order.coheight_add_one_le hlt).trans
      (coheight_le_two_of_topologicalKrullDim_le_two Y hdim z)
  exact (ENat.add_le_add_iff_right (by simp : (1 : ℕ∞) ≠ ⊤)).mp hsum

/-- Normal target points of coheight at most one have valuation-ring stalks,
including the generic field stalk, and admit actual birational isomorphism opens. -/
theorem exists_isIso_restrict_of_isProper_birational_at_coheight_le_one
    {X Y : Scheme.{u}} [IsIntegral X] [IsIntegral Y] [IsLocallyNoetherian Y]
    (f : X ⟶ Y) [IsProper f] [IsDominant f]
    (hff : IsIso (CommRingCat.ofHom (functionFieldMap f)))
    (hY : NormalStalks Y) (y : Y) (hy : Order.coheight y ≤ 1) :
    ∃ U : Y.Opens, y ∈ U ∧ IsIso (f ∣_ U) := by
  let R := Y.presheaf.stalk y
  let : IsDomain R := (hY y).1
  let : IsIntegrallyClosed R := (hY y).2
  let : Ring.KrullDimLE 1 R := krullDimLE_of_coheight_le hy
  have hprime : ∀ P : Ideal R, P ≠ ⊥ → P.IsPrime → P = IsLocalRing.maximalIdeal R := by
    intro P hP hprime
    exact IsLocalRing.eq_maximalIdeal (hprime.isMaximal_of_ne_bot hP)
  let : ValuationRing R :=
    ((tfae_of_isNoetherianRing_of_isLocalRing_of_isDomain R).out 4 2 rfl rfl).mp
      ⟨inferInstance, hprime⟩
  exact exists_isIso_restrict_of_isProper_birational_at_valuationRing f hff y

/-- The actual proper birational morphism is an isomorphism on a neighborhood of
every nonclosed point of the normal target of dimension at most two. -/
theorem exists_isIso_restrict_of_isProper_birational_at_nonclosed_point
    {X Y : Scheme.{u}} [IsIntegral X] [IsIntegral Y] [IsLocallyNoetherian Y]
    (f : X ⟶ Y) [IsProper f] [IsDominant f]
    (hff : IsIso (CommRingCat.ofHom (functionFieldMap f)))
    (hY : NormalStalks Y) (hdim : topologicalKrullDim Y ≤ 2)
    (y : Y) (hy : ¬IsClosed ({y} : Set Y)) :
    ∃ U : Y.Opens, y ∈ U ∧ IsIso (f ∣_ U) :=
  exists_isIso_restrict_of_isProper_birational_at_coheight_le_one f hff hY y
    (coheight_le_one_of_not_isClosed_singleton_of_dimension_le_two Y hdim y hy)

/-- Every point outside the actual target isomorphism locus is closed. -/
theorem Hom.isClosed_singleton_of_not_mem_targetIsomorphismLocus
    {X Y : Scheme.{u}} [IsIntegral X] [IsIntegral Y] [IsLocallyNoetherian Y]
    (f : X ⟶ Y) [IsProper f] [IsDominant f]
    (hff : IsIso (CommRingCat.ofHom (functionFieldMap f)))
    (hY : NormalStalks Y) (hdim : topologicalKrullDim Y ≤ 2)
    (y : Y) (hy : y ∉ f.targetIsomorphismLocus) : IsClosed ({y} : Set Y) := by
  by_contra hclosed
  obtain ⟨U, hyU, hU⟩ :=
    exists_isIso_restrict_of_isProper_birational_at_nonclosed_point f hff hY hdim y hclosed
  exact hy (f.le_targetIsomorphismLocus U hU hyU)

private theorem finite_of_isClosed_of_singletons_closed
    (Y : Scheme.{u}) [NoetherianSpace Y] {C : Set Y} (hC : IsClosed C)
    (hpoints : ∀ y ∈ C, IsClosed ({y} : Set Y)) : C.Finite := by
  obtain ⟨S, hSfinite, hSclosed, hSirr, hcover⟩ :=
    NoetherianSpace.exists_finite_set_isClosed_irreducible hC
  have hfinite : ∀ Z ∈ S, Z.Finite := by
    intro Z hZ
    let y := (hSirr Z hZ).genericPoint
    have hy : IsGenericPoint y Z := (hSirr Z hZ).isGenericPoint_genericPoint (hSclosed Z hZ)
    have hyC : y ∈ C := by
      rw [hcover]
      exact Set.mem_sUnion_of_mem hy.mem hZ
    have hZsingle : Z = {y} := hy.symm.trans (hpoints y hyC).closure_eq
    rw [hZsingle]
    exact Set.finite_singleton y
  rw [hcover]
  exact hSfinite.sUnion hfinite

/-- The complement of the actual isomorphism locus is finite for a normal
Noetherian integral target of dimension at most two. -/
theorem Hom.finite_compl_targetIsomorphismLocus_of_isProper_birational
    {X Y : Scheme.{u}} [IsIntegral X] [IsIntegral Y] [IsNoetherian Y]
    (f : X ⟶ Y) [IsProper f] [IsDominant f]
    (hff : IsIso (CommRingCat.ofHom (functionFieldMap f)))
    (hY : NormalStalks Y) (hdim : topologicalKrullDim Y ≤ 2) :
    ((f.targetIsomorphismLocus : Set Y)ᶜ).Finite := by
  apply finite_of_isClosed_of_singletons_closed Y f.targetIsomorphismLocus.isOpen.isClosed_compl
  intro y hy
  exact f.isClosed_singleton_of_not_mem_targetIsomorphismLocus hff hY hdim y hy

/-- A proper dominant birational morphism onto a normal Noetherian integral
surface is an actual isomorphism over an open whose complement is a finite set
of closed points. No regularity of the source is needed. -/
theorem exists_isIso_restrict_finite_closed_complement_of_isProper_birational
    {X Y : Scheme.{u}} [IsIntegral X] [IsIntegral Y] [IsNoetherian Y]
    (f : X ⟶ Y) [IsProper f] [IsDominant f]
    (hff : IsIso (CommRingCat.ofHom (functionFieldMap f)))
    (hY : NormalStalks Y) (hdim : topologicalKrullDim Y ≤ 2) :
    ∃ U : Y.Opens, IsIso (f ∣_ U) ∧ ((U : Set Y)ᶜ).Finite ∧
      ∀ y : Y, y ∉ U → IsClosed ({y} : Set Y) := by
  exact ⟨f.targetIsomorphismLocus, f.isIso_restrict_targetIsomorphismLocus,
    f.finite_compl_targetIsomorphismLocus_of_isProper_birational hff hY hdim,
    f.isClosed_singleton_of_not_mem_targetIsomorphismLocus hff hY hdim⟩

end AlgebraicGeometry.Scheme
