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

/-! # The actual isomorphism locus of a proper birational morphism

The maximal target isomorphism open and its restriction are constructed for
an arbitrary scheme morphism. For proper birational maps with integral source
and locally Noetherian normal integral target, this open contains every point
of codimension at most one. No global dimension bound is required.

The general declarations are extracted unchanged from the surface consumer.
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

end AlgebraicGeometry.Scheme
