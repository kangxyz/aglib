/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.Surfaces.Birational.NormalizedPointDomination.AdaptedCharts
public import Aglib.AlgebraicGeometry.Normalization.FunctionField
public import Mathlib.AlgebraicGeometry.Noetherian
public import Mathlib.AlgebraicGeometry.Morphisms.Proper
public import Aglib.AlgebraicGeometry.Normalization.FunctionField.Finiteness

/-!
# Finite normalization of actual birational surface models

At each source point choose an affine neighborhood mapping into an affine
neighborhood of the original base. GF2 gives Nagata on that actual chart.
The affine normalization section map is finite there; finiteness is local
on the target. Thus no arbitrary-dimensional Nagata stability or
normalization base-change comparison is needed.
-/

@[expose] public noncomputable section

set_option autoImplicit false
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open CategoryTheory TopologicalSpace

namespace AlgebraicGeometry.Scheme.NormalizedPointDomination

universe u

private theorem isFinite_restrict_of_finite_app
    {X Y : Scheme.{u}} (f : X ⟶ Y) [IsAffineHom f]
    (U : Y.Opens) (hU : IsAffineOpen U) (hf : (f.app U).hom.Finite) :
    IsFinite (f ∣_ U) := by
  let : IsAffine U.toScheme := hU
  apply (HasAffineProperty.iff_of_isAffine (P := @IsFinite)).mpr
  refine ⟨hU.preimage f, ?_⟩
  have hfinite (W : Y.Opens) (hW : W = U) : (f.app W).hom.Finite := by
    subst W
    exact hf
  have hf' := hfinite (U.ι ''ᵁ ⊤) U.ι_image_top
  rw [morphismRestrict_appTop, CommRingCat.hom_comp,
    RingHom.finite_respectsIso.cancel_right_isIso]
  exact hf'

/-- Generic normalization is finite for any actual locally finite-type
birational integral model of the original Nagata surface. The original base
may be nonaffine and need not be regular. -/
theorem genericNormalization_isFinite_of_birational
    {X Y : Scheme.{u}} [IsIntegral X] [IsIntegral Y]
    (f : X ⟶ Y) [IsDominant f] [LocallyOfFiniteType f]
    (hNagata : ∀ V : Y.affineOpens, Nonempty V.1 → IsNagataRing.{u, 0} Γ(Y, V.1))
    (hdY : topologicalKrullDim Y ≤ 2)
    (hff : IsIso (CommRingCat.ofHom (functionFieldMap f))) :
    IsFinite (X.fromSpecStalk (genericPoint X)).fromNormalization := by
  let ν := (X.fromSpecStalk (genericPoint X)).fromNormalization
  apply IsZariskiLocalAtTarget.of_forall_exists_morphismRestrict (P := @IsFinite)
  intro x
  obtain ⟨V, hV, hxV, _⟩ := exists_isAffineOpen_mem_and_subset
    (show f x ∈ (⊤ : Y.Opens) from trivial)
  obtain ⟨U, hU, hxU, hUV⟩ := exists_isAffineOpen_mem_and_subset
    (show x ∈ f ⁻¹ᵁ V from hxV)
  let : Nonempty V := ⟨⟨f x, hxV⟩⟩
  let : Nonempty U := ⟨⟨x, hxU⟩⟩
  have hNU := (adaptedChart_nagata_and_dimension f V U hUV hV hU
    (hNagata ⟨V, hV⟩ inferInstance) hdY hff).1
  exact ⟨U, hxU, isFinite_restrict_of_finite_app ν U hU
    (genericNormalization_finite_app X U hU hNU)⟩

/-- The normalized actual model remains proper over the original base. -/
theorem genericNormalization_comp_isProper
    {X Y : Scheme.{u}} [IsIntegral X] [IsIntegral Y]
    (f : X ⟶ Y) [IsDominant f] [IsProper f]
    (hNagata : ∀ V : Y.affineOpens, Nonempty V.1 → IsNagataRing.{u, 0} Γ(Y, V.1))
    (hdY : topologicalKrullDim Y ≤ 2)
    (hff : IsIso (CommRingCat.ofHom (functionFieldMap f))) :
    IsProper ((X.fromSpecStalk (genericPoint X)).fromNormalization ≫ f) := by
  let := genericNormalization_isFinite_of_birational f hNagata hdY hff
  infer_instance

end AlgebraicGeometry.Scheme.NormalizedPointDomination
