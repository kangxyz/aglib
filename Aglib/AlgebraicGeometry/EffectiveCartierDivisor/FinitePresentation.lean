/-
Copyright (c) 2026 algebraic-geometry contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.IdealSheaf.Invertible.Affine
public import Mathlib.AlgebraicGeometry.Morphisms.FinitePresentation

/-!
# Finite presentation of actual invertible closed ideals

## Extraction basis

Existing proofs transferred from frozen dirty R5 revision
`79307ff88f07d34fd5c3edb859f799c55e38f290`. Source identities:

- `R5Lab/AlgebraicGeometry/Curves/RelativeDivisors/CartierLocality.lean`, SHA-256
  `d11c4ffb39327cd751cb517541e51344ca708630381facd0620868347b548718`.

Actual objects, maps, universes and stated conditions are retained.
Native validation coverage is recorded separately in `docs/WORK_PLAN.md` and
the migration records; the source hashes above identify extraction inputs.
-/

@[expose] public section

noncomputable section
set_option autoImplicit false
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

universe u v w t

open CategoryTheory Limits AlgebraicGeometry Opposite TopologicalSpace
open AlgebraicGeometry.Scheme
open AlgebraicGeometry.Scheme.Hom
open AlgebraicGeometry.Scheme.Modules
open LinearMap
open AlgebraicGeometry.Scheme.Modules.Invertible

section
namespace AlgebraicGeometry.Scheme.Hom

open scoped nonZeroDivisors
variable {D X : Scheme.{u}} (i : D ⟶ X)

/-- A closed immersion with locally rank-one kernel ideal is locally of finite presentation.
This result does not require a base, flatness, smoothness, or Noetherian hypotheses. -/
theorem closedImmersion_locallyOfFinitePresentation_of_isLocallyRankOne
    [IsClosedImmersion i] (hI : IsLocallyRankOne X (idealModule i)) :
    LocallyOfFinitePresentation i := by
  apply IsZariskiLocalAtTarget.of_forall_exists_morphismRestrict
    (P := @LocallyOfFinitePresentation)
  intro x
  obtain ⟨W, hxW, ⟨e⟩⟩ :=
    (isLocallyRankOne_iff_local_unit X (idealModule i)).mp hI x
  obtain ⟨_, ⟨U, hU, rfl⟩, hxU, hUW⟩ :=
    X.isBasis_affineOpens.exists_subset_of_mem_open hxW W.isOpen
  refine ⟨U, hxU, ?_⟩
  have : IsAffine U := hU
  have : IsAffine (i ⁻¹ᵁ U) := hU.preimage i
  rw [HasRingHomProperty.iff_of_isAffine (P := @LocallyOfFinitePresentation),
    morphismRestrict_appTop, CommRingCat.hom_comp,
    RingHom.finitePresentation_respectsIso.cancel_right_isIso]
  change (i.app (Scheme.Opens.ι U ''ᵁ ⊤)).hom.FinitePresentation
  rw [Scheme.Opens.ι_image_top]
  exact RingHom.FinitePresentation.of_surjective (i.app U).hom
    (i.app_surjective U hU) (idealKernel_fg_of_local_unit i W U hUW e)

/-- The finite-presentation conclusion of relative Cartier locality, on arbitrary bases. -/
theorem relativeCartier_locallyOfFinitePresentation {S : Scheme.{u}} (p : X ⟶ S)
    [LocallyOfFinitePresentation p] [IsClosedImmersion i]
    (hI : IsLocallyRankOne X (idealModule i)) :
    LocallyOfFinitePresentation (i ≫ p) := by
  let := closedImmersion_locallyOfFinitePresentation_of_isLocallyRankOne i hI
  infer_instance

end AlgebraicGeometry.Scheme.Hom
end
