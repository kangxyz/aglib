/-
Copyright (c) 2026 algebraic-geometry contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.Modules.LocallyFree.OpenImage
public import Aglib.AlgebraicGeometry.Modules.LocallyFree.FreeCover
public import Aglib.AlgebraicGeometry.Modules.LocallyFree.FibreDimension
public import Aglib.AlgebraicGeometry.Modules.Invertible.Tensor

/-!
# Local rank one on an arbitrary open cover

## Extraction basis

Existing proofs transferred from frozen dirty R5 revision
`79307ff88f07d34fd5c3edb859f799c55e38f290`. Source identities:

- `R5Lab/AlgebraicGeometry/Curves/RelativeDivisors/SmoothIdeal.lean`, SHA-256
  `1e1f564e4d5d68f6f673a435f935642b06c6faeca7632d110bc71565993a96e4`.

Actual objects, maps, universes and stated conditions are retained.
Native validation coverage is recorded separately in `doc/WORK_PLAN.md` and
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
open AlgebraicGeometry.Scheme.Modules
open LinearMap
open AlgebraicGeometry.Scheme.Modules.Invertible

section
namespace AlgebraicGeometry.Scheme.Modules.Invertible

variable {X D : Scheme.{u}}

/-- Local singleton bases glue along any open cover. -/
theorem isLocallyRankOne_of_cover_restrict {κ : Type u} (M : X.Modules)
    (U : κ → X.Opens) (hcov : IsOpenCover U)
    (h : ∀ i, IsLocallyRankOne (U i).toScheme (M.restrict (U i).ι)) :
    IsLocallyRankOne X M := by
  let q (i : κ) := (h i).choose
  let (i : κ) : (q i).IsLocallyFreeData := (h i).choose_spec.1
  let W : (Σ i : κ, (q i).I) → X.Opens := fun i ↦ (U i.1).ι ''ᵁ (q i.1).X i.2
  have hW : IsOpenCover W := by
    apply top_le_iff.mp
    intro x _
    obtain ⟨i, hi⟩ := hcov.exists_mem x
    obtain ⟨j, hj⟩ := (Opens.coversTop_iff (U i).toScheme (q i).X).mp (q i).coversTop
      |>.exists_mem (⟨x, hi⟩ : U i)
    exact Opens.mem_iSup.mpr ⟨⟨i, j⟩, ⟨⟨x, hi⟩, hj, rfl⟩⟩
  let I' (i : Σ i : κ, (q i).I) := ((q i.1).generators i.2).I
  let q' := localGeneratorsOfCoverFreeIso W hW I' (fun i ↦
    freeIsoOnImage (U i.1).ι M ((q i.1).X i.2)
      (((localBasisRestrictedIso
        (M.restrict (U i.1).ι) (q i.1) inferInstance i.2) ≪≫
        (Scheme.Modules.restrictFunctorIsoPullback
          (Scheme.Opens.ι (X := (U i.1).toScheme) ((q i.1).X i.2))).symm.app
          (M.restrict (U i.1).ι))))
  exact ⟨q', inferInstance, fun i ↦ (h i.1).choose_spec.2 i.2⟩

end AlgebraicGeometry.Scheme.Modules.Invertible
end
