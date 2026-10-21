/-
Copyright (c) 2026 kangxyz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.RingTheory.PlaneNode.Regularity
public import Aglib.AlgebraicGeometry.Properties.Regular.OpenCover

/-!
Native extraction from the R5 local-model source
`PointedResolution.Resolution.Regularity`.
R5 revision: `f8a3314ddecffcada2ec721d26d56a937bed9690`.
Source SHA-256:
`07c33ab8a3a7219f5117bb99ad8a853507d20db7b06cc21ecf79db954b4bd1af`.
Only regularity of the actual spectrum stalks is retained in this scheme-level leaf.
Conditional blowup families remain explicit inputs.
-/

@[expose] public section

noncomputable section
open AlgebraicGeometry
universe u

namespace PlaneNode.Regularity

variable {R : Type u} [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]

/-- The regularity proof is for the stalks of the literal affine node scheme. -/
lemma uniformizerNode_stalk_regular (π : R) (hπ : Irreducible π)
    (x : Spec (.of (PlaneNode.Ring π))) :
    IsRegularLocalRing ((Spec (.of (PlaneNode.Ring π))).presheaf.stalk x) := by
  have := uniformizerNode_regular π hπ
  exact Scheme.regularStalks_spec (PlaneNode.Ring π) x


end PlaneNode.Regularity
