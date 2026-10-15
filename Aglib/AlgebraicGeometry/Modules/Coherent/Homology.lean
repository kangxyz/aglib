/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Mathlib.Algebra.Homology.ShortComplex.HomologicalComplex
public import Aglib.AlgebraicGeometry.Modules.Coherent.FinitePresentation
/-!
# Local coherence and actual coherent homology

On locally noetherian schemes, actual coherence is local on arbitrary open
neighborhoods and is preserved by actual homology of termwise coherent
complexes. No quasi-compactness or boundedness is needed.
-/
@[expose] public section


noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
universe u
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry TopologicalSpace
open AlgebraicGeometry.Scheme.Modules.QuasiCoherent
namespace AlgebraicGeometry.Scheme.Modules.Coherent

/-- Coherence is local on actual open neighborhoods of a locally noetherian scheme. -/
theorem affineLocallyFiniteType_of_openNeighborhoods {X : Scheme.{u}} [IsLocallyNoetherian X]
    (M : X.Modules) (hM : ∀ x : X, ∃ U : X.Opens, x ∈ U ∧
      affineLocallyFiniteType U.toScheme (M.restrict U.ι)) : affineLocallyFiniteType X M := by
  classical
  choose U hU hc using hM
  have hfp (x : X) : (M.restrict (U x).ι).IsFinitePresentation := by
    let : IsLocallyNoetherian (U x).toScheme := isLocallyNoetherian_of_isOpenImmersion (U x).ι
    exact affineLocallyFiniteType_finitePresentation (hc x)
  have : M.IsFinitePresentation := finitePresentation_of_openCover M U (by
    rw [IsOpenCover]
    apply top_unique
    intro x _
    exact Opens.mem_iSup.mpr ⟨x, hU x⟩) hfp
  exact affineLocallyFiniteType_of_finitePresentation M

/-- Actual homology of a termwise coherent complex is coherent. -/
theorem affineLocallyFiniteType_homology {X : Scheme.{u}} [IsLocallyNoetherian X]
    (K : CochainComplex X.Modules ℤ) (hK : ∀ n, affineLocallyFiniteType X (K.X n)) (i : ℤ) :
    affineLocallyFiniteType X (K.homology i) := by
  let S := K.sc i
  have hk := (affineLocallyFiniteType X).prop_kernel S.g (hK _) (hK _)
  have hc := (affineLocallyFiniteType X).prop_cokernel (kernel.lift S.g S.f S.zero) (hK _) hk
  exact (affineLocallyFiniteType X).prop_of_iso S.homologyIsoCokernelLift.symm hc

end AlgebraicGeometry.Scheme.Modules.Coherent
