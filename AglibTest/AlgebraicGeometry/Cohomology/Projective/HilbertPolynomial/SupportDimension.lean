/-
Copyright (c) 2026 kangxyz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.Cohomology.Projective.HilbertPolynomial.SupportDimension

/-! A monic twist on support of dimension at most one has zero-dimensional cokernel support. -/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry TopologicalSpace
open AlgebraicGeometry.ProjectiveSpace AlgebraicGeometry.Scheme.Modules
open AlgebraicGeometry.Scheme.Modules.QuasiCoherent AlgebraicGeometry.Scheme.Cohomology

universe u

example (k : Type u) [Field k] (ι : Type u) [Finite ι]
    (M : (ProjectiveSpace k ι).Modules) (hM : affineLocallyFiniteType _ M)
    (f : M ⟶ (moduleTensorLeftFunctor (ProjectiveSpace k ι) (twistingSheaf k ι 1)).obj M)
    [Mono f] (hd : topologicalKrullDim (support M) ≤ 1) :
    topologicalKrullDim (support (cokernel f)) ≤ 0 := by
  simpa using topologicalKrullDim_support_cokernel_mono_twist_le k ι M hM 1 f 0 hd

end
