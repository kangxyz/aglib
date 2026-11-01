/-
Copyright (c) 2026 kangxyz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.Cohomology.Projective.HilbertPolynomial.SupportZero

/-! Zero-dimensional support is handled without a nonempty-support premise. -/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry TopologicalSpace
open AlgebraicGeometry.Scheme.Modules AlgebraicGeometry.Scheme.Modules.QuasiCoherent
open AlgebraicGeometry.ProjectiveSpace AlgebraicGeometry.Scheme.Cohomology

universe u

example (k : Type u) [Field k] (ι : Type u) [Finite ι]
    (M : (ProjectiveSpace k ι).Modules) (hM : affineLocallyFiniteType _ M)
    (f : M ⟶ (moduleTensorLeftFunctor (ProjectiveSpace k ι) (twistingSheaf k ι 1)).obj M)
    [Mono f] (hd : topologicalKrullDim (support M) ≤ 0) : IsZero (cokernel f) :=
  isZero_cokernel_mono_twist_of_supportDimension_nonpos k ι M hM 1 f hd

end
