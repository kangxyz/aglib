/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.Modules.PerfectComplexes.Strict
public import Aglib.AlgebraicGeometry.Modules.LocallyFree.Affine.LocalBases
public import Aglib.AlgebraicGeometry.Modules.QuasiCoherent.Affine.TildeExact
public import Mathlib.Algebra.Homology.Embedding.CochainComplex

/-!
# Strict perfectness of the original affine tilde complex

Applying the native exact tilde functor to a bounded complex of finite
projective modules gives a strict perfect complex on the actual affine
spectrum. The original terms, differential maps and term bounds are retained.
No Noetherian hypothesis or homology-finiteness premise is needed.
-/

@[expose] public section

noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

namespace AlgebraicGeometry.Scheme.Modules.Complex

/-- The actual native tilde complex of a strictly bounded finite-projective
module complex is strict perfect on the original spectrum, with the same
term bounds. -/
theorem strictPerfect_tilde_of_finite_projective (R : CommRingCat.{u})
    (P : CochainComplex (ModuleCat.{u} R) ℤ) (a b : ℤ)
    [P.IsStrictlyGE a] [P.IsStrictlyLE b]
    [∀ j, Module.Finite R (P.X j)] [∀ j, Module.Projective R (P.X j)] :
    strictPerfect (Spec R) (((tilde.functor R).mapHomologicalComplex (.up ℤ)).obj P) := by
  constructor
  · refine ⟨a, b, fun j hj => ?_⟩
    exact (tilde.functor R).map_isZero (hj.elim
      (fun h => P.isZero_of_isStrictlyGE a j h)
      (fun h => P.isZero_of_isStrictlyLE b j h))
  · intro j
    exact finiteLocallyFree_tilde_of_finite_projective R (P.X j)

end AlgebraicGeometry.Scheme.Modules.Complex
