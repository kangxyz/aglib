/-
Copyright (c) 2026 algebraic-geometry contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.Modules.QuasiCoherent.Affine.TildeExact
public import Aglib.Algebra.Homology.DerivedCategory.KInjective.Adjunction.InjectiveComplex

/-!
# Injective affine sections of arbitrary module sheaves

The original affine sections functor is right adjoint to exact tilde, so
it preserves injectives on all module sheaves. It takes any bounded-below
complex of injectives to a K-injective module complex. Neither the sheaves
in that complex nor their images are assumed quasicoherent. Exactness of
sections on a resolution of a quasicoherent coefficient is a separate
cohomological assertion.
-/

@[expose] public section

noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

universe u

namespace AlgebraicGeometry.Scheme.Modules

variable (R : CommRingCat.{u})

/-- Exact tilde makes original affine sections preserve injective objects;
the input injective sheaf need not be quasicoherent. -/
instance moduleSpecΓFunctor_preservesInjectiveObjects :
    (moduleSpecΓFunctor (R := R)).PreservesInjectiveObjects :=
  Functor.preservesInjectiveObjects_of_adjunction_of_preservesMonomorphisms
    (tilde.adjunction (R := R))

/-- The actual sections of a bounded-below injective complex form a
K-injective module complex, without termwise quasicoherence or exactness. -/
theorem moduleSpecΓFunctor_map_isKInjective (I : CochainComplex (Spec R).Modules ℤ)
    (a : ℤ) [I.IsStrictlyGE a] [∀ n : ℤ, Injective (I.X n)] :
    CochainComplex.IsKInjective
      (((moduleSpecΓFunctor (R := R)).mapHomologicalComplex (.up ℤ)).obj I) :=
  (tilde.adjunction (R := R)).isKInjective_map_of_injectiveComplex I a

end AlgebraicGeometry.Scheme.Modules
