/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/

module

public import Aglib.AlgebraicGeometry.Modules.Coherent.Affine.Comparison

/-!
# Exact global sections on an affine coherent category

The actual all-chart coherent category compares exactly with finite modules
over a Noetherian affine ring, independently of any closed subscheme.
-/
@[expose] public section

noncomputable section
universe u
open CategoryTheory AlgebraicGeometry ModuleCat CategoryTheory.ExactCategory
open AlgebraicGeometry.Scheme.Modules.QuasiCoherent
attribute [local instance] CategoryTheory.Abelian.hasFiniteBiproducts

namespace AlgebraicGeometry.Scheme.Modules.Coherent

variable (R : CommRingCat.{u}) [IsNoetherianRing R]

/-- Actual global sections on the global coherent category as an exact functor. -/
def globalSectionsExact :
    ExactFunctor (coherentExactStructure (Spec R)) (finiteModuleExactStructure.{u, u} R) :=
  (coherentToAffineExact R).comp (affineGlobalSectionsExact R)


end AlgebraicGeometry.Scheme.Modules.Coherent
