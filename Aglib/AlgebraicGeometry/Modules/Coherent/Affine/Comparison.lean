/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/

module

public import Aglib.AlgebraicGeometry.Modules.QuasiCoherent.Affine.FiniteTypeComparison
public import Aglib.AlgebraicGeometry.Modules.Coherent.Exact

/-!
# Exact comparison of Noetherian affine coherent categories
-/
@[expose] public section

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
universe u
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry TopologicalSpace
open CategoryTheory.ExactCategory
open ModuleCat
open AlgebraicGeometry.Scheme.Modules.QuasiCoherent
attribute [local instance] Abelian.hasFiniteBiproducts

namespace AlgebraicGeometry.Scheme.Modules.Coherent

variable (R : CommRingCat.{u}) [IsNoetherianRing R]

/-- The inverse of the actual composite affine sheaf/module equivalence is additive. -/
instance finiteTypeSheavesSpecModuleEquivalence_inverse_additive :
    (finiteTypeSheavesSpecModuleEquivalence R).inverse.Additive := by
  let := preservesBinaryBiproducts_of_preservesBinaryProducts
    (finiteTypeSheavesSpecModuleEquivalence R).inverse
  exact Functor.additive_of_preservesBinaryBiproducts _

instance finiteTypeSheavesAffineEquivalence_additive : (finiteTypeSheavesAffineEquivalence
  R).functor.Additive := by
  let := preservesBinaryBiproducts_of_preservesBinaryProducts (finiteTypeSheavesAffineEquivalence
    R).functor
  exact Functor.additive_of_preservesBinaryBiproducts _

instance finiteTypeSheavesAffineEquivalence_inverse_additive :
    (finiteTypeSheavesAffineEquivalence R).inverse.Additive := by
  let := preservesBinaryBiproducts_of_preservesBinaryProducts (finiteTypeSheavesAffineEquivalence
    R).inverse
  exact Functor.additive_of_preservesBinaryBiproducts _

/-- The comparison is an exact functor for the actual abelian exact structures. -/
def coherentToAffineExact :
    ExactFunctor (coherentExactStructure (Spec R)) (affineCoherentExactStructure R) where
  toFunctor := (finiteTypeSheavesAffineEquivalence R).functor
  map_conflation _ h := h.map_of_exact _

/-- Its inverse is exact as well. -/
def affineToCoherentExact :
    ExactFunctor (affineCoherentExactStructure R) (coherentExactStructure (Spec R)) where
  toFunctor := (finiteTypeSheavesAffineEquivalence R).inverse
  map_conflation _ h := h.map_of_exact _

end AlgebraicGeometry.Scheme.Modules.Coherent
