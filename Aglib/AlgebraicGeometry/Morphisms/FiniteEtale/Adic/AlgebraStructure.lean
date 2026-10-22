/-
Copyright (c) 2026 kangxyz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.Morphisms.FiniteEtale.Adic.CoverSystemModules
public import Aglib.AlgebraicGeometry.Cohomology.GrothendieckExistence.Algebraization.Operations

/-!
# Native algebra structure on the actual coherent cover system

This shared adapter uses the original finite direct-image algebras and their
original transition maps. It introduces neither a formal tensor product nor a
new realization premise. Both object algebraization and morphism lifting use it.
-/

@[expose] public noncomputable section

open CategoryTheory
open scoped MonObj

namespace AlgebraicGeometry.Scheme.FiniteEtale.Adic.CoverSystem

universe u

open Modules.Coherent

variable {X : Scheme.{u}} [IsLocallyNoetherian X] {K : X.IdealSheafData}

/-- The actual coefficient algebras and transition maps of the cover tower. -/
instance adicAlgebraStructure (T : CoverSystem K) : AdicAlgebraStructure T.adicSystem where
  mon n := T.instMonObjModuleDiagram n
  comm n := T.instIsCommMonObjModuleDiagram n
  map _ _ g := T.instIsMonHomModuleDiagramMap g

end AlgebraicGeometry.Scheme.FiniteEtale.Adic.CoverSystem
