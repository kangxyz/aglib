/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.Cohomology.GrothendieckExistence.Algebraization.NativeOperations
public import Aglib.AlgebraicGeometry.Cohomology.GrothendieckExistence.Proper

/-! # Proper existence for the original native algebraization operations

The complete native operations and their original stage equations live in
`NativeOperations`. This module retains the proper-existence specialization
and re-exports the unchanged native declarations for existing consumers.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits MonoidalCategory Opposite
open scoped MonObj

namespace AlgebraicGeometry.Scheme.Cohomology

open AlgebraicGeometry.Scheme.Modules AlgebraicGeometry.Scheme.Modules.Coherent

universe u
variable {A : Type u} [CommRing A] [IsNoetherianRing A]
  (I : Ideal A) [IsAdicComplete I A] {X : Scheme.{u}}
  (f : X ⟶ Spec (CommRingCat.of A)) [IsProper f]

/-- Proper Grothendieck existence algebraizes native commutative algebra
operations, retaining the original formal isomorphism and all its stage maps. -/
def properAdicAlgebraization :
    letI : IsLocallyNoetherian X := LocallyOfFiniteType.isLocallyNoetherian f
    ∀ (F : AdicSystem X (idealThickeningIdealSheaf f I)) [AdicAlgebraStructure F],
      AdicAlgebraizationData F := by
  letI : IsLocallyNoetherian X := LocallyOfFiniteType.isLocallyNoetherian f
  intro F _
  let e := properCompletionEquivalence I f
  exact algebraizationDataOfComparison (completionFunctorFullyFaithful I f)
    (e.inverse.obj F) (e.counitIso.app F)

end AlgebraicGeometry.Scheme.Cohomology
