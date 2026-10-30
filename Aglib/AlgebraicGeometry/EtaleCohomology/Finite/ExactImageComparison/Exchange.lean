/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.EtaleCohomology.Derived.BaseChange
public import Aglib.AlgebraicGeometry.EtaleCohomology.Finite.ExactImageComparison.Exact
public import
  Aglib.Algebra.Homology.DerivedCategory.RightDerivedFunctorPlus.BaseChange.ExactUnitIsomorphism

/-! # Invertibility of the original exchange under exact direct image

The unit equation identifies the canonical derived mate, rather than replacing
it by an arbitrarily chosen isomorphism between its endpoints.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits


namespace AlgebraicGeometry.Scheme.EtaleCohomology

universe u wX wS wX' wS'

attribute [local instance] hasSheafifyLarge

variable {X S X' S' : Scheme.{u}}
  [HasDerivedCategory.{wX} (AbelianSheaf.{u, u + 1} X)]
  [HasDerivedCategory.{wS} (AbelianSheaf.{u, u + 1} S)]
  [HasDerivedCategory.{wX'} (AbelianSheaf.{u, u + 1} X')]
  [HasDerivedCategory.{wS'} (AbelianSheaf.{u, u + 1} S')]
  (f : X ⟶ S) (f' : X' ⟶ S') (g : S' ⟶ S) (g' : X' ⟶ X)
  (h : f' ≫ g = g' ≫ f)
  [(directImage f).PreservesHomology] [(directImage f').PreservesHomology]
  [IsIso (baseChangeMap f f' g g' h)]

/-- Under explicit exactness hypotheses, the original ordinary exchange being invertible
implies that the original canonical derived mate is invertible. -/
theorem isIso_derivedBaseChangeMap_of_exact :
    IsIso (derivedBaseChangeMap f f' g g' h) :=
  Functor.isIso_of_actualDerivedUnitEquation
    (directImage f) (directImage f') (inverseImage g) (inverseImage g')
    (baseChangeMap f f' g g' h) (derivedBaseChangeMap f f' g g' h)
    (derivedBaseChangeMap_actualUnit f f' g g' h)

/-- All original higher exchange maps are invertible under the same explicit hypotheses. -/
theorem isIso_higherBaseChangeMap_of_exact (q : ℕ) :
    IsIso (higherBaseChangeMap f f' g g' h q) := by
  have : IsIso (derivedBaseChangeMap f f' g g' h) :=
    isIso_derivedBaseChangeMap_of_exact f f' g g' h
  rw [higherBaseChangeMap_eq_transport]
  infer_instance

end AlgebraicGeometry.Scheme.EtaleCohomology
