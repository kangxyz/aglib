/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.Morphisms.Etale.JacobsonPointedCover
public import Aglib.AlgebraicGeometry.EtaleCohomology.Pullback

/-! # Closed-point class effacement retains every original geometric mark

The supplied zero charts are actual target etale charts of the same original
class. Their open images cover a Jacobson target. One of these unchanged
charts therefore retains any specified separably closed geometric point and
its existing whole-pullback zero. This consumes closed-point zero production;
it neither assumes an open vanishing locus nor asserts those zeros exist.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry.Scheme.EtaleCohomology

universe u eY

attribute [local instance] hasSheafifyLarge HasExt.standard

/-- Actual closed-point target refinements of an original class supply an
actual refinement retaining any specified geometric point over the same
separably closed field. The original class and pullback map are unchanged. -/
theorem exists_pointed_class_zero_of_closedPoint_charts
    {X Y : Scheme.{u}} [JacobsonSpace X]
    [HasExt.{eY} (AbelianSheaf.{u, u + 1} Y)] (a : Y ⟶ X)
    (F : AbelianSheaf.{u, u + 1} Y) (q : ℕ) (c : Sheaf.H.{eY} F q)
    (hclosed : ∀ x : X, IsClosed ({x} : Set X) →
      ∃ (U : X.Etale) (y : U.left), U.hom y = x ∧
        cohomologyPullback.{u, eY, u + 2} (pullback.snd U.hom a) F q c = 0)
    (Ω : Type u) [Field Ω] [IsSepClosed Ω] (x : Spec (.of Ω) ⟶ X) :
    ∃ (U : X.Etale) (y : Spec (.of Ω) ⟶ U.left), y ≫ U.hom = x ∧
      cohomologyPullback.{u, eY, u + 2} (pullback.snd U.hom a) F q c = 0 :=
  exists_pointed_etale_property_of_closedPoints
    (fun U => cohomologyPullback.{u, eY, u + 2} (pullback.snd U.hom a) F q c = 0)
    hclosed Ω x

end AlgebraicGeometry.Scheme.EtaleCohomology
