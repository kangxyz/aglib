/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import
  Aglib.AlgebraicGeometry.EtaleCohomology.Fields.PurelyInseparable.FiniteConstants.Cohomology
public import Aglib.AlgebraicGeometry.EtaleCohomology.Curves.ConstantRestriction

/-! # Detection of original classwise zero before a finite purely inseparable extension

This is a thin use of the existing finite-pure comparison, not an arbitrary
purely inseparable continuity theorem. It removes only the finite pure top
of a chosen finite field stage, retaining the original class and restriction.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry.Scheme.EtaleCohomology.ConstantFinite

universe u eX eY eF

attribute [local instance] hasSheafifyLarge

/-- A zero of the original composite restriction after a finite pure field
extension already vanishes before that extension. -/
theorem constantRestriction_eq_zero_of_finitePure
    (E F : Type u) [Field E] [Field F] [Algebra E F]
    [IsPurelyInseparable E F] [Module.Finite E F]
    {X Y : Scheme.{u}} (p : Y ⟶ Spec (.of E)) (r : Y ⟶ X)
    [HasExt.{eX} (AbelianSheaf.{u, u + 1} X)]
    [HasExt.{eY} (AbelianSheaf.{u, u + 1} Y)]
    [HasExt.{eF} (AbelianSheaf.{u, u + 1} (pullback p (Spec.algebraMap E F)))]
    (A : Type u) [AddCommGroup A] [Finite A] (q : ℕ)
    (c : Sheaf.H.{eX} (coefficient A X) q)
    (hc : Curves.constantRestriction.{u, eX, eF} A
      (pullback.fst p (Spec.algebraMap E F) ≫ r) q c = 0) :
    Curves.constantRestriction.{u, eX, eY} A r q c = 0 := by
  have hinj : Function.Injective
      (Curves.constantRestriction.{u, eY, eF} A
        (pullback.fst p (Spec.algebraMap E F)) q) :=
    (finitePure_constantCohomologyPullback_bijective E F p A q).injective
  apply hinj
  rw [map_zero, ← Curves.constantRestriction_comp]
  exact hc

end AlgebraicGeometry.Scheme.EtaleCohomology.ConstantFinite
