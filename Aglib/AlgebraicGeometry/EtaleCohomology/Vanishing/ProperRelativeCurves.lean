/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.EtaleCohomology.Vanishing.ProperCurves
public import Aglib.AlgebraicGeometry.EtaleCohomology.Vanishing.ProperGeometricFibres

/-! # Proper relative torsion cohomological dimension for geometric curves

The proved original cohomology bound on every proper geometric curve supplies
all inputs to original proper base change and geometric-stalk conservativity.
The base is arbitrary: no absolute base cohomological dimension, Noetherianity
or quasi-compactness is needed. The coefficient is internally torsion, not
necessarily killed by one integer, and characteristic-primary torsion is
included.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits TopologicalSpace

namespace AlgebraicGeometry.Scheme.EtaleCohomology.Vanishing

universe u

attribute [local instance] hasSheafifyLarge HasExt.standard

/-- A proper morphism whose literal algebraically closed geometric fibres
have dimension at most one has original torsion higher direct images zero
above degree two, over an arbitrary base scheme. -/
theorem isZero_higherDirectImage_obj_of_geometricFibres_dimension_le_one
    {X S : Scheme.{u}} (f : X ⟶ S) [IsProper f]
    (hdim : ∀ (K : Type u) [Field K] [IsAlgClosed K] (η : Spec (.of K) ⟶ S),
      topologicalKrullDim (pullback (C := Scheme) f η) ≤ 1)
    (F : AbelianSheaf.{u, u + 1} X) (hF : IsTorsion X F)
    (q : ℕ) (hq : 2 < q) : IsZero ((higherDirectImage f q).obj F) := by
  apply isZero_higherDirectImage_obj_of_geometricFiber_H_standard f F hF q
  intro K _ _ η
  exact subsingleton_H_of_isTorsion_of_proper_curve (pullback.snd f η) (hdim K η)
    ((inverseImage (pullback.fst f η)).obj F) (hF.inverseImage (pullback.fst f η)) q hq

end AlgebraicGeometry.Scheme.EtaleCohomology.Vanishing
