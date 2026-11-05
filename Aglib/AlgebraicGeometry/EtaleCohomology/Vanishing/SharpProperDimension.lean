/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.EtaleCohomology.Vanishing.SharpFiniteDimension
public import Aglib.AlgebraicGeometry.Dimension.GeometricFibres

/-! # Sharp relative torsion bounds from actual geometric fibre dimensions

The original proper geometric-stalk comparison and the proved sharp
geometric-field theorem give vanishing of the original higher direct images
above `2 * d` on any base scheme. The bound is on the actual geometric fibres;
there is no finite-dimensional, Noetherian, or quasi-compact base hypothesis.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits TopologicalSpace

namespace AlgebraicGeometry.Scheme.EtaleCohomology.Vanishing

universe u

attribute [local instance] hasSheafifyLarge HasExt.standard

/-- Proper higher direct images of every internally torsion abelian sheaf
vanish above twice a bound on all actual geometric fibre dimensions. -/
theorem isZero_higherDirectImage_obj_of_geometricFibres_two_mul_lt
    {X S : Scheme.{u}} (f : X ⟶ S) [IsProper f] (d : ℕ)
    (hdim : ∀ (K : Type u) [Field K] [IsAlgClosed K] (η : Spec (.of K) ⟶ S),
      topologicalKrullDim (pullback (C := Scheme) f η) ≤ (d : ℕ))
    (F : AbelianSheaf.{u, u + 1} X) (hF : IsTorsion X F)
    (q : ℕ) (hq : 2 * d < q) : IsZero ((higherDirectImage f q).obj F) := by
  apply isZero_higherDirectImage_obj_of_geometricFiber_H_standard f F hF q
  intro K _ _ η
  exact subsingleton_H_of_isTorsion_of_proper_dimension_le
    (pullback.snd f η) d (hdim K η) ((inverseImage (pullback.fst f η)).obj F)
      (hF.inverseImage (pullback.fst f η)) q hq

/-- Proper morphisms whose original ordinary fibres have dimension at most
`d` have no higher direct images of torsion abelian sheaves above `2 * d`.
This is the arbitrary-base, all-torsion statement of Stacks, Tag 095U. -/
theorem isZero_higherDirectImage_obj_of_fibers_two_mul_lt
    {X S : Scheme.{u}} (f : X ⟶ S) [IsProper f] (d : ℕ)
    (hdim : ∀ s : S, topologicalKrullDim (f.fiber s) ≤ (d : ℕ))
    (F : AbelianSheaf.{u, u + 1} X) (hF : IsTorsion X F)
    (q : ℕ) (hq : 2 * d < q) : IsZero ((higherDirectImage f q).obj F) :=
  isZero_higherDirectImage_obj_of_geometricFibres_two_mul_lt f d
    (fun K _ _ η => f.geometricFiber_dimension_le_of_fiber_dimension_le d hdim K η)
    F hF q hq

end AlgebraicGeometry.Scheme.EtaleCohomology.Vanishing
