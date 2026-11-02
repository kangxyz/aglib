/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.EtaleCohomology.Fields.BoundedClassFiniteConstant
public import Aglib.AlgebraicGeometry.EtaleCohomology.Fields.TwoFieldEffacement.FiniteSource
public import Aglib.AlgebraicGeometry.EtaleCohomology.PullbackComposition

/-! # Literal coefficient-class zero through the original composite

The coefficient stage uses standard Ext; the original class retains its independent
Ext world. This is the single implementation of coefficient-image zero transport.
-/
@[expose] public noncomputable section
open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry.Scheme.EtaleCohomology.TwoFieldEffacement
universe u eX
attribute [local instance] hasSheafifyLarge HasExt.standard

/-- Transport the original coefficient presentation and zero along the same maps. -/
theorem cohomologyPullback_zero_of_constant_coefficient_composite
    {S T T₀ : Scheme.{u}} [HasExt.{eX} (AbelianSheaf.{u, u + 1} T₀)]
    (v : S ⟶ T) (f : T ⟶ T₀)
    (M : AbelianSheaf.{u, u + 1} T₀)
    (A : Type u) [AddCommGroup A] (q : ℕ)
    (c : Sheaf.H.{eX} M q)
    (d : Sheaf.H.{u + 2} (ConstantFinite.coefficient A T) q)
    (β : ConstantFinite.coefficient A T ⟶ (inverseImage f).obj M)
    (hd : Sheaf.H.map β q d = cohomologyPullback.{u, eX, u + 2} f M q c)
    (hz : Curves.constantRestriction A v q d = 0) :
    cohomologyPullback.{u, eX, u + 2} (v ≫ f) M q c = 0 := by
  have hd0 : cohomologyPullback v (ConstantFinite.coefficient A T) q d = 0 := by
    apply (cohomologyMapIso_bijective
      ((inverseImageConstantIso v).app (ConstantFinite.value A)) q).injective
    exact (Curves.constantRestriction_apply A v q d).symm.trans
      (hz.trans (map_zero _).symm)
  have hc0 := Fields.cohomologyPullback_eq_zero_of_coefficient_class v β q d
    (cohomologyPullback.{u, eX, u + 2} f M q c) hd hd0
  apply (cohomologyMapIso_bijective ((inverseImageComp f v).app M) q).injective
  exact (cohomologyPullback_comp.{u, eX, u + 2, u + 2} f v M q c).trans
    (hc0.trans (map_zero _).symm)

/-- A zero after the original stage restriction gives literal composite zero.
No field, cover, or coefficient presentation is selected again. -/
theorem cohomologyPullback_zero_of_constant_coefficient_stage
    {S W T T₀ : Scheme.{u}} [HasExt.{eX} (AbelianSheaf.{u, u + 1} T₀)]
    (r : S ⟶ W) (h : W ⟶ T) (f : T ⟶ T₀)
    (M : AbelianSheaf.{u, u + 1} T₀)
    (A : Type u) [AddCommGroup A] (q : ℕ)
    (c : Sheaf.H.{eX} M q)
    (d : Sheaf.H.{u + 2} (ConstantFinite.coefficient A T) q)
    (β : ConstantFinite.coefficient A T ⟶ (inverseImage f).obj M)
    (hd : Sheaf.H.map β q d = cohomologyPullback.{u, eX, u + 2} f M q c)
    (hz : Curves.constantRestriction A r q (Curves.constantRestriction A h q d) = 0) :
    cohomologyPullback.{u, eX, u + 2} ((r ≫ h) ≫ f) M q c = 0 := by
  exact cohomologyPullback_zero_of_constant_coefficient_composite
    (r ≫ h) f M A q c d β hd ((Curves.constantRestriction_comp A h r q d).trans hz)

end AlgebraicGeometry.Scheme.EtaleCohomology.TwoFieldEffacement
