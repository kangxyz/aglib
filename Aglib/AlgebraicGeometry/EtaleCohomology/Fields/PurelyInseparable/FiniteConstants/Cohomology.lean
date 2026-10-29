/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.EtaleCohomology.Fields.PurelyInseparable.FiniteConstants.SectionUnit
public import Aglib.AlgebraicGeometry.EtaleCohomology.Finite.HigherVanishing
public import Aglib.AlgebraicGeometry.EtaleCohomology.Finite.ExactImageComparison.Cohomology
public import Aglib.AlgebraicGeometry.EtaleCohomology.PullbackEquivalence
public import Aglib.CategoryTheory.Sites.SheafCohomology.Slice.ExtComparison
public import Mathlib.AlgebraicGeometry.Morphisms.Finite

/-! # Original finite constant cohomology under finite purely inseparable extension

The original constant-sheaf unit is proved in `SectionUnit`. Exact finite
direct image then identifies the actual all-degree pullback with the original
coefficient-unit map under the exact-adjunction comparison. The two Ext
universes remain independent.
-/

@[expose] public noncomputable section

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry.Scheme.EtaleCohomology.ConstantFinite

universe u w w'

attribute [local instance] hasSheafifyLarge

private theorem cohomologyPullback_bijective_of_finite_unit
    {X S : Scheme.{u}} (f : S ⟶ X) [IsFinite f]
    [HasExt.{w} (AbelianSheaf.{u, u + 1} X)]
    [HasExt.{w'} (AbelianSheaf.{u, u + 1} S)]
    (L : AbelianSheaf.{u, u + 1} X)
    [IsIso ((inverseImageAdjunction f).unit.app L)] (q : ℕ) :
    Function.Bijective (cohomologyPullback.{u, w, w'} f L q) := by
  exact (inverseImageAdjunction f).mapExactFunctor_precomp_bijective_of_isIso_unit
    ((inverseImageConstantIso f).app (AddCommGrpCat.of (ULift.{u + 1} ℤ))) L q

variable (k K : Type u) [Field k] [Field K] [Algebra k K]
  [IsPurelyInseparable k K] [Module.Finite k K]
  {X : Scheme.{u}} (p : X ⟶ Spec (.of k))
  [HasExt.{w} (AbelianSheaf.{u, u + 1} X)]
  [HasExt.{w'} (AbelianSheaf.{u, u + 1} (pullback p (Spec.algebraMap k K)))]
  (A : Type u) [AddCommGroup A] [Finite A]

/-- Original pullback on the actual inverse-image coefficient is bijective in every
degree under a finite purely inseparable field extension, on every scheme. -/
theorem finitePure_cohomologyPullback_bijective (q : ℕ) :
    Function.Bijective (cohomologyPullback.{u, w, w'}
      (pullback.fst p (Spec.algebraMap k K)) (coefficient A X) q) := by
  let : IsFinite (Spec.algebraMap k K) := by
    change IsFinite (Spec.map (CommRingCat.ofHom (algebraMap k K)))
    rw [IsFinite.SpecMap_iff]
    exact RingHom.finite_algebraMap.mpr inferInstance
  let := finitePure_adjunctionUnit_isIso k K p A
  exact cohomologyPullback_bijective_of_finite_unit
    (pullback.fst p (Spec.algebraMap k K)) (coefficient A X) q

/-- The literal original all-degree finite constant restriction is bijective.
The map is original pullback followed by the native constant coefficient isomorphism. -/
theorem finitePure_constantCohomologyPullback_bijective (q : ℕ) :
    Function.Bijective
      ((Sheaf.H.map ((inverseImageConstantIso
        (pullback.fst p (Spec.algebraMap k K))).app (value A)).hom q).comp
        (cohomologyPullback.{u, w, w'}
          (pullback.fst p (Spec.algebraMap k K)) (coefficient A X) q)) :=
  (cohomologyMapIso_bijective ((inverseImageConstantIso
    (pullback.fst p (Spec.algebraMap k K))).app (value A)) q).comp
      (finitePure_cohomologyPullback_bijective k K p A q)

end AlgebraicGeometry.Scheme.EtaleCohomology.ConstantFinite
