/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.Algebra.Homology.DerivedCategory.UnboundedRightDerived.Computation.Window
public import Mathlib.Algebra.Homology.DerivedCategory.TStructure

/-! # Finite amplitude of the actual unbounded right-derived functor

The original functor sends native cohomological lower bounds `m` to `m` and
upper bounds `n` to `n + N`, under uniform all-object vanishing in degree
`N + 1`. A finite exactness window is applied to the same actual K-injective
replacement. No other resolution model or geometric vanishing theorem is assumed.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits HomologicalComplex

universe s u v w u' v' w'

namespace CategoryTheory.Functor

variable {C : Type u} [Category.{v} C] [Abelian C] [HasDerivedCategory.{w} C]
  [IsGrothendieckAbelian.{s} C]
  {D : Type u'} [Category.{v'} D] [Abelian D] [HasDerivedCategory.{w'} D]
  (F : C ⥤ D) [F.Additive] [PreservesFiniteLimits F]
  (N : ℕ) (hbound : ∀ M : C, IsZero ((F.rightDerived (N + 1)).obj M))

include N hbound

/-- A finite cohomological vanishing window on a native derived object implies
vanishing in the indicated degree of its original unbounded derived image. -/
theorem isZero_homology_unboundedRightDerivedFunctor_of_window
    (X : DerivedCategory C) (q : ℤ)
    (hX : ∀ j : ℤ, q - (N : ℤ) ≤ j → j ≤ q →
      IsZero ((DerivedCategory.homologyFunctor C j).obj X)) :
    IsZero ((DerivedCategory.homologyFunctor D q).obj
      (F.unboundedRightDerivedFunctor.obj X)) := by
  let K := DerivedCategory.Q.objPreimage X
  let I := (CochainComplex.kInjectiveReplacementFunctor (isSeparator_separator C)).obj K
  let η := (CochainComplex.kInjectiveReplacementUnit (isSeparator_separator C)).app K
  let e : DerivedCategory.Q.obj I ≅ X :=
    (asIso (DerivedCategory.Q.map η)).symm ≪≫ DerivedCategory.Q.objObjPreimageIso X
  have hexact (j : ℤ) (hj₁ : q - (N : ℤ) ≤ j) (hj₂ : j ≤ q) : I.ExactAt j := by
    rw [HomologicalComplex.exactAt_iff_isZero_homology]
    exact ((DerivedCategory.homologyFunctorFactors C j).app I).isZero_iff.mp
      (((DerivedCategory.homologyFunctor C j).mapIso e).isZero_iff.mpr (hX j hj₁ hj₂))
  have hterms (j : ℤ) (m : ℕ) :
      IsZero ((F.rightDerived (m + 1)).obj (I.X j)) :=
    F.isZero_rightDerived_obj_injective_succ m _
  have hFI := F.exactAt_map_of_acyclic_terms_of_window I N hbound q hterms hexact
  let eF : F.unboundedRightDerivedFunctor.obj X ≅
      DerivedCategory.Q.obj ((F.mapHomologicalComplex (.up ℤ)).obj I) :=
    F.unboundedRightDerivedFunctor.mapIso (DerivedCategory.Q.objObjPreimageIso X).symm ≪≫
      F.unboundedRightDerivedFunctorReplacementIso K
  let eH := (DerivedCategory.homologyFunctor D q).mapIso eF ≪≫
    (DerivedCategory.homologyFunctorFactors D q).app
      ((F.mapHomologicalComplex (.up ℤ)).obj I)
  exact eH.isZero_iff.mpr hFI.isZero_homology

/-- The actual unbounded derived functor preserves every native lower bound.
This statement uses the same all-object finite-dimensional hypothesis as the
window theorem; no boundedness of a chosen representative is assumed. -/
theorem unboundedRightDerivedFunctor_isGE_of_bound
    (X : DerivedCategory C) (m : ℤ) [X.IsGE m] :
    (F.unboundedRightDerivedFunctor.obj X).IsGE m := by
  rw [DerivedCategory.isGE_iff]
  intro q hq
  apply F.isZero_homology_unboundedRightDerivedFunctor_of_window N hbound X q
  intro j _ hj
  exact DerivedCategory.isZero_of_isGE X m j (by omega)

/-- The actual unbounded derived functor increases a native upper bound by at
most `N`, without requiring a lower bound or a second derived model. -/
theorem unboundedRightDerivedFunctor_isLE_of_bound
    (X : DerivedCategory C) (n : ℤ) [X.IsLE n] :
    (F.unboundedRightDerivedFunctor.obj X).IsLE (n + (N : ℤ)) := by
  rw [DerivedCategory.isLE_iff]
  intro q hq
  apply F.isZero_homology_unboundedRightDerivedFunctor_of_window N hbound X q
  intro j hj _
  exact DerivedCategory.isZero_of_isLE X n j (by omega)

end CategoryTheory.Functor
