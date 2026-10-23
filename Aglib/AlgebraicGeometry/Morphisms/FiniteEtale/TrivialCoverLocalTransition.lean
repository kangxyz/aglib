/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.Morphisms.FiniteEtale.TrivialCoverFunctor
public import Aglib.AlgebraicGeometry.Morphisms.FiniteEtale.CoverLocalEquality

/-! # Local permutations between actual trivial finite-etale covers

A transition need not be one permutation over the whole base. Its actual
geometric fibre determines a label isomorphism which agrees with the transition
on an open neighbourhood, by the finite-etale equalizer theorem.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

namespace AlgebraicGeometry.Scheme.FiniteEtale

universe u

variable {X : Scheme.{u}} {K : Type u} [Field K] [IsSepClosed K]
    (s : Spec (CommRingCat.of K) ⟶ X) {A B : FintypeCat.{u}}

/-- The label isomorphism of a transition at the specified geometric point. -/
def trivialCoverTransitionLabels
    (e : (trivialCoverFunctor X).obj A ≅ (trivialCoverFunctor X).obj B) : A ≅ B :=
  (trivialCoverFunctorFiberIso s).app A ≪≫ (fiberToFinite s).mapIso e ≪≫
    ((trivialCoverFunctorFiberIso s).app B).symm

omit [IsSepClosed K] in
/-- The constant relabeling and the transition have the same actual geometric fibre. -/
theorem trivialCoverTransitionLabels_fiber
    (e : (trivialCoverFunctor X).obj A ≅ (trivialCoverFunctor X).obj B) :
    (fiberToFinite s).map
        ((trivialCoverFunctor X).map (trivialCoverTransitionLabels s e).hom) =
      (fiberToFinite s).map e.hom := by
  apply (cancel_epi ((trivialCoverFunctorFiberIso s).app A).hom).mp
  have h := (trivialCoverFunctorFiberIso s).hom.naturality
    (trivialCoverTransitionLabels s e).hom
  change (trivialCoverTransitionLabels s e).hom ≫
      ((trivialCoverFunctorFiberIso s).app B).hom =
    ((trivialCoverFunctorFiberIso s).app A).hom ≫
      (fiberToFinite s).map
        ((trivialCoverFunctor X).map (trivialCoverTransitionLabels s e).hom) at h
  rw [← h]
  simp only [trivialCoverTransitionLabels, Iso.trans_hom, Iso.symm_hom,
    Functor.mapIso_hom, Category.assoc, Iso.inv_hom_id, Category.comp_id]

/-- Every geometric point has an actual open neighbourhood on which the
transition is its fibre permutation. The neighbourhood is allowed to depend
on the point; no connectedness or global-permutation premise is used. -/
theorem exists_open_trivialCoverTransition
    (e : (trivialCoverFunctor X).obj A ≅ (trivialCoverFunctor X).obj B) :
    ∃ V : X.Opens, s default ∈ V ∧
      (baseChange V.ι).map e.hom =
        (baseChange V.ι).map
          ((trivialCoverFunctor X).map (trivialCoverTransitionLabels s e).hom) :=
  exists_open_map_eq_of_fiber_eq s e.hom
    ((trivialCoverFunctor X).map (trivialCoverTransitionLabels s e).hom)
    (trivialCoverTransitionLabels_fiber s e).symm

end AlgebraicGeometry.Scheme.FiniteEtale
