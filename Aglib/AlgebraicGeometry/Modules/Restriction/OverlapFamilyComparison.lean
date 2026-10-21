/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.Modules.Restriction.OverlapComparison
public import Aglib.AlgebraicGeometry.Modules.InternalHom.Gluing

/-! # Original comparison compatibility for a family of overlap presentations -/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits
universe u v
namespace AlgebraicGeometry.Scheme.Modules

/-- A family of actual cartesian refinements supplies the existing native
restriction-compatibility predicate, with the original maps on every chart. -/
theorem restrictionHomCompatible_of_refinements
    {X : Scheme.{u}} {ι : Type v} {Y : ι → Scheme.{u}}
    (j : ∀ i, Y i ⟶ X) [∀ i, IsOpenImmersion (j i)]
    (W : ι → ι → Scheme.{u})
    (a : ∀ i k, W i k ⟶ Y i) (b : ∀ i k, W i k ⟶ Y k)
    (c : ∀ i k, W i k ⟶ X)
    [∀ i k, IsOpenImmersion (a i k)] [∀ i k, IsOpenImmersion (b i k)]
    [∀ i k, IsOpenImmersion (c i k)]
    (H : ∀ i k, IsPullback (a i k) (b i k) (j i) (j k))
    (ha : ∀ i k, a i k ≫ j i = c i k)
    (hb : ∀ i k, b i k ≫ j k = c i k)
    (N M : X.Modules)
    (q : ∀ i, N.restrict (j i) ⟶ M.restrict (j i))
    (qW : ∀ i k, N.restrict (c i k) ⟶ M.restrict (c i k))
    (hU : ∀ i k, (restrictFunctor (a i k)).map (q i) ≫
        ((restrictFunctorComp (a i k) (j i)).symm.app M ≪≫
          (restrictFunctorCongr (ha i k)).app M).hom =
      ((restrictFunctorComp (a i k) (j i)).symm.app N ≪≫
        (restrictFunctorCongr (ha i k)).app N).hom ≫ qW i k)
    (hV : ∀ i k, (restrictFunctor (b i k)).map (q k) ≫
        ((restrictFunctorComp (b i k) (j k)).symm.app M ≪≫
          (restrictFunctorCongr (hb i k)).app M).hom =
      ((restrictFunctorComp (b i k) (j k)).symm.app N ≪≫
        (restrictFunctorCongr (hb i k)).app N).hom ≫ qW i k) :
    InternalHom.RestrictionHomCompatible j N M q := by
  intro i k
  exact overlapRestrictIso_refinement_comparison (a i k) (b i k) (j i) (j k)
    (c i k) (H i k) (ha i k) (hb i k) N M (q i) (q k) (qW i k) (hU i k) (hV i k)

end AlgebraicGeometry.Scheme.Modules
