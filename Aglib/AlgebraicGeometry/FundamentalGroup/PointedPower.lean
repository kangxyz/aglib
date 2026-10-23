/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.FundamentalGroup.PointedPrecomposition
public import Mathlib.Algebra.Group.Pi.Lemmas

/-! # Powers of original pointed fibre automorphisms

The actual pullback-fibre equivalence transports finite-order component
identities. All geometric maps remain typed parameters in this proof.
-/

@[expose] public noncomputable section

open CategoryTheory AlgebraicGeometry
open Scheme.FiniteEtale

namespace AlgebraicGeometry.Scheme.EtaleFundamentalGroups

universe u

/-- An identity power of a pointed image component is an identity power
of the original component on the actual pulled-back cover. -/
theorem component_pow_eq_one_of_pointedMap
    {K : Type u} [Field K] {S X : PointedScheme K} (f : S ⟶ X)
    (a : FiberAutGroup S.hom) (Y : Scheme.FiniteEtale X.right) (n : ℕ)
    (h : PreGaloisCategory.autEmbedding (fiberToFinite X.hom) (pointedMap f a) Y ^ n = 1) :
    PreGaloisCategory.autEmbedding (fiberToFinite S.hom) a
      ((baseChange f.right).obj Y) ^ n = 1 := by
  let ev : FiberAutGroup X.hom →* Aut ((fiberToFinite X.hom).obj Y) :=
    (Pi.evalMonoidHom _ Y).comp (PreGaloisCategory.autEmbedding (fiberToFinite X.hom))
  let Y' := (baseChange f.right).obj Y
  let ev' : FiberAutGroup S.hom →* Aut ((fiberToFinite S.hom).obj Y') :=
    (Pi.evalMonoidHom _ Y').comp (PreGaloisCategory.autEmbedding (fiberToFinite S.hom))
  have hp : ev (pointedMap f (a ^ n)) = 1 := by
    rw [map_pow, map_pow]
    exact h
  change ev' a ^ n = 1
  rw [← map_pow]
  apply Aut.ext
  apply FintypeCat.hom_ext
  intro z
  have hz := congrArg (fun k : Aut ((fiberToFinite X.hom).obj Y) =>
    k.hom ((pointedFiberEquiv f Y).symm z)) hp
  change (pointedMap f (a ^ n)).hom.app Y
    ((pointedFiberEquiv f Y).symm z) = (pointedFiberEquiv f Y).symm z at hz
  rw [pointedMap_apply] at hz
  have he := congrArg (fun t : (fiberToFinite S.hom).obj Y' =>
    (pointedFiberEquiv f Y).symm ((ev' (a ^ n)).hom t))
    ((pointedFiberEquiv f Y).apply_symm_apply z)
  exact (pointedFiberEquiv f Y).symm.injective (he.symm.trans hz)

end AlgebraicGeometry.Scheme.EtaleFundamentalGroups
