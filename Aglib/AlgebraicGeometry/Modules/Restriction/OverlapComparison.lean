/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.Modules.Restriction.OverlapQuotient

/-! # Original module comparisons on cartesian overlap presentations -/

@[expose] public noncomputable section
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false

open CategoryTheory CategoryTheory.Limits
universe u
namespace AlgebraicGeometry.Scheme.Modules

/-- Comparisons agreeing on a cartesian presentation satisfy the original
categorical overlap equation. Both ambient modules retain their canonical
restriction isomorphisms. -/
theorem overlapRestrictIso_refinement_comparison
    {W U V X : Scheme.{u}} (a : W ⟶ U) (b : W ⟶ V)
    (j : U ⟶ X) (k : V ⟶ X) (c : W ⟶ X)
    [IsOpenImmersion a] [IsOpenImmersion b] [IsOpenImmersion j]
    [IsOpenImmersion k] [IsOpenImmersion c]
    (H : IsPullback a b j k) (ha : a ≫ j = c) (hb : b ≫ k = c)
    (N M : X.Modules)
    (qU : N.restrict j ⟶ M.restrict j)
    (qV : N.restrict k ⟶ M.restrict k)
    (qW : N.restrict c ⟶ M.restrict c)
    (hU : (restrictFunctor a).map qU ≫
        ((restrictFunctorComp a j).symm.app M ≪≫ (restrictFunctorCongr ha).app M).hom =
      ((restrictFunctorComp a j).symm.app N ≪≫ (restrictFunctorCongr ha).app N).hom ≫ qW)
    (hV : (restrictFunctor b).map qV ≫
        ((restrictFunctorComp b k).symm.app M ≪≫ (restrictFunctorCongr hb).app M).hom =
      ((restrictFunctorComp b k).symm.app N ≪≫ (restrictFunctorCongr hb).app N).hom ≫ qW) :
    (restrictFunctor (pullback.fst j k)).map qU ≫ (overlapRestrictIso j k).hom.app M =
      (overlapRestrictIso j k).hom.app N ≫ (restrictFunctor (pullback.snd j k)).map qV := by
  have hh := overlapRestrictIso_refinement_quotient a b j k c H ha hb N
    (M.restrict j) (M.restrict k) (M.restrict c) qU qV qW
    ((restrictFunctorComp a j).symm.app M ≪≫ (restrictFunctorCongr ha).app M)
    ((restrictFunctorComp b k).symm.app M ≪≫ (restrictFunctorCongr hb).app M) hU hV
  have hm := overlapRestrictIso_refinement a b j k c H ha hb M
  dsimp only at hh hm
  rw [hm] at hh
  exact hh

end AlgebraicGeometry.Scheme.Modules
