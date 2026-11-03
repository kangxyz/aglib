/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.Limits.IntegralOpenOverlap
public import Aglib.AlgebraicGeometry.Modules.Invertible.GenericUniqueness.Open
public import Aglib.AlgebraicGeometry.Modules.Invertible.Nonvanishing.Pullback


/-!
# Ordinary local unit-square uniqueness from an actual open isomorphism

The original arrow is invertible on one actual nonempty open. Pulling back
that open to another original open chart gives an actual nonempty overlap.
Native functor comparisons carry its isomorphism, and ordinary line-target
uniqueness gives injectivity of precomposition. No raw evaluation is canceled.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits
open AlgebraicGeometry.Scheme.Modules

universe u


open AlgebraicGeometry.Scheme

namespace AlgebraicGeometry.Scheme.Modules.Invertible

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
/-- An original arrow invertible on one nonempty open determines line-valued maps
on every original nonempty open chart by their actual precomposition. -/
theorem openUnitSquare_precomp_injective {X U V : Scheme.{u}} [IsIntegral X]
    [Nonempty U] [Nonempty V] (j : U ⟶ X) (f : V ⟶ X)
    [IsOpenImmersion j] [IsOpenImmersion f]
    {P M : X.Modules} (β : P ⟶ M) (L : Invertible.LineBundle X)
    [IsIso ((Scheme.Modules.pullback j).map β)]
    {r s : (Scheme.Modules.restrictFunctor f).obj M ⟶
      (Scheme.Modules.restrictFunctor f).obj L.val}
    (h : (Scheme.Modules.restrictFunctor f).map β ≫ r =
      (Scheme.Modules.restrictFunctor f).map β ≫ s) : r = s := by
  let _ : IsIntegral V := isIntegral_of_isOpenImmersion f
  let _ : Nonempty (CategoryTheory.Limits.pullback f j : Scheme) := nonempty_openOverlap f j
  let p := CategoryTheory.Limits.pullback.fst f j
  let q := CategoryTheory.Limits.pullback.snd f j
  let e : Scheme.Modules.restrictFunctor f ⋙ Scheme.Modules.pullback p ≅
      Scheme.Modules.pullback j ⋙ Scheme.Modules.pullback q :=
    CategoryTheory.Functor.isoWhiskerRight (Scheme.Modules.restrictFunctorIsoPullback f)
      (Scheme.Modules.pullback p) ≪≫
      pullbackComp p f ≪≫
        pullbackCongr (CategoryTheory.Limits.pullback.condition (f := f) (g := j)) ≪≫
        (pullbackComp q j).symm
  let _ : IsIso ((Scheme.Modules.pullback p).map ((Scheme.Modules.restrictFunctor f).map β)) :=
    (NatIso.isIso_map_iff e β).mpr
      (inferInstanceAs (IsIso ((Scheme.Modules.pullback q).map
        ((Scheme.Modules.pullback j).map β))))
  apply Invertible.hom_ext_of_nonempty_pullback p
    (Invertible.Nonvanishing.restrictLineBundle f L).property
  apply (cancel_epi
    ((Scheme.Modules.pullback p).map ((Scheme.Modules.restrictFunctor f).map β))).mp
  simpa only [CategoryTheory.Functor.map_comp] using
    congrArg (fun t => (Scheme.Modules.pullback p).map t) h

end AlgebraicGeometry.Scheme.Modules.Invertible
