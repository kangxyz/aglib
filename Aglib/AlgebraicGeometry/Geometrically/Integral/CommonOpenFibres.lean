/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.Limits.ImmersionBaseChange
public import Aglib.AlgebraicGeometry.Morphisms.Flat.GenericFiberCriteria

/-! # Integrality from the original common open after base change

Both arrows use the same original object of the over category and the same
native pullback functor. Density is measured in the original target fibre.
The target fibre must be nonempty and reduced; neither condition is replaced
by a common-open or geometric-integrality certificate.
-/

@[expose] public noncomputable section

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false

open CategoryTheory Limits

namespace AlgebraicGeometry.Scheme

universe u

/-- An original common open transfers fibrewise integrality from one family
to the other when its inverse image is dense and the other fibre is reduced
and nonempty. Both base-changed arrows are the actual `Over.pullback` maps. -/
theorem isIntegral_pullback_of_dense_common_open
    {S T : Scheme.{u}} (b : T ⟶ S) {V X Y : Over S}
    (i : V ⟶ X) (j : V ⟶ Y) [IsOpenImmersion j.left]
    [IsIntegral (pullback Y.hom b)] [IsReduced (pullback X.hom b)]
    [Nonempty (pullback X.hom b : Scheme.{u})]
    (hd : Dense (pullback.fst X.hom b ⁻¹' Set.range i.left)) :
    IsIntegral (pullback X.hom b) := by
  let iT : pullback V.hom b ⟶ pullback X.hom b := ((Over.pullback b).map i).left
  let jT : pullback V.hom b ⟶ pullback Y.hom b := ((Over.pullback b).map j).left
  have hr : Set.range iT = pullback.fst X.hom b ⁻¹' Set.range i.left :=
    Pullback.Fibre.pullback_range_snd (isPullback_overPullbackMap b i)
  have hdi : DenseRange iT := by
    change Dense (Set.range iT)
    rw [hr]
    exact hd
  let : Nonempty (pullback V.hom b : Scheme.{u}) := hdi.nonempty
  let : IsOpenImmersion jT :=
    MorphismProperty.overPullbackMap (P := @IsOpenImmersion) b j inferInstance
  let : IsIntegral (pullback V.hom b) := isIntegral_of_isOpenImmersion jT
  let : IsDominant iT := ⟨hdi⟩
  exact LocalRing.GenericFiber.integral_of_dense_integral_source iT

end AlgebraicGeometry.Scheme
