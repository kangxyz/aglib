/-
Copyright (c) 2026 algebraic-geometry contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.Modules.QuasiCoherent.Affine.ChartPullbackCoordinateRestriction

/-! # Postcomposition of original chart-coordinate restrictions

The original section restriction and coordinate unit are kept under one shared
predicate. Postcomposition is proved before specializing any of the four chart
rings, source coefficients, or target coordinate functions.
-/

@[expose] public noncomputable section
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

universe u v
open CategoryTheory
open scoped TensorProduct

namespace AlgebraicGeometry.Scheme.Modules

variable {R S T : Type u} [CommRing R] [CommRing S] [CommRing T]
  [Algebra R S] {X Z : Scheme.{u}} (p : Z ⟶ X)
  (j : Spec (CommRingCat.of R) ⟶ X) [IsOpenImmersion j]
  (c : Spec (CommRingCat.of S) ⟶ Z) (d : Spec (CommRingCat.of T) ⟶ Z)
  [IsOpenImmersion c] [IsOpenImmersion d]
  (φ : CommRingCat.of S ⟶ CommRingCat.of T) [IsOpenImmersion (Spec.map φ)]
  (hc : Spec.map φ ≫ c = d)
  (HU : c ≫ p = Spec.map (CommRingCat.ofHom (algebraMap R S)) ≫ j)
  (M : X.Modules) [M.IsQuasicoherent] {N : ModuleCat.{u} R}
  (e : moduleSpecΓFunctor.obj (M.restrict j) ≅ N) {P : Type v}
  (q : moduleSpecΓFunctor.obj (((pullback p).obj M).restrict d) → P)
  (z : N → P) (m : N)

/-- The image of the original restricted coordinate unit under a specified
target function, with no linearity requirement on that function. -/
def chartPullbackCoordinatesRestrictionPostcomposeEquation : Prop :=
  q (affineChartSectionRestriction φ c d hc ((pullback p).obj M)
      ((chartPullbackCoordinatesIso p j c HU M e).inv ((1 : S) ⊗ₜ[R] m))) = z m

/-- A native chart-refinement equation and the smaller chart's coordinate-unit
image determine the image of the original restricted unit. -/
theorem chartPullbackCoordinatesRestrictionPostcomposeEquation_of_refinement
    {R' : Type u} [CommRing R'] [Algebra R' T]
    (j' : Spec (CommRingCat.of R') ⟶ X) [IsOpenImmersion j']
    (HV : d ≫ p = Spec.map (CommRingCat.ofHom (algebraMap R' T)) ≫ j')
    {N' : ModuleCat.{u} R'} (e' : moduleSpecΓFunctor.obj (M.restrict j') ≅ N')
    (r : N → N')
    (hr : chartPullbackCoordinatesRefinementEquation p j j' c d φ hc HU HV M e e' r m)
    (hq : q ((chartPullbackCoordinatesIso p j' d HV M e').inv
      ((1 : T) ⊗ₜ[R'] r m)) = z m) :
    chartPullbackCoordinatesRestrictionPostcomposeEquation p j c d φ hc HU M e q z m := by
  have hs := congrArg q hr
  exact hs.trans hq

end AlgebraicGeometry.Scheme.Modules
