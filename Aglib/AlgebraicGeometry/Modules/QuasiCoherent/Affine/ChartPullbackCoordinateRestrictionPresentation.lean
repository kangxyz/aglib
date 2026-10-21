/-
Copyright (c) 2026 algebraic-geometry contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.Algebra.Category.ModuleCat.ChangeOfRings.PresentationUnit
public import Aglib.AlgebraicGeometry.Modules.QuasiCoherent.Affine.ChartPullbackCoordinateRestrictionPostcompose

/-! # Original presentation units after chart restriction

The smaller chart's presentation unit is accepted through its shared regular
predicate. Its elimination is performed with all four chart rings and source
coefficients abstract, before any concrete presentation is substituted.
-/

@[expose] public noncomputable section
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

universe u
open CategoryTheory

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
  (e : moduleSpecΓFunctor.obj (M.restrict j) ≅ N) {P : ModuleCat.{u} T}
  (q : moduleSpecΓFunctor.obj (((pullback p).obj M).restrict d) ⟶ P)
  (z : N → P) (m : N)

/-- A native refinement and the original smaller-chart presentation unit give
the original restricted unit's image under the same presentation morphism. -/
theorem chartPullbackCoordinatesRestrictionPostcomposeEquation_of_presentation_unit
    {R' : Type u} [CommRing R'] [Algebra R' T]
    (j' : Spec (CommRingCat.of R') ⟶ X) [IsOpenImmersion j']
    (HV : d ≫ p = Spec.map (CommRingCat.ofHom (algebraMap R' T)) ≫ j')
    {N' : ModuleCat.{u} R'} (e' : moduleSpecΓFunctor.obj (M.restrict j') ≅ N')
    (r : N → N')
    (hr : chartPullbackCoordinatesRefinementEquation p j j' c d φ hc HU HV M e e' r m)
    (hq : ModuleCat.algebraTensorPresentationUnitEquation
      (chartPullbackCoordinatesIso p j' d HV M e') q (r m) (z m)) :
    chartPullbackCoordinatesRestrictionPostcomposeEquation p j c d φ hc HU M e
      (fun x => q x) z m := by
  exact chartPullbackCoordinatesRestrictionPostcomposeEquation_of_refinement
    p j c d φ hc HU M e (fun x => q x) z m j' HV e' r hr hq

end AlgebraicGeometry.Scheme.Modules
