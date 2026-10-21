/-
Copyright (c) 2026 algebraic-geometry contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.Algebra.Category.ModuleCat.ChangeOfRings.PresentationCompatibility
public import Aglib.Algebra.Category.ModuleCat.ChangeOfRings.PresentationUnit
public import Aglib.AlgebraicGeometry.Modules.QuasiCoherent.Pullback
public import Aglib.AlgebraicGeometry.Modules.QuasiCoherent.Affine.ChartScalarRestriction
public import Aglib.AlgebraicGeometry.Modules.QuasiCoherent.Affine.ChartPullbackCoordinateRestrictionPostcompose

/-! # Presentation compatibility on original pullback charts

Original presentation-unit and restricted-unit predicates determine the whole
scalar restriction square. Their elimination and the scalar unit calculation
take place before specializing the chart rings or quasicoherent coefficient.
-/

@[expose] public noncomputable section
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

universe u
open CategoryTheory
open scoped TensorProduct ChangeOfRings

namespace AlgebraicGeometry.Scheme.Modules

variable {B R S : Type u} [CommRing B] [CommRing R] [CommRing S]
  [Algebra B R] {X Z : Scheme.{u}} (p : Z ⟶ X)
  (j : Spec (CommRingCat.of B) ⟶ X) [IsOpenImmersion j]
  (c : Spec (CommRingCat.of R) ⟶ Z) (d : Spec (CommRingCat.of S) ⟶ Z)
  [IsOpenImmersion c] [IsOpenImmersion d]
  (φ : CommRingCat.of R ⟶ CommRingCat.of S) [IsOpenImmersion (Spec.map φ)]
  (hc : Spec.map φ ≫ c = d)
  (HU : c ≫ p = Spec.map (CommRingCat.ofHom (algebraMap B R)) ≫ j)
  (M : X.Modules) [M.IsQuasicoherent] {L : ModuleCat.{u} B}
  (e : moduleSpecΓFunctor.obj (M.restrict j) ≅ L)
  {N : ModuleCat.{u} R} {N' : ModuleCat.{u} S}
  (q : moduleSpecΓFunctor.obj (((pullback p).obj M).restrict c) ⟶ N)
  (q' : moduleSpecΓFunctor.obj (((pullback p).obj M).restrict d) ⟶ N')
  (dN : (ModuleCat.extendScalars φ.hom).obj N ⟶ N')
  (i : L → N) (jj : L → N')

/-- The whole original presentation square follows from its original unit
images and the native chart restriction, with no extra geometric hypothesis. -/
theorem chartPullbackPresentationCompatible_of_unit_equations
    (hq : ∀ m, ModuleCat.algebraTensorPresentationUnitEquation
      (chartPullbackCoordinatesIso p j c HU M e) q m (i m))
    (hd : ∀ m, dN ((1 : S) ⊗ₜ[R,φ.hom] i m) = jj m)
    (hq' : ∀ m, chartPullbackCoordinatesRestrictionPostcomposeEquation
      p j c d φ hc HU M e (fun x => q' x) jj m) :
    ModuleCat.algebraTensorPresentationCompatible φ.hom
      (chartPullbackCoordinatesIso p j c HU M e) q q' dN
      (affineChartScalarRestriction φ c d hc ((pullback p).obj M)) := by
  apply ModuleCat.algebraTensorPresentationCompatible_of_unit_equations φ.hom
    (chartPullbackCoordinatesIso p j c HU M e) q q' dN
    (affineChartScalarRestriction φ c d hc ((pullback p).obj M)) i jj
    (fun m => affineChartSectionRestriction φ c d hc ((pullback p).obj M)
      ((chartPullbackCoordinatesIso p j c HU M e).inv ((1 : R) ⊗ₜ[B] m)))
  · exact hq
  · exact hd
  · intro m
    exact affineChartScalarRestriction_one_tmul φ c d hc ((pullback p).obj M) _
  · exact hq'

end AlgebraicGeometry.Scheme.Modules
