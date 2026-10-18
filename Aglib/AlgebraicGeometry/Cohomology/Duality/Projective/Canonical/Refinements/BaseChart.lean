/-
Copyright (c) 2026 algebraic-geometry contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import
  Aglib.AlgebraicGeometry.Cohomology.Duality.Projective.Canonical.Refinements.PrincipalChart

/-!
# Actual principal refinement of the common affine base

The base localization and its two original spectral inverse images retain
the same closed chart, localized ordered regular list and chosen point.
Native localization preservation supplies the original standard-smooth
dimensions over the new base ring.
-/

@[expose] public section
noncomputable section

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open CategoryTheory AlgebraicGeometry

universe u
namespace AlgebraicGeometry.Scheme.Modules.Differentials
namespace SmoothClosedImmersionLocalChart

attribute [local instance] SmoothClosedImmersionLocalChart.openX
  SmoothClosedImmersionLocalChart.openP SmoothClosedImmersionLocalChart.openY

variable {X P Y : Scheme.{u}} {i : X ⟶ P} {p : P ⟶ Y} {n d : ℕ} {x : X}
  (C : SmoothClosedImmersionLocalChart i p n d x)

/-- Principal base refinement uses the actual inverse-image localizations of both charts. -/
def basePrincipalChart (r : C.R) (hr : C.σ (C.α r) ∉ C.point.asIdeal) :
    SmoothClosedImmersionLocalChart i p n d x := by
  let R' : CommRingCat := .of (Localization.Away r)
  let A' : CommRingCat := .of (Localization.Away (C.α r))
  let B' : CommRingCat := .of (Localization.Away (C.σ (C.α r)))
  let locR : C.R ⟶ R' := CommRingCat.ofHom (algebraMap C.R R')
  let α' : R' ⟶ A' := CommRingCat.ofHom (IsLocalization.Away.map R' A' C.α.hom r)
  let β' : R' ⟶ B' := CommRingCat.ofHom
    (IsLocalization.Away.map R' B' (C.α ≫ C.σ).hom r)
  let D := C.principalChart (C.α r) hr
  have hcomp : α' ≫ D.σ = β' := by
    apply CommRingCat.hom_ext
    apply IsLocalization.ringHom_ext (Submonoid.powers r)
    ext z
    change IsLocalization.Away.map A' B' C.σ.hom (C.α r)
        (IsLocalization.Away.map R' A' C.α.hom r (algebraMap C.R R' z)) =
      IsLocalization.Away.map R' B' (C.α ≫ C.σ).hom r (algebraMap C.R R' z)
    simp only [IsLocalization.Away.map, IsLocalization.map_eq]
    rfl
  have hA : RingHom.IsStandardSmoothOfRelativeDimension n α'.hom :=
    (RingHom.isStandardSmoothOfRelativeDimension_localizationPreserves n).away
      C.α.hom r R' A' C.ambientSmooth
  have hB : RingHom.IsStandardSmoothOfRelativeDimension d (α' ≫ D.σ).hom := by
    rw [hcomp]
    exact (RingHom.isStandardSmoothOfRelativeDimension_localizationPreserves d).away
      (C.α ≫ C.σ).hom r R' B' C.sourceSmooth
  let hp := Scheme.isPullback_specMap_localizationAway C.α r
  exact {
    R := R'
    A := D.A
    B := D.B
    α := α'
    σ := D.σ
    surjective := D.surjective
    jY := Spec.map locR ≫ C.jY
    jP := D.jP
    jX := D.jX
    openY := inferInstance
    openP := D.openP
    openX := D.openX
    ambientSquare := by
      change Spec.map α' ≫ (Spec.map locR ≫ C.jY) =
        (Spec.map (CommRingCat.ofHom (algebraMap C.A A')) ≫ C.jP) ≫ p
      rw [← Category.assoc, hp.w, Category.assoc, C.ambientSquare, Category.assoc]
    closedSquare := D.closedSquare
    cartesian := D.cartesian
    point := D.point
    point_eq := D.point_eq
    regularList := D.regularList
    weaklyRegular := D.weaklyRegular
    kernel := D.kernel
    ambientSmooth := hA
    sourceSmooth := hB }

end SmoothClosedImmersionLocalChart
end AlgebraicGeometry.Scheme.Modules.Differentials
