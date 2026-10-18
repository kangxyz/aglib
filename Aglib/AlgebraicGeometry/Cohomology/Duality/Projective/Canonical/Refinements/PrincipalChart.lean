/-
Copyright (c) 2026 algebraic-geometry contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import
  Aglib.AlgebraicGeometry.Cohomology.Duality.Projective.Canonical.LocalCharts.Quotient
public import Aglib.AlgebraicGeometry.Spec.Localization

/-!
# The actual principal refinement of a smooth regular chart

The ambient and quotient principal localizations retain the original
closed square, ordered localized regular list, smooth dimensions and
chosen point. This constructs the refinements used in canonical-map
compatibility from the original chart, rather than assuming a coherent
family of regular lists or frames.
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

/-- An actual principal refinement, retaining the same original base and ordered generators. -/
def principalChart (a : C.A) (ha : C.σ a ∉ C.point.asIdeal) :
    SmoothClosedImmersionLocalChart i p n d x := by
  let A' : CommRingCat := .of (Localization.Away a)
  let B' : CommRingCat := .of (Localization.Away (C.σ a))
  let locA : C.A ⟶ A' := CommRingCat.ofHom (algebraMap C.A A')
  let locB : C.B ⟶ B' := CommRingCat.ofHom (algebraMap C.B B')
  let σ' : A' ⟶ B' := CommRingCat.ofHom
    (IsLocalization.Away.map A' B' C.σ.hom a)
  have hσ' : Function.Surjective σ' :=
    IsLocalization.map_surjective_of_surjective (Submonoid.powers a) A' B' C.surjective
  have hpoint : ∃ q : PrimeSpectrum B', PrimeSpectrum.comap locB.hom q = C.point := by
    change C.point ∈ Set.range (PrimeSpectrum.comap (algebraMap C.B B'))
    rw [PrimeSpectrum.localization_away_comap_range B' (C.σ a)]
    exact ha
  let q := Classical.choose hpoint
  have hq : PrimeSpectrum.comap locB.hom q = C.point := Classical.choose_spec hpoint
  let hp := Scheme.isPullback_specMap_localizationAway C.σ a
  have hα : C.α ≫ locA ≫ σ' = (C.α ≫ C.σ) ≫ locB := by
    ext r
    change IsLocalization.Away.map A' B' C.σ.hom a
      (algebraMap C.A A' (C.α r)) = algebraMap C.B B' (C.σ (C.α r))
    simp only [IsLocalization.Away.map, IsLocalization.map_eq]
  have hA : RingHom.IsStandardSmoothOfRelativeDimension n (C.α ≫ locA).hom :=
    (RingHom.isStandardSmoothOfRelativeDimension_stableUnderCompositionWithLocalizationAway
      n).right A' a C.α.hom C.ambientSmooth
  have hB : RingHom.IsStandardSmoothOfRelativeDimension d (C.α ≫ locA ≫ σ').hom := by
    rw [hα]
    exact (RingHom.isStandardSmoothOfRelativeDimension_stableUnderCompositionWithLocalizationAway
      d).right B' (C.σ a) (C.α ≫ C.σ).hom C.sourceSmooth
  let : Module.Flat C.A A' := IsLocalization.flat A' (Submonoid.powers a)
  have hker : Ideal.ofList (C.regularList.map (algebraMap C.A A')) = RingHom.ker σ'.hom := by
    have h := CommRingCat.ker_localizationAway_map C.σ a
    change RingHom.ker σ'.hom = (RingHom.ker C.σ.hom).map (algebraMap C.A A') at h
    rw [← C.kernel, Ideal.map_ofList] at h
    exact h.symm
  exact {
    R := C.R
    A := A'
    B := B'
    α := C.α ≫ locA
    σ := σ'
    surjective := hσ'
    jY := C.jY
    jP := Spec.map locA ≫ C.jP
    jX := Spec.map locB ≫ C.jX
    openY := C.openY
    openP := inferInstance
    openX := inferInstance
    ambientSquare := by
      rw [Spec.map_comp, Category.assoc, C.ambientSquare, Category.assoc]
    closedSquare := by
      rw [← Category.assoc, hp.w, Category.assoc, C.closedSquare, Category.assoc]
    cartesian := hp.flip.paste_horiz C.cartesian
    point := q
    point_eq := (congrArg C.jX hq).trans C.point_eq
    regularList := C.regularList.map (algebraMap C.A A')
    weaklyRegular := C.weaklyRegular.of_flat
    kernel := hker
    ambientSmooth := hA
    sourceSmooth := hB }

end SmoothClosedImmersionLocalChart
end AlgebraicGeometry.Scheme.Modules.Differentials
