/-
Copyright (c) 2026 algebraic-geometry contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.Cohomology.BaseChange.HigherDirectImage.Nonflat.Charts
public import Aglib.AlgebraicGeometry.Cohomology.BaseChange.HigherDirectImage.Nonflat.Cartesian
public import Aglib.AlgebraicGeometry.Cohomology.BaseChange.HigherDirectImage.Nonflat.ChartAdjoint

/-! # Original scalar criteria for the actual chart comparison

The original scalar map on the chosen fibre product detects invertibility and
surjectivity on sections of the actual chart map. The comparison retains the
actual cartesian isomorphism and the original restricted coefficient adjoint.
-/

@[expose] public section

noncomputable section

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

namespace AlgebraicGeometry.Scheme.Modules.Nonflat

open Cohomology

variable {W U V X : Scheme.{u}}
  (a : W ⟶ U) (b : W ⟶ V) (f : U ⟶ X) (g : V ⟶ X)
  (h : IsPullback a b f g) [QuasiCompact f] [QuasiSeparated f]
  {R S : CommRingCat.{u}} (j : Spec R ⟶ X) (v : Spec S ⟶ V) (σ : R ⟶ S)
  [IsOpenImmersion j] [IsOpenImmersion v] (hv : Spec.map σ ≫ j = v ≫ g)
  (n : ℕ) (M : U.Modules) [M.IsQuasicoherent]

/-- The actual chart comparison is invertible exactly when the original scalar
base-change map on the genuine chosen fibre product is invertible. -/
theorem chartMap_isIso_iff :
    IsIso (chartMap a b f g h j v σ hv n M) ↔
      IsIso (moduleCohomologyBaseChangeMap (Limits.pullback.snd f j) σ.hom
        (M.restrict (Limits.pullback.fst f j)) n) := by
  let : QuasiCompact b := MorphismProperty.of_isPullback h inferInstance
  let : QuasiSeparated b := MorphismProperty.of_isPullback h inferInstance
  let p := Limits.pullback.fst f j
  let d := Limits.pullback.snd f j
  let c := Limits.pullback.fst b v
  let e := Limits.pullback.snd b v
  let q := chartUpper a b f g h j v σ hv
  let N := (pullback a).obj M
  let ψ : M.restrict p ⟶ (pushforward q).obj (N.restrict c) :=
    chartCoefficient a p c q (chartUpper_fst a b f g h j v σ hv)
      ((pullbackPushforwardAdjunction a).unit.app M)
  let β := higherDirectImageAffineMap (M := M.restrict p) (N := N.restrict c)
    q e d σ (chartUpper_snd a b f g h j v σ hv) ψ n
  have hψ : IsIso (((pullbackPushforwardAdjunction q).homEquiv _ _).symm ψ) :=
    chartCoefficient_pullbackUnit_adjoint_isIso a p c q
      (chartUpper_fst a b f g h j v σ hv) M
  have hβ : IsIso β ↔ IsIso (moduleCohomologyBaseChangeMap d σ.hom (M.restrict p) n) :=
    (higherDirectImageAffineMap_isIso_iff q e d σ
      (chartUpper_snd a b f g h j v σ hv) ψ n).trans
      (moduleCohomologyTensorMap_isIso_iff_baseChangeMap_of_isPullback_of_isIso_adjoint
        q e d σ.hom (chartUpper_isPullback a b f g h j v σ hv) ψ hψ n)
  change IsIso (_ ≫ _ ≫ β ≫ _) ↔ _
  rw [isIso_comp_left_iff, isIso_comp_left_iff, isIso_comp_right_iff]
  exact hβ

/-- Surjectivity on actual chart sections is exactly surjectivity of the original scalar
base-change map, with the original cartesian and coefficient isomorphisms retained. -/
theorem chartMap_sections_epi_iff :
    Epi (moduleSpecΓFunctor.map (chartMap a b f g h j v σ hv n M)) ↔
      Epi (moduleCohomologyBaseChangeMap (Limits.pullback.snd f j) σ.hom
        (M.restrict (Limits.pullback.fst f j)) n) := by
  let : QuasiCompact b := MorphismProperty.of_isPullback h inferInstance
  let : QuasiSeparated b := MorphismProperty.of_isPullback h inferInstance
  let p := Limits.pullback.fst f j
  let d := Limits.pullback.snd f j
  let c := Limits.pullback.fst b v
  let e := Limits.pullback.snd b v
  let q := chartUpper a b f g h j v σ hv
  let N := (pullback a).obj M
  let ψ : M.restrict p ⟶ (pushforward q).obj (N.restrict c) :=
    chartCoefficient a p c q (chartUpper_fst a b f g h j v σ hv)
      ((pullbackPushforwardAdjunction a).unit.app M)
  let β := higherDirectImageAffineMap (M := M.restrict p) (N := N.restrict c)
    q e d σ (chartUpper_snd a b f g h j v σ hv) ψ n
  have hψ : IsIso (((pullbackPushforwardAdjunction q).homEquiv _ _).symm ψ) :=
    chartCoefficient_pullbackUnit_adjoint_isIso a p c q
      (chartUpper_fst a b f g h j v σ hv) M
  have hβ : Epi (moduleSpecΓFunctor.map β) ↔
      Epi (moduleCohomologyBaseChangeMap d σ.hom (M.restrict p) n) :=
    (higherDirectImageAffineMap_sections_epi_iff q e d σ
      (chartUpper_snd a b f g h j v σ hv) ψ n).trans
      (moduleCohomologyTensorMap_epi_iff_baseChangeMap_of_isPullback_of_isIso_adjoint
        q e d σ.hom (chartUpper_isPullback a b f g h j v σ hv) ψ hψ n)
  change Epi (moduleSpecΓFunctor.map (_ ≫ _ ≫ β ≫ _)) ↔ _
  simp only [Functor.map_comp, epi_comp_iff_of_epi, epi_comp_iff_of_isIso]
  exact hβ

end AlgebraicGeometry.Scheme.Modules.Nonflat
