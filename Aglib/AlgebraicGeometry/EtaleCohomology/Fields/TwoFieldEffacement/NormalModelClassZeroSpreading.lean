/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.EtaleCohomology.Continuity.GenericCoefficientZeroSpreading
public import Aglib.AlgebraicGeometry.Normalization.GenericFiniteEtale.SeparableBaseSquare
public import Mathlib.FieldTheory.SeparableDegree

/-! # Original classes on a finite normal coefficient model

Given an actual generic Cartesian square and its original class zero, construct
the literal finite normal coefficient model and spread that zero to a nonempty
principal open. The effacement consumer supplies the generic zero internally.
This lower does not assert target-point or whole-fibre local vanishing.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite
open IsLocalization.PrincipalDiagram
open AlgebraicGeometry.Scheme.PrincipalNeighborhoodLimit
open scoped nonZeroDivisors

namespace AlgebraicGeometry.Scheme.EtaleCohomology.TwoFieldEffacement

universe u eX
attribute [local instance] hasSheafifyLarge HasExt.standard

/-- The original generic Cartesian square over a finite model is obtained by
cancelling its original base-change square. No second generic fibre is chosen. -/
private theorem spread_on_fraction_model
    (B R E : Type u) [CommRing B] [CommRing R] [IsDomain R] [Field E]
    [Algebra B R] [Algebra B E] [Algebra R E] [IsScalarTower B R E]
    [IsFractionRing R E]
    {Y T : Scheme.{u}} (e : Y ⟶ Spec (.of B))
    [QuasiCompact e] [QuasiSeparated e]
    [HasExt.{eX} (AbelianSheaf.{u, u + 1} Y)]
    (a : T ⟶ Y) (b : T ⟶ Spec (.of E))
    (H : IsPullback a b e (Spec.algebraMap B E))
    (M : AbelianSheaf.{u, u + 1} Y) (q : ℕ) (c : Sheaf.H.{eX} M q)
    (hc : cohomologyPullback.{u, eX, u + 2} a M q c = 0) :
    ∃ s : Finset R⁰, denominator R⁰ s ≠ 0 ∧ Nonempty (stageBaseOpen R⁰ s) ∧
      cohomologyPullback.{u, eX, u + 2}
        ((stageSourceOpen R⁰ (pullback.snd e (Spec.algebraMap B R)) s).ι ≫
          pullback.fst e (Spec.algebraMap B R)) M q c = 0 := by
  have ht : Spec.algebraMap R E ≫ Spec.algebraMap B R = Spec.algebraMap B E := by
    rw [← Spec.map_comp]
    exact congrArg Spec.map (CommRingCat.hom_ext
      (IsScalarTower.algebraMap_eq B R E).symm)
  let v : T ⟶ pullback e (Spec.algebraMap B R) :=
    pullback.lift a (b ≫ Spec.algebraMap R E)
      (H.w.trans (by rw [Category.assoc, ht]))
  have hv : v ≫ pullback.fst e (Spec.algebraMap B R) = a := pullback.lift_fst ..
  have Houter : IsPullback (v ≫ pullback.fst e (Spec.algebraMap B R)) b e
      (Spec.algebraMap R E ≫ Spec.algebraMap B R) := by
    rw [hv, ht]
    exact H
  have HR : IsPullback v b (pullback.snd e (Spec.algebraMap B R))
      (Spec.algebraMap R E) :=
    Houter.of_right (pullback.lift_snd ..) (IsPullback.of_hasPullback e _)
  let : QuasiSeparatedSpace (pullback e (Spec.algebraMap B R) : Scheme.{u}) :=
    quasiSeparatedSpace_of_quasiSeparated (pullback.snd e (Spec.algebraMap B R))
  exact Continuity.exists_fraction_principalOpen_composite_zero_of_reconstruction
    R E (pullback.snd e (Spec.algebraMap B R)) (pullback.fst e (Spec.algebraMap B R))
    v b HR (𝟙 T) a (by simpa only [Category.id_comp] using hv.symm) M q c hc

/-- The same literal finite normal model and an actual nonempty principal zero.
The ambient field and coefficient action remain explicit parameters. -/
def NormalPrincipalOpenClassZero
    (B E : Type u) [CommRing B] [Field E] [Algebra B E]
    {Y : Scheme.{u}} (e : Y ⟶ Spec (.of B))
    [HasExt.{eX} (AbelianSheaf.{u, u + 1} Y)]
    (M : AbelianSheaf.{u, u + 1} Y) (q : ℕ) (c : Sheaf.H.{eX} M q) : Prop :=
  let R := integralClosure B E
  Module.Finite B R ∧ IsNoetherianRing R ∧ IsIntegrallyClosed R ∧
    IsFractionRing R E ∧ IsFinite (Spec.algebraMap B R) ∧
    ∃ s : Finset R⁰, denominator R⁰ s ≠ 0 ∧ Nonempty (stageBaseOpen R⁰ s) ∧
      cohomologyPullback.{u, eX, u + 2}
        ((stageSourceOpen R⁰ (pullback.snd e (Spec.algebraMap B R)) s).ι ≫
          pullback.fst e (Spec.algebraMap B R)) M q c = 0

/-- Normalize in the given finite separable field, retain the original generic
Cartesian source, and spread its original class zero by fraction continuity. -/
theorem normal_principalOpen_class_zero_of_generic_zero
    (B L E : Type u) [CommRing B] [IsDomain B] [IsNoetherianRing B]
    [IsIntegrallyClosed B] [Field L] [Field E]
    [Algebra B L] [IsFractionRing B L] [Algebra L E] [Algebra B E]
    [IsScalarTower B L E] [Module.Finite L E] [Algebra.IsSeparable L E]
    {Y T : Scheme.{u}} (e : Y ⟶ Spec (.of B)) [QuasiCompact e] [QuasiSeparated e]
    [HasExt.{eX} (AbelianSheaf.{u, u + 1} Y)]
    (a : T ⟶ Y) (b : T ⟶ Spec (.of E))
    (H : IsPullback a b e (Spec.algebraMap B E))
    (M : AbelianSheaf.{u, u + 1} Y) (q : ℕ) (c : Sheaf.H.{eX} M q)
    (hc : cohomologyPullback.{u, eX, u + 2} a M q c = 0) :
    NormalPrincipalOpenClassZero B E e M q c := by
  obtain ⟨hfin, hnoeth, hnormal, hfrac, hf⟩ :=
    SeparableBaseSquare.normal_finite_model B L E
  let : IsFractionRing (integralClosure B E) E := hfrac
  exact ⟨hfin, hnoeth, hnormal, hfrac, hf,
    spread_on_fraction_model B (integralClosure B E) E e a b H M q c hc⟩

end AlgebraicGeometry.Scheme.EtaleCohomology.TwoFieldEffacement
