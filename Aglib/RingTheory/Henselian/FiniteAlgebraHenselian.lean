/-
Copyright (c) 2026 kangxyz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.RingTheory.Henselian.FiniteAlgebraLocalFactor
public import Aglib.RingTheory.LocalRing.FiniteFlatResidue
public import Mathlib.RingTheory.Etale.StandardEtale
public import Mathlib.RingTheory.Flat.Localization

/-!
# Finite local algebras over Henselian local rings

The monic simple-root definition is proved by selecting the actual root point
in an AdjoinRoot algebra. Its localization is finite by the selected-factor
theorem, flat by monicity, and formally unramified via a surjection from an
actual standard etale algebra. No global etale claim for an arbitrary prime
localization is needed.
-/

@[expose] public noncomputable section

open IsLocalRing Polynomial

universe u v

namespace IsLocalRing

/-- An actual residue-valued point of a local algebra forces its native residue
extension to be unchanged. -/
lemma bijective_residue_algebraMap_of_point
    {B D : Type*} [CommRing B] [CommRing D] [IsLocalRing B] [IsLocalRing D]
    [Algebra B D] [IsLocalHom (algebraMap B D)]
    (pt : D →ₐ[B] ResidueField B) :
    Function.Bijective (algebraMap (ResidueField B) (ResidueField D)) := by
  have hpt : Function.Surjective pt := by
    intro z
    obtain ⟨b, hb⟩ := residue_surjective (R := B) z
    exact ⟨algebraMap B D b, (pt.commutes b).trans hb⟩
  have hker : RingHom.ker pt.toRingHom = maximalIdeal D :=
    ker_eq_maximalIdeal pt.toRingHom hpt
  refine ⟨(algebraMap (ResidueField B) (ResidueField D)).injective, ?_⟩
  intro z
  obtain ⟨d, rfl⟩ := residue_surjective (R := D) z
  obtain ⟨b, hb⟩ := residue_surjective (R := B) (pt d)
  refine ⟨residue B b, ?_⟩
  change algebraMap (ResidueField B) (ResidueField D)
    (algebraMap B (ResidueField B) b) = algebraMap D (ResidueField D) d
  rw [← IsScalarTower.algebraMap_apply B (ResidueField B) (ResidueField D),
    IsScalarTower.algebraMap_apply B D (ResidueField D)]
  apply sub_eq_zero.mp
  rw [← map_sub]
  apply (residue_eq_zero_iff _).mpr
  rw [← hker]
  change pt (algebraMap B D b - d) = 0
  rw [map_sub, pt.commutes]
  exact sub_eq_zero.mpr hb

end IsLocalRing

namespace HenselianLocalRing

/-- A finite local algebra over a Henselian local ring is Henselian, with the
native monic simple-root lifting property. -/
theorem of_finite_local_algebra
    (R : Type u) [CommRing R] [HenselianLocalRing R]
    (B : Type v) [CommRing B] [IsLocalRing B] [Algebra R B] [Module.Finite R B] :
    HenselianLocalRing B := by
  classical
  constructor
  intro f hf a₀ hfa hdf
  let C := AdjoinRoot f
  let : Module.Finite B C := hf.finite_adjoinRoot
  let : Module.Free B C := hf.free_adjoinRoot
  let : Module.Finite R C := Module.Finite.trans B C
  have hroot : f.eval₂ (algebraMap B (ResidueField B)) (residue B a₀) = 0 := by
    change f.eval₂ (residue B) ((residue B) a₀) = 0
    rw [Polynomial.eval₂_at_apply]
    exact (residue_eq_zero_iff _).mpr hfa
  let π : C →ₐ[B] ResidueField B :=
    AdjoinRoot.liftAlgHom f (Algebra.ofId B (ResidueField B)) (residue B a₀) hroot
  have hπroot : π (AdjoinRoot.root f) = residue B a₀ :=
    AdjoinRoot.liftAlgHom_root f _ _ _
  have hπ : Function.Surjective π := by
    intro z
    obtain ⟨b, hb⟩ := residue_surjective (R := B) z
    exact ⟨algebraMap B C b, (π.commutes b).trans hb⟩
  let q := RingHom.ker π.toRingHom
  let : q.IsMaximal := RingHom.ker_isMaximal_of_surjective π hπ
  let D := Localization.AtPrime q
  let : Module.Finite R D := finite_localizationAtPrime R C q
  let : Module.Finite B D := Module.Finite.of_restrictScalars_finite R B D
  let : Module.Flat B D := Module.Flat.trans B C D
  have hπunit (s : q.primeCompl) : IsUnit (π s) :=
    isUnit_iff_ne_zero.mpr s.property
  let pt : D →ₐ[B] ResidueField B := IsLocalization.liftAlgHom hπunit
  have hpt (c : C) : pt (algebraMap C D c) = π c :=
    IsLocalization.lift_eq hπunit c
  let : IsLocalHom (algebraMap B D) := ⟨fun b hb => by
    apply (residue_ne_zero_iff_isUnit b).mp
    have hu : IsUnit (residue B b) := by
      have hu := hb.map pt.toRingHom
      change IsUnit (pt (algebraMap B D b)) at hu
      rw [pt.commutes] at hu
      exact hu
    exact isUnit_iff_ne_zero.mp hu⟩
  let x : D := algebraMap C D (AdjoinRoot.root f)
  have hx : aeval x f = 0 :=
    AdjoinRoot.aeval_algHom_eq_zero f (IsScalarTower.toAlgHom B C D)
  have hdx : IsUnit (aeval x f.derivative) := by
    let d : C := aeval (AdjoinRoot.root f) f.derivative
    have hπd : π d = residue B (f.derivative.eval a₀) := by
      change π (aeval (AdjoinRoot.root f) f.derivative) = _
      rw [← Polynomial.aeval_algHom_apply, hπroot]
      change f.derivative.eval₂ (residue B) ((residue B) a₀) = _
      exact Polynomial.eval₂_at_apply _ _
    have hd : d ∉ q := by
      change π d ≠ 0
      rw [hπd]
      exact isUnit_iff_ne_zero.mp (hdf.map (residue B))
    have hu := IsLocalization.map_units D (⟨d, hd⟩ : q.primeCompl)
    change IsUnit ((IsScalarTower.toAlgHom B C D)
      (aeval (AdjoinRoot.root f) f.derivative)) at hu
    rw [← Polynomial.aeval_algHom_apply] at hu
    exact hu
  obtain ⟨e, he, heq, hi⟩ := exists_idempotent_isolating_maximal R C q
  let E := IsLocalization.quotientEquivAtPrimeOfIsolatingIdempotent q e he heq hi
  have hCD : Function.Surjective (algebraMap C D) := by
    intro d
    obtain ⟨c, hc⟩ := Ideal.Quotient.mk_surjective (E.symm d)
    refine ⟨c, ?_⟩
    calc
      algebraMap C D c = E (Ideal.Quotient.mk _ c) := (E.commutes c).symm
      _ = d := by rw [hc]; exact E.apply_symm_apply d
  let P : StandardEtalePair B :=
    { f := f, monic_f := hf, g := f.derivative, cond := ⟨1, 0, 1, by simp⟩ }
  let ψ : P.Ring →ₐ[B] D := P.lift x ⟨hx, hdx⟩
  let η : C →ₐ[B] P.Ring :=
    AdjoinRoot.liftAlgHom f (Algebra.ofId B P.Ring) P.X P.hasMap_X.1
  have hcomp : ψ.comp η = IsScalarTower.toAlgHom B C D := by
    apply AdjoinRoot.algHom_ext
    change ψ (η (AdjoinRoot.root f)) = algebraMap C D (AdjoinRoot.root f)
    rw [show η (AdjoinRoot.root f) = P.X from AdjoinRoot.liftAlgHom_root f _ _ _]
    exact P.lift_X x ⟨hx, hdx⟩
  have hψ : Function.Surjective ψ := by
    intro d
    obtain ⟨c, hc⟩ := hCD d
    exact ⟨η c, (AlgHom.congr_fun hcomp c).trans hc⟩
  let : Algebra.FormallyUnramified B D := Algebra.FormallyUnramified.of_surjective ψ hψ
  have hBD := IsLocalRing.bijective_algebraMap_of_finite_flat_unramified_residue
    (R := B) (S := D) (IsLocalRing.bijective_residue_algebraMap_of_point pt)
  obtain ⟨b, hb⟩ := hBD.surjective x
  refine ⟨b, ?_, ?_⟩
  · change f.eval b = 0
    apply hBD.injective
    rw [map_zero, ← Polynomial.eval₂_at_apply, hb]
    exact hx
  · apply (residue_eq_zero_iff _).mp
    rw [map_sub, sub_eq_zero]
    calc
      residue B b = pt (algebraMap B D b) := (pt.commutes b).symm
      _ = pt x := congrArg pt hb
      _ = π (AdjoinRoot.root f) := hpt _
      _ = residue B a₀ := hπroot

end HenselianLocalRing
