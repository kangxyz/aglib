/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.RingTheory.Kummer.UniformizerRecognition
public import Aglib.RingTheory.DiscreteValuationRing.UniformizerRamification
public import Aglib.RingTheory.Henselian.UnitRoots
public import Aglib.RingTheory.Henselian.FiniteAlgebraHenselian
public import Aglib.RingTheory.HenselianUniformizerNormalization

/-!
# Actual uniformizer-root normal form over a strictly Henselian DVR

For a finite torsion-free extension of DVRs, a surjective actual residue map
and an invertible native ramification index give the root normal form on the
same extension ring. The source is Henselian with separably closed residue
field. Henselianity of the target, the uniformizer root, and the root-algebra
isomorphism are constructed, not assumed. No completeness or field-degree
premise is used.
-/

@[expose] public noncomputable section

open IsLocalRing IsDiscreteValuationRing

namespace Algebra.Kummer

universe u v

/-- The native ramification index is positive and the same finite DVR extension
is the literal root algebra of the prescribed original uniformizer. -/
theorem exists_uniformizerRootEquiv_of_strictHenselian
    (R : Type u) (S : Type v)
    [CommRing R] [IsDomain R] [IsDiscreteValuationRing R] [HenselianLocalRing R]
    [IsSepClosed (ResidueField R)]
    [CommRing S] [IsDomain S] [IsDiscreteValuationRing S]
    [Algebra R S] [Module.Finite R S] [Module.IsTorsionFree R S]
    (π : R) (hπ : Irreducible π)
    (hκ : Function.Surjective (algebraMap (ResidueField R) (ResidueField S)))
    (heunit : IsUnit ((IsLocalRing.maximalIdeal S).ramificationIdx R : R)) :
    let e := (IsLocalRing.maximalIdeal S).ramificationIdx R
    0 < e ∧ ∃ E : RootAlgebra e π ≃ₐ[R] S,
      Irreducible (E (AdjoinRoot.root (rootPolynomial e π))) ∧
      E (AdjoinRoot.root (rootPolynomial e π)) ^ e = algebraMap R S π ∧
      Module.finrank R S = e := by
  let : HenselianLocalRing S := HenselianLocalRing.of_finite_local_algebra R S
  obtain ⟨τ, hτ⟩ := exists_irreducible S
  have hπ0 : algebraMap R S π ≠ 0 :=
    (map_ne_zero_iff _ (FaithfulSMul.algebraMap_injective R S)).mpr hπ.ne_zero
  obtain ⟨e, u, hfactor⟩ := eq_unit_mul_pow_irreducible hπ0 hτ
  have hindex := ramificationIdx_eq_uniformizerExponent R S hπ hτ u e hfactor
  have hepos : 0 < e := by
    apply Nat.pos_of_ne_zero
    intro hezero
    have hu : IsUnit (algebraMap R S π) := by simp [hfactor, hezero]
    exact hπ.not_isUnit (isUnit_of_map_unit (algebraMap R S) π hu)
  have heR : IsUnit (e : R) := hindex ▸ heunit
  have heS : IsUnit (e : S) := by
    simpa only [map_natCast] using heR.map (algebraMap R S)
  have hres : Function.Surjective (ResidueField.map (algebraMap R S)) := hκ
  obtain ⟨a, v, _, hτ', hadjust⟩ := exists_principal_adjusted_uniformizer
    (algebraMap R S) hres hτ u e hepos heS hfactor
  obtain ⟨b, hb⟩ := HenselianLocalRing.exists_unit_pow_eq_of_isSepClosed_residue
    e hepos heR a
  let t : S := algebraMap R S (b : R) * ((v : S) * τ)
  have ht : Irreducible t :=
    (irreducible_isUnit_mul (b.isUnit.map (algebraMap R S))).mpr hτ'
  have hbval : (b : R) ^ e = (a : R) := congrArg Units.val hb
  have hpow : t ^ e = algebraMap R S π := by
    dsimp only [t]
    rw [mul_pow, ← map_pow, hbval]
    exact hadjust.symm
  let E := uniformizerRootEquiv R S π hπ e hepos t ht hpow hκ
  have hE : E (AdjoinRoot.root (rootPolynomial e π)) = t :=
    uniformizerRootEquiv_root R S π hπ e hepos t ht hpow hκ
  change 0 < (IsLocalRing.maximalIdeal S).ramificationIdx R ∧ _
  rw [hindex]
  refine ⟨hepos, E, ?_, ?_, ?_⟩
  · rw [hE]
    exact ht
  · rw [hE]
    exact hpow
  · exact finrank_eq_of_uniformizer_root R S π hπ e hepos t ht hpow hκ

end Algebra.Kummer
