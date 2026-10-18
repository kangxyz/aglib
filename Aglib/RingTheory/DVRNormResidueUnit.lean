/-
Copyright (c) 2026 Motivic Cohomology contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.RingTheory.PolynomialFiberNorm
public import Mathlib.RingTheory.TensorProduct.Quotient
public import Mathlib.RingTheory.LocalRing.ResidueField.Basic
public import Mathlib.RingTheory.IntegralClosure.IntegralRestrict
public import Mathlib.RingTheory.DiscreteValuationRing.Basic

/-!
# Reduction of norms through the actual closed fiber

Determinant scalar extension identifies the reduction of the ring norm with
the norm of the literal quotient by the extended base maximal ideal. The
finite local algebra norm formula retains the actual closed-fiber length,
including nilpotents and inseparable residue extensions. Its residue field
is identified with the original extension residue field by the actual
quotient map, not by a supplied isomorphism. For actual DVRs a separate
ideal-and-length proof identifies this length with the stated uniformizer
exponent, giving the original integral-norm formula on residue units.
-/

@[expose] public noncomputable section

open IsLocalRing

namespace Algebra

variable (R S : Type*) [CommRing R] [CommRing S] [IsLocalRing R]
  [Algebra R S] [Module.Free R S] [Module.Finite R S]

/-- Determinant scalar extension at the closed point, using the literal
quotient–tensor equivalence and the original determinant norm. -/
theorem norm_closedFiber (b : S) :
    let _ : Algebra (ResidueField R) (S ⧸ (maximalIdeal R).map (algebraMap R S)) :=
      Ideal.Quotient.algebraQuotientOfLEComap Ideal.le_comap_map
    Algebra.norm (ResidueField R)
      (Ideal.Quotient.mk ((maximalIdeal R).map (algebraMap R S)) b) =
        residue R (Algebra.norm R b) := by
  let : Algebra (ResidueField R) (S ⧸ (maximalIdeal R).map (algebraMap R S)) :=
    Ideal.Quotient.algebraQuotientOfLEComap Ideal.le_comap_map
  let ε := Algebra.TensorProduct.quotIdealMapEquivQuotTensor S (maximalIdeal R)
  have h := Algebra.norm_eq_of_algEquiv ε
    (Ideal.Quotient.mk ((maximalIdeal R).map (algebraMap R S)) b)
  rw [Algebra.TensorProduct.quotIdealMapEquivQuotTensor_mk, Algebra.norm_one_tmul] at h
  exact h.symm

variable [IsLocalRing S] [IsLocalHom (algebraMap R S)]

/-- Norm reduction keeps the full length of the actual closed fiber. Neither
reducedness nor separability of the residue extension is assumed. -/
theorem residue_norm_eq_norm_residue_pow_length (b : S) :
    residue R (Algebra.norm R b) =
      Algebra.norm (ResidueField R) (residue S b) ^
        (Module.length (S ⧸ (maximalIdeal R).map (algebraMap R S))
          (S ⧸ (maximalIdeal R).map (algebraMap R S))).toNat := by
  let I := (maximalIdeal R).map (algebraMap R S)
  let A := S ⧸ I
  let : Algebra (ResidueField R) A :=
    Ideal.Quotient.algebraQuotientOfLEComap Ideal.le_comap_map
  let : IsScalarTower R (ResidueField R) A := IsScalarTower.of_algebraMap_eq fun _ => rfl
  have hI : I ≠ ⊤ := ne_of_lt (IsLocalRing.map_maximalIdeal_lt_top (algebraMap R S))
  let : Nontrivial A := Ideal.Quotient.nontrivial_iff.mpr hI
  let : IsLocalRing A := .of_surjective' (Ideal.Quotient.mk I) Ideal.Quotient.mk_surjective
  let : IsLocalHom (Ideal.Quotient.mk I) :=
    IsLocalHom.of_surjective (Ideal.Quotient.mk I) Ideal.Quotient.mk_surjective
  let : IsLocalHom (algebraMap R A) := by
    change IsLocalHom ((Ideal.Quotient.mk I).comp (algebraMap R S))
    infer_instance
  let : IsLocalHom (IsScalarTower.toAlgHom R S A) :=
    ⟨fun a ha => IsUnit.of_map (Ideal.Quotient.mk I) a ha⟩
  let : Module.Finite (ResidueField R) A := Module.Finite.of_restrictScalars_finite R _ _
  let φ : ResidueField S →ₐ[ResidueField R] ResidueField A :=
    ResidueField.mapAlgHom' (IsScalarTower.toAlgHom R S A)
  have hφ (s : S) : φ (residue S s) = residue A (Ideal.Quotient.mk I s) :=
    ResidueField.mapAlgHom'_residue (IsScalarTower.toAlgHom R S A) s
  have hsurj : Function.Surjective φ := by
    intro x
    obtain ⟨a, rfl⟩ := residue_surjective x
    obtain ⟨s, rfl⟩ := Ideal.Quotient.mk_surjective a
    exact ⟨residue S s, hφ s⟩
  let ε : ResidueField S ≃ₐ[ResidueField R] ResidueField A :=
    AlgEquiv.ofBijective φ ⟨φ.injective, hsurj⟩
  have hn : Algebra.norm (ResidueField R) (residue A (Ideal.Quotient.mk I b)) =
      Algebra.norm (ResidueField R) (residue S b) := by
    rw [← hφ]
    exact Algebra.norm_eq_of_algEquiv ε (residue S b)
  let δ : (A ⧸ maximalIdeal A) ≃ₐ[ResidueField R] ResidueField A :=
    { RingEquiv.refl (A ⧸ maximalIdeal A) with
      commutes' x := by
        obtain ⟨r, rfl⟩ := residue_surjective x
        rfl }
  calc
    _ = Algebra.norm (ResidueField R) (Ideal.Quotient.mk I b) :=
      (norm_closedFiber R S b).symm
    _ = Algebra.norm (ResidueField R) (residue A (Ideal.Quotient.mk I b)) ^
        (Module.length A A).toNat := by
      have h := Algebra.norm_eq_quotient_norm_pow_length (k := ResidueField R) (B := A)
        (Ideal.Quotient.mk I b)
      rw [← Algebra.norm_eq_of_algEquiv δ] at h
      exact h
    _ = _ := congrArg (fun x => x ^ (Module.length A A).toNat) hn

end Algebra

namespace IsDiscreteValuationRing

variable (R S : Type*) [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]
  [CommRing S] [IsDomain S] [IsDiscreteValuationRing S] [Algebra R S]

/-- The literal uniformizer equation identifies the extended maximal ideal.
This is an ideal identity, before any norm or length comparison. -/
theorem map_maximalIdeal_eq_pow_of_uniformizer
    {π : R} {ϖ : S} (hπ : Irreducible π) (hϖ : Irreducible ϖ)
    (u : Sˣ) (e : ℕ) (he : algebraMap R S π = (u : S) * ϖ ^ e) :
    (maximalIdeal R).map (algebraMap R S) = maximalIdeal S ^ e := by
  rw [hπ.maximalIdeal_eq, Ideal.map_span, Set.image_singleton, he,
    Ideal.span_singleton_mul_left_unit u.isUnit, hϖ.maximalIdeal_eq, Ideal.span_singleton_pow]

/-- The actual closed-fiber length equals the actual uniformizer exponent.
Restriction of scalars along the surjective quotient map is explicit. -/
theorem closedFiber_length_eq_ramification
    {π : R} {ϖ : S} (hπ : Irreducible π) (hϖ : Irreducible ϖ)
    (u : Sˣ) (e : ℕ) (he : algebraMap R S π = (u : S) * ϖ ^ e) :
    Module.length (S ⧸ (maximalIdeal R).map (algebraMap R S))
      (S ⧸ (maximalIdeal R).map (algebraMap R S)) = e := by
  rw [← Module.length_eq_of_surjective (S := S) Ideal.Quotient.mk_surjective,
    map_maximalIdeal_eq_pow_of_uniformizer R S hπ hϖ u e he]
  exact length_quotient_pow_maximalIdeal S e

end IsDiscreteValuationRing

namespace Algebra

variable (R S : Type*) [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]
  [CommRing S] [IsDomain S] [IsDiscreteValuationRing S] [Algebra R S]
  [Module.Finite R S] [Module.IsTorsionFree R S] [IsLocalHom (algebraMap R S)]

/-- Reduction of the actual integral norm is the ordinary residue-field norm
raised to the proved uniformizer exponent, in arbitrary characteristic. -/
theorem residue_intNorm_eq_norm_residue_pow
    {π : R} {ϖ : S} (hπ : Irreducible π) (hϖ : Irreducible ϖ)
    (u : Sˣ) (e : ℕ) (he : algebraMap R S π = (u : S) * ϖ ^ e) (b : S) :
    residue R (Algebra.intNorm R S b) =
      Algebra.norm (ResidueField R) (residue S b) ^ e := by
  rw [Algebra.intNorm_eq_norm, residue_norm_eq_norm_residue_pow_length,
    IsDiscreteValuationRing.closedFiber_length_eq_ramification R S hπ hϖ u e he,
    ENat.toNat_natCast]

/-- The unit-valued form keeps both original residue maps and the actual
integral norm. The residue extension is not assumed separable. -/
theorem residueUnits_intNorm_eq_norm_pow
    {π : R} {ϖ : S} (hπ : Irreducible π) (hϖ : Irreducible ϖ)
    (u : Sˣ) (e : ℕ) (he : algebraMap R S π = (u : S) * ϖ ^ e) (b : Sˣ) :
    Units.map (residue R).toMonoidHom (Units.map (Algebra.intNorm R S) b) =
      Units.map (Algebra.norm (ResidueField R))
        (Units.map (residue S).toMonoidHom b) ^ e := by
  apply Units.ext
  exact residue_intNorm_eq_norm_residue_pow R S hπ hϖ u e he (b : S)

end Algebra
