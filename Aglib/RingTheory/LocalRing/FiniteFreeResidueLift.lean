/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.RingTheory.LocalRing.EtaleLift
public import Mathlib.RingTheory.Ideal.GoingUp
public import Mathlib.RingTheory.TensorProduct.Quotient
public import Mathlib.FieldTheory.IntermediateField.Adjoin.Algebra
public import Mathlib.LinearAlgebra.Finsupp.VectorSpace

/-! # Finite free local lifts of a specified simple residue extension

A supplied power basis, without separability, lifts through a monic polynomial.
The original residue tensor product is the given field. Integrality then shows
that the actual lifted algebra is local, and that its maximal ideal is exactly
the extension of the original maximal ideal. An arbitrary finite extension
still requires a finite generating tower; it is not assumed to be simple.
-/

@[expose] public noncomputable section

open Polynomial
open scoped TensorProduct IntermediateField

universe u v w

namespace IsLocalRing

variable (R : Type u) [CommRing R] [IsLocalRing R]
  (L : Type v) [Field L] [Algebra (ResidueField R) L]

/-- A specified power basis lifts by a monic polynomial even when its minimal
polynomial is inseparable. The comparison is the original residue tensor. -/
theorem exists_monic_residue_lift_of_powerBasis (pb : PowerBasis (ResidueField R) L) :
    ∃ f : R[X], f.Monic ∧
      Nonempty (ResidueField R ⊗[R] AdjoinRoot f ≃ₐ[ResidueField R] L) := by
  let q := minpoly (ResidueField R) pb.gen
  have hq : q.Monic := minpoly.monic pb.isIntegral_gen
  obtain ⟨f, hfq, _, hfm⟩ := lifts_and_natDegree_eq_and_monic
    (mem_lifts_of_surjective (residue_surjective (R := R)) q) hq
  refine ⟨f, hfm, ⟨?_⟩⟩
  exact (AdjoinRoot.baseChangeEquiv f q hfq).trans
    (AdjoinRoot.equiv' q pb (by simp [q, AdjoinRoot.aeval_eq]) (minpoly.aeval _ _))

variable (S : Type u) [CommRing S] [Algebra R S]

/-- The extended maximal ideal is maximal when the actual residue tensor
product is a field. This does not assume the lifted ring is already local. -/
theorem map_maximalIdeal_isMaximal_of_residueTensorEquiv
    (e : ResidueField R ⊗[R] S ≃ₐ[ResidueField R] L) :
    ((maximalIdeal R).map (algebraMap R S)).IsMaximal := by
  let eQ : S ⧸ (maximalIdeal R).map (algebraMap R S) ≃+* L :=
    (Algebra.TensorProduct.quotIdealMapEquivTensorQuot S (maximalIdeal R)).toRingEquiv.trans
      ((Algebra.TensorProduct.comm R S (ResidueField R)).toRingEquiv.trans e.toRingEquiv)
  rw [Ideal.Quotient.maximal_ideal_iff_isField_quotient]
  exact eQ.toMulEquiv.isField (Field.toIsField L)

/-- The same finite algebra is local: all its maximal ideals contract to the
coefficient maximal ideal and therefore equal its already maximal extension. -/
theorem isLocalRing_of_residueTensorEquiv [Module.Finite R S]
    (e : ResidueField R ⊗[R] S ≃ₐ[ResidueField R] L) : IsLocalRing S := by
  have hm := map_maximalIdeal_isMaximal_of_residueTensorEquiv R L S e
  apply IsLocalRing.of_unique_max_ideal
  refine ⟨(maximalIdeal R).map (algebraMap R S), hm, ?_⟩
  intro N hN
  have hi : (algebraMap R S).IsIntegral := algebraMap_isIntegral_iff.mpr inferInstance
  have hc : N.comap (algebraMap R S) = maximalIdeal R :=
    eq_maximalIdeal
      (Ideal.isMaximal_comap_of_isIntegral_of_isMaximal (algebraMap R S) hi N)
  have hle : (maximalIdeal R).map (algebraMap R S) ≤ N := by
    rw [Ideal.map_le_iff_le_comap, hc]
  exact (hm.eq_of_le hN.ne_top hle).symm

/-- Once the actual local structure is installed, its maximal ideal is
literally the original extended ideal, rather than a separately chosen prime. -/
theorem map_maximalIdeal_eq_of_residueTensorEquiv [IsLocalRing S]
    (e : ResidueField R ⊗[R] S ≃ₐ[ResidueField R] L) :
    (maximalIdeal R).map (algebraMap R S) = maximalIdeal S :=
  eq_maximalIdeal (map_maximalIdeal_isMaximal_of_residueTensorEquiv R L S e)

/-- A specified simple finite residue extension lifts to the actual monic root
algebra, finite free and local over the original coefficient ring. No etaleness,
separability, Henselianity, or normality is assumed or asserted. -/
theorem exists_finite_free_local_residue_lift_of_powerBasis
    (pb : PowerBasis (ResidueField R) L) :
    ∃ (S : Type u) (_ : CommRing S) (_ : Algebra R S) (_ : IsLocalRing S),
      Module.Finite R S ∧ Module.Free R S ∧
        (maximalIdeal R).map (algebraMap R S) = maximalIdeal S ∧
          Nonempty (ResidueField R ⊗[R] S ≃ₐ[ResidueField R] L) := by
  obtain ⟨f, hf, ⟨e⟩⟩ := exists_monic_residue_lift_of_powerBasis R L pb
  let : Module.Finite R (AdjoinRoot f) := hf.finite_adjoinRoot
  let : Module.Free R (AdjoinRoot f) := hf.free_adjoinRoot
  let : IsLocalRing (AdjoinRoot f) := isLocalRing_of_residueTensorEquiv R L (AdjoinRoot f) e
  exact ⟨AdjoinRoot f, inferInstance, inferInstance, inferInstance,
    inferInstance, inferInstance, map_maximalIdeal_eq_of_residueTensorEquiv R L (AdjoinRoot f) e,
    ⟨e⟩⟩

end IsLocalRing

namespace IsLocalRing

variable (R : Type u) [CommRing R] [IsLocalRing R]

/-- One genuine generating-tower step. The new ring is the monic root algebra
of the preceding ring. Its original residue tensor is compared directly using
the native root-algebra base-change equivalence and the existing coefficient
comparison; no intermediate residue-field model is selected. -/
theorem exists_finite_free_residue_tower_step
    (S : Type u) [CommRing S] [Algebra R S]
    [Module.Finite R S] [Module.Free R S]
    (K : Type v) [Field K] [Algebra (ResidueField R) K]
    (L : Type w) [Field L] [Algebra K L] [Algebra (ResidueField R) L]
    [IsScalarTower (ResidueField R) K L]
    (e : ResidueField R ⊗[R] S ≃ₐ[ResidueField R] K) (pb : PowerBasis K L) :
    ∃ (T : Type u) (_ : CommRing T) (_ : Algebra R T),
      Module.Finite R T ∧ Module.Free R T ∧
        Nonempty (ResidueField R ⊗[R] T ≃ₐ[ResidueField R] L) := by
  let φ : S →+* K := e.toRingHom.comp
    (Algebra.TensorProduct.includeRight : S →ₐ[R] ResidueField R ⊗[R] S).toRingHom
  have hφ : Function.Surjective φ := e.surjective.comp
    (Algebra.TensorProduct.includeRight_surjective S (residue_surjective (R := R)))
  let q := minpoly K pb.gen
  have hq : q.Monic := minpoly.monic pb.isIntegral_gen
  obtain ⟨f, hfq, _, hf⟩ := lifts_and_natDegree_eq_and_monic
    (mem_lifts_of_surjective hφ q) hq
  let p := f.map
    (Algebra.TensorProduct.includeRight : S →ₐ[R] ResidueField R ⊗[R] S).toRingHom
  have hpq : p.map e.toRingHom = q := by
    rw [Polynomial.map_map]
    exact hfq
  let e₁ := AdjoinRoot.tensorAlgEquiv (R := R) (T := ResidueField R) f p rfl
  let e₂ := AdjoinRoot.mapAlgEquiv e p q (Associated.of_eq hpq)
  let e₃ := (AdjoinRoot.equiv' q pb
    (by simp [q, AdjoinRoot.aeval_eq]) (minpoly.aeval K pb.gen)).restrictScalars
      (ResidueField R)
  let : Module.Finite S (AdjoinRoot f) := hf.finite_adjoinRoot
  let : Module.Free S (AdjoinRoot f) := hf.free_adjoinRoot
  let : Module.Finite R (AdjoinRoot f) := Module.Finite.trans S (AdjoinRoot f)
  let : Module.Free R (AdjoinRoot f) := Module.Free.trans (R := R) (S := S)
  exact ⟨AdjoinRoot f, inferInstance, inferInstance, inferInstance, inferInstance,
    ⟨e₁.trans (e₂.trans e₃)⟩⟩

/-- Every finite residue extension is the original residue tensor of a finite
free algebra. The proof uses a finite generating tower, not a primitive element
for the entire extension; inseparable and nonsimple extensions are included. -/
theorem exists_finite_free_residue_lift
    (L : Type v) [Field L] [Algebra (ResidueField R) L]
    [FiniteDimensional (ResidueField R) L] :
    ∃ (S : Type u) (_ : CommRing S) (_ : Algebra R S),
      Module.Finite R S ∧ Module.Free R S ∧
        Nonempty (ResidueField R ⊗[R] S ≃ₐ[ResidueField R] L) := by
  let P (K : IntermediateField (ResidueField R) L) : Prop :=
    ∃ (S : Type u) (_ : CommRing S) (_ : Algebra R S),
      Module.Finite R S ∧ Module.Free R S ∧
        Nonempty (ResidueField R ⊗[R] S ≃ₐ[ResidueField R] K)
  have hbase : P ⊥ := by
    exact ⟨R, inferInstance, inferInstance, inferInstance, inferInstance,
      ⟨(Algebra.TensorProduct.rid R (ResidueField R) (ResidueField R)).trans
        (IntermediateField.botEquiv (ResidueField R) L).symm⟩⟩
  have hstep (K : IntermediateField (ResidueField R) L) (x : L) (hK : P K) :
      P (K⟮x⟯.restrictScalars (ResidueField R)) := by
    obtain ⟨S, hS, hRS, hfin, hfree, ⟨e⟩⟩ := hK
    let : CommRing S := hS
    let : Algebra R S := hRS
    let : Module.Finite R S := hfin
    let : Module.Free R S := hfree
    have hx : IsIntegral K x := Algebra.IsIntegral.isIntegral x
    exact exists_finite_free_residue_tower_step R S K K⟮x⟯ e
      (IntermediateField.adjoin.powerBasis hx)
  obtain ⟨S, hS, hRS, hfin, hfree, ⟨e⟩⟩ :=
    IntermediateField.induction_on_adjoin P hbase hstep ⊤
  exact ⟨S, hS, hRS, hfin, hfree, ⟨e.trans IntermediateField.topEquiv⟩⟩

/-- The complete finite-free local residue lift. The maximal ideal is exactly
mR extended to the same lifted ring; the residue comparison is still from the
original tensor product, and the structural map is local. -/
theorem exists_finite_free_local_residue_lift
    (L : Type v) [Field L] [Algebra (ResidueField R) L]
    [FiniteDimensional (ResidueField R) L] :
    ∃ (S : Type u) (_ : CommRing S) (_ : Algebra R S) (_ : IsLocalRing S),
      Module.Finite R S ∧ Module.Free R S ∧ IsLocalHom (algebraMap R S) ∧
        (maximalIdeal R).map (algebraMap R S) = maximalIdeal S ∧
          Nonempty (ResidueField R ⊗[R] S ≃ₐ[ResidueField R] L) := by
  obtain ⟨S, hS, hRS, hfin, hfree, ⟨e⟩⟩ := exists_finite_free_residue_lift R L
  let : CommRing S := hS
  let : Algebra R S := hRS
  let : Module.Finite R S := hfin
  let : Module.Free R S := hfree
  let : IsLocalRing S := isLocalRing_of_residueTensorEquiv R L S e
  have hm := map_maximalIdeal_eq_of_residueTensorEquiv R L S e
  have hl : IsLocalHom (algebraMap R S) :=
    ((local_hom_TFAE (algebraMap R S)).out 3 1 rfl rfl).mp hm.le
  exact ⟨S, inferInstance, inferInstance, inferInstance, hfin, hfree, hl, hm, ⟨e⟩⟩

end IsLocalRing
