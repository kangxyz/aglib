/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.RingTheory.Kummer.StrictHenselianRootCancellation
public import Aglib.RingTheory.IntegralClosure.Inertia.StrictHenselianNormalForm

/-! # Bounded Galois cancellation without a supplied chart or embedding

The actual strictly Henselian DVR normal-form theorem constructs the root
chart. The original generic-fibre equivalence then gives a single embedding of
the original field, and evaluation proves etaleness of the literal normalized
generic tensor. No splitting, chart, embedding, or normalized etaleness is an
input. This is the DVR component consumer, not ambient purity.
-/

@[expose] public noncomputable section

open scoped TensorProduct

namespace Algebra.Kummer

universe r k l z

variable (R : Type r) [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]
  [HenselianLocalRing R] [IsSepClosed (IsLocalRing.ResidueField R)]
  (K : Type k) [Field K] [Algebra R K] [IsFractionRing R K]
  (L : Type l) [Field L] [Algebra K L] [Algebra R L] [IsScalarTower R K L]
  [FiniteDimensional K L] [IsGalois K L]
  (π : R) (hπ : Irreducible π) (N : ℕ) (hN : 0 < N)
  (hunit : IsUnit (N : R)) (hcard : Nat.card (L ≃ₐ[K] L) ∣ N)
  (F : Type z) [Field F] [Algebra R F]
  [Algebra (RootAlgebra N π) F] [IsScalarTower R (RootAlgebra N π) F]
  [IsFractionRing (RootAlgebra N π) F] [FaithfulSMul R F]

include hπ hunit hcard

omit [IsFractionRing (RootAlgebra N π) F] in
/-- The original bounded Galois field embeds in the root fraction field by a
constructed root chart and the inverse of its unchanged generic-fibre map. -/
def boundedRootFieldHom :
    letI : Algebra K F := (rootChartCoefficientHom (R := R) K F).toRingHom.toAlgebra
    L →ₐ[K] F := by
  letI : Algebra K F := (rootChartCoefficientHom (R := R) K F).toRingHom.toAlgebra
  have hex :=
    integralClosure.Inertia.FiniteEtale.exists_rootChart_of_strictHenselian_of_card_dvd_pow
    R K L N 1 hunit (by simpa only [pow_one] using hcard) π hπ
  let e := Classical.choose hex
  let E : RootAlgebra e π ≃ₐ[R] integralClosure R L :=
    Classical.choose (Classical.choose_spec hex)
  have he : e ∣ N ^ 1 := (Classical.choose_spec (Classical.choose_spec hex)).2.1
  exact (rootChartGenericFieldHom (N := N) K F E (show e ∣ N by simpa only [pow_one] using he)).comp
    (integralClosure.genericFiberEquiv R K L).symm.toAlgHom

include hN in
/-- The same normalization is etale. The field action is the canonical lift
of the original coefficient map to the specified fraction field. -/
theorem boundedRoot_normalTensor_etale :
    letI : Algebra K F := (rootChartCoefficientHom (R := R) K F).toRingHom.toAlgebra
    Algebra.Etale (RootAlgebra N π)
      (integralClosure (RootAlgebra N π) (F ⊗[K] L)) := by
  let : Algebra K F := (rootChartCoefficientHom (R := R) K F).toRingHom.toAlgebra
  exact uniformizerRoot_normalTensor_etale R π hπ N hN K L F
    (boundedRootFieldHom (R := R) (K := K) (L := L) (π := π)
      (hπ := hπ) (N := N) (hunit := hunit) (hcard := hcard) (F := F))

end Algebra.Kummer
