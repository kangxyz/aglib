/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.EtaleCohomology.Fields.SeparableExtension.FiniteConstantsOne.GenericMap
public import Aglib.RingTheory.Henselian.HenselizationResidue
public import Mathlib.RingTheory.Localization.AtPrime.Basic
public import Mathlib.RingTheory.Jacobson.Ring
public import Mathlib.FieldTheory.PurelyInseparable.Basic

/-! # Actual generic and closed maps of a finite-type coefficient specialization -/

@[expose] public noncomputable section

namespace Henselization

universe u v

/-- The actual henselization of a coefficient algebra localized at a maximal ideal. -/
abbrev AtMaximal (B : Type u) [CommRing B] (m : Ideal B) [m.IsMaximal] :=
  Henselization (Localization.AtPrime m)

namespace AtMaximal

variable (B : Type u) [CommRing B] (m : Ideal B) [m.IsMaximal]

instance algebra : Algebra B (AtMaximal B m) :=
  Algebra.compHom (AtMaximal B m) (algebraMap B (Localization.AtPrime m))

instance isScalarTower : IsScalarTower B (Localization.AtPrime m) (AtMaximal B m) :=
  IsScalarTower.of_algebraMap_eq' rfl

/-- The generic extension is an actual map compatible with the original coefficient algebra.
No residue-field map into the target field and no localness premise is used. -/
theorem nonempty_algHom [IsDomain B]
    (K : Type v) [Field K] [IsSepClosed K] [Algebra B K]
    (hinj : Function.Injective (algebraMap B K)) :
    Nonempty (AtMaximal B m →ₐ[B] K) := by
  let D := Localization.AtPrime m
  have hden : ∀ s : m.primeCompl, IsUnit ((Algebra.ofId B K) s) := by
    intro s
    apply isUnit_iff_ne_zero.mpr
    intro hs
    have hz : (s : B) = 0 := hinj (by simpa only [Algebra.ofId_apply, map_zero] using hs)
    exact s.property (hz.symm ▸ m.zero_mem)
  let φ : D →ₐ[B] K := IsLocalization.liftAlgHom hden
  let : Algebra D K := φ.toRingHom.toAlgebra
  let : IsScalarTower B D K := IsScalarTower.of_algebraMap_eq fun b => (φ.commutes b).symm
  have hD : Function.Injective (algebraMap D K) := by
    change Function.Injective (IsLocalization.lift hden : D →+* K)
    apply (IsLocalization.lift_injective_iff hden).mpr
    intro x y
    exact (FaithfulSMul.algebraMap_injective B D).eq_iff.trans hinj.eq_iff.symm
  obtain ⟨γ⟩ := Henselization.nonempty_algHom_of_injective D K hD
  exact ⟨γ.restrictScalars B⟩

section GroundField

variable (k : Type u) [Field k] [Algebra k B]

/-- The original ground-field algebra on the actual local henselization. -/
abbrev baseAlgebra : Algebra k (AtMaximal B m) :=
  Algebra.compHom (AtMaximal B m) (algebraMap k B)

attribute [local instance] baseAlgebra

theorem baseScalarTower : IsScalarTower k B (AtMaximal B m) :=
  IsScalarTower.of_algebraMap_eq' rfl

attribute [local instance] baseScalarTower

/-- The closed field is the actual finite residue extension, with the original `k`-map. -/
def quotientResidueAlgEquiv : (B ⧸ m) ≃ₐ[k] IsLocalRing.ResidueField (AtMaximal B m) where
  __ := (IsLocalization.AtPrime.equivQuotMaximalIdeal m (Localization.AtPrime m)).trans
    (Henselization.residueEquiv (Localization.AtPrime m)).symm
  commutes' a := by
    change (Henselization.residueEquiv (Localization.AtPrime m)).symm
        (IsLocalRing.residue (Localization.AtPrime m)
          (algebraMap B (Localization.AtPrime m) (algebraMap k B a))) =
      IsLocalRing.residue (AtMaximal B m)
        (algebraMap (Localization.AtPrime m) (AtMaximal B m)
          (algebraMap B (Localization.AtPrime m) (algebraMap k B a)))
    exact Henselization.residueEquiv_symm_residue (Localization.AtPrime m) _

/-- Zariski's lemma supplies actual finite-dimensional closed residue, without rationality. -/
theorem residue_finite [Algebra.FiniteType k B] :
    Module.Finite k (IsLocalRing.ResidueField (AtMaximal B m)) := by
  let : Field (B ⧸ m) := Ideal.Quotient.field m
  let : Module.Finite k (B ⧸ m) := finite_of_finite_type_of_isJacobsonRing k (B ⧸ m)
  exact Module.Finite.of_surjective (quotientResidueAlgEquiv B m k).toLinearMap
    (quotientResidueAlgEquiv B m k).surjective

/-- A separably closed ground field makes the closed extension purely inseparable. -/
theorem residue_isPurelyInseparable [Algebra.FiniteType k B] [IsSepClosed k] :
    IsPurelyInseparable k (IsLocalRing.ResidueField (AtMaximal B m)) := by
  let := residue_finite B m k
  infer_instance

/-- The actual closed residue field is separably closed, and may differ from `k`. -/
theorem residue_isSepClosed [Algebra.FiniteType k B] [IsSepClosed k] :
    IsSepClosed (IsLocalRing.ResidueField (AtMaximal B m)) := by
  let := residue_finite B m k
  exact Algebra.IsAlgebraic.isSepClosed (F := k)
    (E := IsLocalRing.ResidueField (AtMaximal B m))

end GroundField
end AtMaximal
end Henselization
