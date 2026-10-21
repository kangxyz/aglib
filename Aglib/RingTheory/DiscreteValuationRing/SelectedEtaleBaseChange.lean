/-
Copyright (c) 2026 kangxyz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.RingTheory.DiscreteValuationRing.EssentiallyEtale
public import Aglib.RingTheory.Localization.ResiduePoint
public import Mathlib.RingTheory.Etale.Basic
public import Mathlib.RingTheory.Smooth.Flat
public import Mathlib.RingTheory.TensorProduct.Maps

/-! # The selected local étale base-change DVR

The selected target is the native localization of the actual tensor product at
the kernel of its chosen residue point. Its residue field remains the original
one, and every original target uniformizer is preserved.
-/

@[expose] public noncomputable section

open IsLocalRing
open scoped TensorProduct

namespace Algebra.SelectedEtaleBaseChange

variable (R A S : Type*) [CommRing R] [CommRing A] [Algebra R A]
  [CommRing S] [IsDomain S] [IsDiscreteValuationRing S] [Algebra R S]
  (ψ : A →ₐ[R] ResidueField S)

/-- The literal tensor residue point determined by the selected embedding. -/
def tensorPoint : S ⊗[R] A →ₐ[S] ResidueField S :=
  Algebra.TensorProduct.lift (Algebra.ofId S (ResidueField S)) ψ
    (fun s a => Algebra.commutes s (ψ a))

@[simp] theorem tensorPoint_tmul (s : S) (a : A) :
    tensorPoint R A S ψ (s ⊗ₜ[R] a) = residue S s * ψ a := rfl

/-- The tensor point is surjective by the original target residue map. -/
theorem tensorPoint_surjective : Function.Surjective (tensorPoint R A S ψ) := by
  intro x
  obtain ⟨s, rfl⟩ := residue_surjective x
  refine ⟨s ⊗ₜ[R] (1 : A), ?_⟩
  rw [tensorPoint_tmul, map_one, mul_one]

/-- The actual localization at the selected tensor residue prime. -/
abbrev Ring := Localization.ResiduePoint.Ring (tensorPoint R A S ψ).toRingHom

/-- The actual point on the selected local ring. -/
def point : Ring R A S ψ →ₐ[S] ResidueField S where
  toRingHom := Localization.ResiduePoint.point (tensorPoint R A S ψ).toRingHom
  commutes' s := by
    change Localization.ResiduePoint.point (tensorPoint R A S ψ).toRingHom
      (algebraMap S (Ring R A S ψ) s) = _
    rw [IsScalarTower.algebraMap_apply S (S ⊗[R] A) (Ring R A S ψ),
      Localization.ResiduePoint.point_algebraMap]
    exact (tensorPoint R A S ψ).commutes s

instance point_isLocalHom : IsLocalHom (point R A S ψ).toRingHom :=
  Localization.ResiduePoint.point_isLocalHom _

/-- The original target DVR maps locally into the selected localization. -/
instance algebraMap_isLocalHom : IsLocalHom (algebraMap S (Ring R A S ψ)) := by
  refine ⟨fun s hs => ?_⟩
  apply (residue_ne_zero_iff_isUnit s).mp
  intro hz
  have hzero : point R A S ψ (algebraMap S (Ring R A S ψ) s) = 0 := by
    rw [AlgHom.commutes]
    exact hz
  exact (hs.map (point R A S ψ)).ne_zero hzero

/-- The actual right map completes the original base-change square. -/
def rightMap : A →ₐ[R] Ring R A S ψ :=
  (IsScalarTower.toAlgHom R (S ⊗[R] A) (Ring R A S ψ)).comp
    (Algebra.TensorProduct.includeRight : A →ₐ[R] S ⊗[R] A)

/-- The selected local point retains the specified point on the right algebra. -/
@[simp] theorem point_rightMap (a : A) : point R A S ψ (rightMap R A S ψ a) = ψ a := by
  change Localization.ResiduePoint.point (tensorPoint R A S ψ).toRingHom
    (algebraMap (S ⊗[R] A) (Ring R A S ψ) ((1 : S) ⊗ₜ[R] a)) = _
  rw [Localization.ResiduePoint.point_algebraMap]
  change tensorPoint R A S ψ ((1 : S) ⊗ₜ[R] a) = ψ a
  rw [tensorPoint_tmul, map_one, one_mul]

/-- A local specified right point gives a local right map into the actual selected DVR. -/
theorem rightMap_isLocalHom [IsLocalHom ψ.toRingHom] :
    IsLocalHom (rightMap R A S ψ).toRingHom := by
  refine ⟨fun a ha => ?_⟩
  apply isUnit_of_map_unit ψ.toRingHom a
  have h := ha.map (point R A S ψ)
  change IsUnit (point R A S ψ (rightMap R A S ψ a)) at h
  rwa [point_rightMap] at h

/-- The selected target residue field is canonically the original target residue field. -/
def residueEquiv : ResidueField (Ring R A S ψ) ≃+* ResidueField S :=
  Localization.ResiduePoint.residueEquiv (tensorPoint R A S ψ).toRingHom
    (tensorPoint_surjective R A S ψ)

@[simp] theorem residueEquiv_residue (x : Ring R A S ψ) :
    residueEquiv R A S ψ (residue (Ring R A S ψ) x) = point R A S ψ x := rfl

/-- The comparison is the inverse of the actual induced residue map from S. -/
@[simp] theorem residueEquiv_map (x : ResidueField S) :
    residueEquiv R A S ψ (ResidueField.map (algebraMap S (Ring R A S ψ)) x) = x := by
  obtain ⟨s, rfl⟩ := residue_surjective x
  rw [ResidueField.map_residue, residueEquiv_residue, AlgHom.commutes]
  rfl

variable [Algebra.FormallyEtale R A] [Algebra.EssFiniteType R A] [Module.Flat R A]

instance formallyEtale : Algebra.FormallyEtale S (Ring R A S ψ) := inferInstance

instance essFiniteType : Algebra.EssFiniteType S (Ring R A S ψ) :=
  Algebra.EssFiniteType.comp S (S ⊗[R] A) (Ring R A S ψ)

instance flat : Module.Flat S (Ring R A S ψ) := inferInstance

/-- No target-domain hypothesis is used: it follows from the actual local essentially étale map. -/
instance isDomain : IsDomain (Ring R A S ψ) :=
  Algebra.FormallyUnramified.isDomain_of_flat_local_dvr S (Ring R A S ψ)

/-- The selected target local ring is a DVR. -/
instance isDiscreteValuationRing : IsDiscreteValuationRing (Ring R A S ψ) :=
  Algebra.FormallyUnramified.isDiscreteValuationRing_of_flat_local_dvr S (Ring R A S ψ)

/-- Every original target uniformizer remains irreducible. -/
theorem irreducible_algebraMap {π : S} (hπ : Irreducible π) :
    Irreducible (algebraMap S (Ring R A S ψ) π) :=
  Algebra.FormallyUnramified.irreducible_algebraMap_of_flat_local_dvr S (Ring R A S ψ) hπ

end Algebra.SelectedEtaleBaseChange
