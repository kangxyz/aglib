/-
Copyright (c) 2026 algebraic-geometry contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Mathlib.RingTheory.Smooth.Local
public import Mathlib.RingTheory.Smooth.Field

/-!
# A local smoothness criterion from an intersection of ideals

For a presentation `P → S`, the identity `I ∩ m² = mI` makes the first map
of the cotangent sequence injective after passage to the residue field,
provided that field is formally smooth over the base. The local Jacobian
criterion then gives formal smoothness of `S`.
-/

@[expose] public section

noncomputable section

open TensorProduct IsLocalRing KaehlerDifferential

namespace Algebra.FormallySmooth

variable {R P S K : Type*} [CommRing R] [CommRing P] [CommRing S] [CommRing K]
variable [Algebra R P] [Algebra R K]
variable [Algebra P S] [Algebra S K] [Algebra P K]
variable [IsScalarTower P S K] [IsScalarTower R P K]

/-- The ideal intersection criterion gives the injectivity needed in the
Jacobian criterion, when the final quotient is formally smooth. -/
theorem cotangentComplexBaseChange_injective_of_inf_sq_le_mul
    [Algebra.FormallySmooth R P] [Algebra.FormallySmooth R K]
    (hPK : Function.Surjective (algebraMap P K))
    (hI : RingHom.ker (algebraMap P S) ⊓ RingHom.ker (algebraMap P K) ^ 2 ≤
      RingHom.ker (algebraMap P K) * RingHom.ker (algebraMap P S)) :
    Function.Injective (cotangentComplexBaseChange R S P K) := by
  let I := RingHom.ker (algebraMap P S)
  let J := RingHom.ker (algebraMap P K)
  have hIJ : I ≤ J := by
    intro x hx
    rw [RingHom.mem_ker, IsScalarTower.algebraMap_apply P S K x,
      RingHom.mem_ker.mp hx, map_zero]
  have hd : Function.Injective (kerCotangentToTensor R P K) :=
    (kerCotangentToTensor_injective_iff hPK).mpr inferInstance
  rw [injective_iff_map_eq_zero]
  intro z hz
  obtain ⟨x, rfl⟩ := TensorProduct.mk_surjective (R := P) (S := K) (M := I) hPK z
  simp only [TensorProduct.mk_apply] at hz ⊢
  change (1 : K) • ((1 : K) ⊗ₜ[P] D R P (x : P)) = 0 at hz
  have hxJ : (x : P) ∈ J := hIJ x.property
  have hdx : kerCotangentToTensor R P K (J.toCotangent ⟨x, hxJ⟩) = 0 := by
    simpa only [J, one_smul,
      kerCotangentToTensor_toCotangent] using hz
  have hx2 : (x : P) ∈ J ^ 2 :=
    (J.toCotangent_eq_zero ⟨x, hxJ⟩).mp (hd (hdx.trans (map_zero _).symm))
  have hxmul : (x : P) ∈ J * I := hI ⟨x.property, hx2⟩
  have hm : (J • (⊤ : Submodule P I)).map I.subtype = J * I := by
    rw [Submodule.map_smul'', Submodule.map_subtype_top, Ideal.smul_eq_mul]
  rw [← hm] at hxmul
  obtain ⟨y, hy, hxy⟩ := hxmul
  have hxy' : y = x := Subtype.ext hxy
  subst y
  refine Submodule.smul_induction_on hy ?_ ?_
  · intro a ha y _
    rw [TensorProduct.tmul_smul, TensorProduct.smul_tmul',
      ← Algebra.algebraMap_eq_smul_one, RingHom.mem_ker.mp ha, zero_tmul]
  · intro x y hx hy
    rw [tmul_add, hx, hy, add_zero]

variable [Algebra R S] [IsScalarTower R P S]

/-- A local presentation is formally smooth if its kernel has the expected
intersection with the square of the maximal ideal and its residue field is
formally smooth over the base. -/
theorem of_ker_inf_maximalIdeal_sq
    [IsLocalRing P] [IsLocalRing S]
    [Algebra.FormallySmooth R P]
    [Module.Free P Ω[P⁄R]] [Module.Finite P Ω[P⁄R]]
    [Algebra.FormallySmooth R (ResidueField S)]
    (hPS : Function.Surjective (algebraMap P S))
    (hfg : (RingHom.ker (algebraMap P S)).FG)
    (hI : RingHom.ker (algebraMap P S) ⊓ maximalIdeal P ^ 2 ≤
      maximalIdeal P * RingHom.ker (algebraMap P S)) :
    Algebra.FormallySmooth R S := by
  let : IsLocalHom (algebraMap P S) := .of_surjective _ hPS
  have hPK : Function.Surjective (algebraMap P (ResidueField S)) := by
    rw [IsScalarTower.algebraMap_eq P S (ResidueField S)]
    exact residue_surjective.comp hPS
  have hker : RingHom.ker (algebraMap P (ResidueField S)) = maximalIdeal P := by
    ext x
    change residue S (algebraMap P S x) = 0 ↔ x ∈ maximalIdeal P
    rw [residue_eq_zero_iff, ← Ideal.mem_comap, maximalIdeal_comap]
  apply (iff_injective_cotangentComplexBaseChange_residueField P hPS hfg).mpr
  apply cotangentComplexBaseChange_injective_of_inf_sq_le_mul hPK
  simpa only [hker] using hI

end Algebra.FormallySmooth
