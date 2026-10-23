/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.RingTheory.Descent.FormalGluing.FiniteModification
public import Aglib.RingTheory.AdicCompletion.BoundedKernelSeparation
public import Mathlib.RingTheory.Ideal.Quotient.Operations

/-!
# Actual conductor torsion and compatible quotient algebras

The original conductor defines the actual ideal `Ann_D(t)`. Its quotient
makes the same conductor regular, while native Artin–Rees separates this
ideal from an actual high ideal power in a finite algebra. The original
quotient diagonal then identifies the original algebra with its compatible
quotient pairs. No comaximality or descended-algebra premise is introduced.
The final scalar-extension assembly remains a separate obligation.
-/

@[expose] public noncomputable section

namespace Algebra.Descent.FormalGluing

variable {S : Type*} [CommRing S]

section TorsionIdeal

variable {D : Type*} [CommRing D] [Algebra S D]

/-- The actual ideal of elements killed by the original conductor scalar. -/
abbrev conductorTorsionIdeal (t : S) : Ideal D :=
  (LinearMap.lsmul D D (algebraMap S D t)).ker

theorem mem_conductorTorsionIdeal (t : S) (z : D) :
    z ∈ conductorTorsionIdeal (D := D) t ↔ t • z = 0 := by
  change algebraMap S D t * z = 0 ↔ t • z = 0
  rw [Algebra.smul_def]

/-- The torsion ideal has zero intersection with the original scalar image. -/
theorem algebraMap_mem_conductorTorsionIdeal_iff (t : S)
    (hinj : Function.Injective (algebraMap S D)) (hreg : IsSMulRegular S t) (s : S) :
    algebraMap S D s ∈ conductorTorsionIdeal (D := D) t ↔ s = 0 := by
  constructor
  · intro hs
    have hts : t * s = 0 := hinj (by
      rw [map_mul, map_zero]
      simpa only [Algebra.smul_def] using (mem_conductorTorsionIdeal t _).mp hs)
    exact hreg (by simpa only [smul_eq_mul, mul_zero] using hts)
  · rintro rfl
    rw [map_zero]
    exact (conductorTorsionIdeal (D := D) t).zero_mem

/-- A conductor product already lies in S, so t²-torsion is t-torsion.
This is the actual argument making the quotient t-regular. -/
theorem conductor_double_torsion (t : S)
    (hinj : Function.Injective (algebraMap S D)) (hreg : IsSMulRegular S t)
    (hcond : ∀ z : D, ∃ s : S, algebraMap S D s = t • z)
    (z : D) (hz : t • (t • z) = 0) : t • z = 0 := by
  obtain ⟨s, hs⟩ := hcond z
  have hts : t * s = 0 := hinj (by
    rw [map_mul, map_zero, ← Algebra.smul_def, hs]
    exact hz)
  have hs0 : s = 0 := hreg (by simpa only [smul_eq_mul, mul_zero] using hts)
  rw [← hs, hs0, map_zero]

/-- The original scalar map stays injective after quotienting by its
actual conductor torsion ideal. -/
theorem conductorTorsionQuotient_algebraMap_injective (t : S)
    (hinj : Function.Injective (algebraMap S D)) (hreg : IsSMulRegular S t) :
    Function.Injective (algebraMap S (D ⧸ conductorTorsionIdeal (D := D) t)) := by
  intro a b hab
  change Ideal.Quotient.mk (conductorTorsionIdeal (D := D) t) (algebraMap S D a) =
    Ideal.Quotient.mk (conductorTorsionIdeal (D := D) t) (algebraMap S D b) at hab
  have hmem : algebraMap S D (a - b) ∈ conductorTorsionIdeal (D := D) t := by
    rw [map_sub]
    exact Ideal.Quotient.eq.mp hab
  exact sub_eq_zero.mp ((algebraMap_mem_conductorTorsionIdeal_iff t hinj hreg _).mp hmem)

/-- The same original conductor is regular on the actual quotient D/Ann(t). -/
theorem conductorTorsionQuotient_regular (t : S)
    (hinj : Function.Injective (algebraMap S D)) (hreg : IsSMulRegular S t)
    (hcond : ∀ z : D, ∃ s : S, algebraMap S D s = t • z) :
    IsSMulRegular (D ⧸ conductorTorsionIdeal (D := D) t) t := by
  intro x y hxy
  obtain ⟨a, rfl⟩ := Ideal.Quotient.mk_surjective x
  obtain ⟨b, rfl⟩ := Ideal.Quotient.mk_surjective y
  apply Ideal.Quotient.eq.mpr
  apply (mem_conductorTorsionIdeal t (a - b)).mpr
  apply conductor_double_torsion t hinj hreg hcond (a - b)
  have hqa := (Ideal.Quotient.mkₐ S (conductorTorsionIdeal (D := D) t)).toLinearMap.map_smul t a
  have hqb := (Ideal.Quotient.mkₐ S (conductorTorsionIdeal (D := D) t)).toLinearMap.map_smul t b
  have hq : Ideal.Quotient.mk (conductorTorsionIdeal (D := D) t) (t • a) =
      Ideal.Quotient.mk (conductorTorsionIdeal (D := D) t) (t • b) :=
    hqa.trans (hxy.trans hqb.symm)
  have hmem := (mem_conductorTorsionIdeal t _).mp (Ideal.Quotient.eq.mp hq)
  simpa only [smul_sub] using hmem

/-- An actual conductor ideal annihilates the torsion submodule. -/
theorem conductor_smul_torsion_eq_bot (t : S)
    (hinj : Function.Injective (algebraMap S D)) (hreg : IsSMulRegular S t)
    (J : Ideal S)
    (hcond : ∀ r ∈ J, ∀ z : D, ∃ s : S, algebraMap S D s = r • z) :
    J • (conductorTorsionIdeal (D := D) t).restrictScalars S = ⊥ := by
  apply le_antisymm _ bot_le
  apply Submodule.smul_le.mpr
  intro r hr z hz
  obtain ⟨s, hs⟩ := hcond r hr z
  have hts : t * s = 0 := hinj (by
    rw [map_mul, map_zero, ← Algebra.smul_def, hs, smul_comm t r z,
      (mem_conductorTorsionIdeal t z).mp hz, smul_zero])
  have hs0 : s = 0 := hreg (by simpa only [smul_eq_mul, mul_zero] using hts)
  change r • z = 0
  rw [← hs, hs0, map_zero]

/-- The original conductor products pass to the actual torsion quotient. -/
theorem conductorTorsionQuotient_conductor (t : S) (J : Ideal S)
    (hcond : ∀ r ∈ J, ∀ z : D, ∃ s : S, algebraMap S D s = r • z) :
    ∀ r ∈ J, ∀ z : D ⧸ conductorTorsionIdeal (D := D) t,
      ∃ s : S, algebraMap S (D ⧸ conductorTorsionIdeal (D := D) t) s = r • z := by
  intro r hr z
  obtain ⟨x, rfl⟩ := Ideal.Quotient.mk_surjective z
  obtain ⟨s, hs⟩ := hcond r hr x
  refine ⟨s, ?_⟩
  calc
    algebraMap S (D ⧸ conductorTorsionIdeal (D := D) t) s =
        Ideal.Quotient.mk (conductorTorsionIdeal (D := D) t) (r • x) :=
      congrArg (Ideal.Quotient.mk (conductorTorsionIdeal (D := D) t)) hs
    _ = r • Ideal.Quotient.mk (conductorTorsionIdeal (D := D) t) x :=
      (Ideal.Quotient.mkₐ S (conductorTorsionIdeal (D := D) t)).toLinearMap.map_smul r x

/-- Native Artin–Rees separates the actual torsion ideal from an actual
power of the extended ideal. Neither Jacobson containment nor separatedness
of an adic completion is assumed. -/
theorem exists_pow_map_inf_conductorTorsion_eq_bot [IsNoetherianRing S] [Module.Finite S D]
    (t : S) (hinj : Function.Injective (algebraMap S D)) (hreg : IsSMulRegular S t)
    (I : Ideal S) (n : ℕ)
    (hcond : ∀ r ∈ I ^ n, ∀ z : D, ∃ s : S, algebraMap S D s = r • z) :
    ∃ m : ℕ, (I ^ m).map (algebraMap S D) ⊓ conductorTorsionIdeal (D := D) t = ⊥ := by
  have hann : I ^ n • (conductorTorsionIdeal (D := D) t).restrictScalars S = ⊥ :=
    conductor_smul_torsion_eq_bot t hinj hreg (I ^ n) hcond
  obtain ⟨m, hm⟩ := Submodule.exists_pow_smul_top_inf_eq_bot_of_pow_smul_eq_bot
    (R := S) (M := D) I ((conductorTorsionIdeal (D := D) t).restrictScalars S) n hann
  refine ⟨m, le_antisymm ?_ bot_le⟩
  intro z hz
  have hzm : z ∈ I ^ m • (⊤ : Submodule S D) ⊓
      (conductorTorsionIdeal (D := D) t).restrictScalars S := by
    refine ⟨?_, hz.2⟩
    rw [Ideal.smul_top_eq_map]
    exact hz.1
  rw [hm] at hzm
  exact hzm

end TorsionIdeal

section QuotientFibreProduct

variable {D : Type*} [CommRing D] [Algebra S D]

/-- The actual compatible quotient pairs, with componentwise ring operations. -/
def quotientFibreProduct (T K : Ideal D) : Subalgebra S ((D ⧸ T) × (D ⧸ K)) :=
  AlgHom.equalizer
    ((Ideal.Quotient.factorₐ S (show T ≤ T ⊔ K from le_sup_left)).comp
      (AlgHom.fst S (D ⧸ T) (D ⧸ K)))
    ((Ideal.Quotient.factorₐ S (show K ≤ T ⊔ K from le_sup_right)).comp
      (AlgHom.snd S (D ⧸ T) (D ⧸ K)))

/-- The diagonal of the two original quotient maps, with the compatibility
in the original common quotient built into its codomain. -/
def quotientDiagonal (T K : Ideal D) : D →ₐ[S] quotientFibreProduct (S := S) T K :=
  ((Ideal.Quotient.mkₐ S T).prod (Ideal.Quotient.mkₐ S K)).codRestrict _ (fun _ => rfl)

@[simp]
theorem quotientDiagonal_coe (T K : Ideal D) (z : D) :
    (quotientDiagonal (S := S) T K z : (D ⧸ T) × (D ⧸ K)) =
      (Ideal.Quotient.mk T z, Ideal.Quotient.mk K z) := rfl

/-- Zero intersection makes the original quotient diagonal injective. -/
theorem quotientDiagonal_injective (T K : Ideal D) (hTK : T ⊓ K = ⊥) :
    Function.Injective (quotientDiagonal (S := S) T K) := by
  intro a b hab
  have ha : a - b ∈ T := Ideal.Quotient.eq.mp
    (congrArg (fun z : quotientFibreProduct (S := S) T K => z.val.1) hab)
  have hb : a - b ∈ K := Ideal.Quotient.eq.mp
    (congrArg (fun z : quotientFibreProduct (S := S) T K => z.val.2) hab)
  have h : a - b ∈ T ⊓ K := ⟨ha, hb⟩
  rw [hTK] at h
  exact sub_eq_zero.mp h

/-- A compatible pair of quotient classes lifts through the original
quotient maps. No comaximality hypothesis is used. -/
theorem quotientDiagonal_surjective (T K : Ideal D) :
    Function.Surjective (quotientDiagonal (S := S) T K) := by
  rintro ⟨⟨a', b'⟩, hab⟩
  obtain ⟨a, rfl⟩ := Ideal.Quotient.mk_surjective a'
  obtain ⟨b, rfl⟩ := Ideal.Quotient.mk_surjective b'
  change Ideal.Quotient.mk (T ⊔ K) a = Ideal.Quotient.mk (T ⊔ K) b at hab
  obtain ⟨u, hu, v, hv, huv⟩ := Submodule.mem_sup.mp (Ideal.Quotient.eq.mp hab)
  refine ⟨a - u, Subtype.ext (Prod.ext ?_ ?_)⟩
  · apply Ideal.Quotient.eq.mpr
    have he : (a - u) - a = -u := by
      rw [sub_right_comm a u a, sub_self, zero_sub]
    rw [he]
    exact T.neg_mem hu
  · apply Ideal.Quotient.eq.mpr
    have he : (a - u) - b = v := by
      have hv' : v = (a - b) - u :=
        (eq_sub_iff_add_eq).mpr ((add_comm v u).trans huv)
      rw [sub_right_comm a u b, ← hv']
    rw [he]
    exact hv

/-- The actual quotient-diagonal algebra equivalence, preserving both
original quotient maps and the original S-algebra structure. -/
def quotientFibreProductEquiv (T K : Ideal D) (hTK : T ⊓ K = ⊥) :
    D ≃ₐ[S] quotientFibreProduct (S := S) T K :=
  AlgEquiv.ofBijective (quotientDiagonal T K)
    ⟨quotientDiagonal_injective T K hTK, quotientDiagonal_surjective T K⟩

end QuotientFibreProduct

end Algebra.Descent.FormalGluing
