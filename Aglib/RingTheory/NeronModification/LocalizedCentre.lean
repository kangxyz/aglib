/-
Copyright (c) 2026 kangxyz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.RingTheory.NeronModification.GlobalPoint
public import Aglib.RingTheory.NeronModification.Localization
public import Mathlib.RingTheory.Localization.Ideal
public import Mathlib.RingTheory.Localization.FractionRing

/-! # Exact localization of the global residue centre

An injective map from the original residue target into the localized residue
target identifies the localized kernel with the extension of the original
kernel. This is an ideal equality, not merely a commuting evaluation square.
The last result separately supplies the actual modification-point square.
-/

@[expose] public noncomputable section

namespace Algebra.NeronModification

section Kernel

variable {B D Q F : Type*} [CommRing B] [CommRing D] [CommRing Q] [CommRing F]
variable (S : Submonoid B) [Algebra B D] [IsLocalization S D]
variable (r : B →+* Q) (j : Q →+* F)
variable (hS : ∀ s : S, IsUnit (j (r s)))

/-- The actual residue point extends to the source localization. -/
def localizedResiduePoint : D →+* F :=
  IsLocalization.lift (M := S) (g := j.comp r) hS

@[simp] theorem localizedResiduePoint_algebraMap (b : B) :
    localizedResiduePoint S r j hS (algebraMap B D b) = j (r b) :=
  IsLocalization.lift_eq hS b

/-- Injectivity of the residue-target comparison gives the exact localized centre. -/
theorem ker_localizedResiduePoint (hj : Function.Injective j) :
    RingHom.ker (localizedResiduePoint (D := D) S r j hS) =
      (RingHom.ker r).map (algebraMap B D) := by
  apply le_antisymm
  · intro x hx
    obtain ⟨b, s, rfl⟩ := IsLocalization.exists_mk'_eq S x
    have hb : j (r b) = 0 := by
      have h := (IsLocalization.lift_mk'_spec hS b 0 s).mp hx
      simpa only [RingHom.comp_apply, mul_zero] using h
    have hr : r b = 0 := hj (hb.trans (map_zero j).symm)
    apply (IsLocalization.mk'_mem_map_algebraMap_iff S D (RingHom.ker r) b s).mpr
    exact ⟨1, S.one_mem, by simpa only [one_mul, RingHom.mem_ker] using hr⟩
  · apply Ideal.map_le_iff_le_comap.mpr
    intro b hb
    change localizedResiduePoint S r j hS (algebraMap B D b) = 0
    rw [localizedResiduePoint_algebraMap, show r b = 0 from hb, map_zero]

end Kernel

section FractionResidue

variable {B D Q : Type*} [CommRing B] [CommRing D] [CommRing Q] [IsDomain Q]
variable (S : Submonoid B) [Algebra B D] [IsLocalization S D]
variable (r : B →+* Q) (hS : ∀ s : S, r s ≠ 0)

/-- The canonical residue-fraction point, using the actual fraction ring of the residue target. -/
def localizedResidueFractionPoint : D →+* FractionRing Q :=
  localizedResiduePoint S r (algebraMap Q (FractionRing Q)) (fun s =>
    IsUnit.mk0 _ ((map_ne_zero_iff _ (IsFractionRing.injective Q (FractionRing Q))).mpr (hS s)))

/-- No separately chosen target embedding is needed for the canonical fraction-residue centre. -/
theorem ker_localizedResidueFractionPoint :
    RingHom.ker (localizedResidueFractionPoint (D := D) S r hS) =
      (RingHom.ker r).map (algebraMap B D) :=
  ker_localizedResiduePoint S r (algebraMap Q (FractionRing Q)) _
    (IsFractionRing.injective Q (FractionRing Q))

end FractionResidue

section ActualCentre

variable {P B C D F : Type*} [CommRing P] [CommRing B] [CommRing C]
variable [CommRing D] [CommRing F] [Algebra P B] [Algebra P C]
variable (p : P) (f : B →ₐ[P] C) (S : Submonoid B)
variable [Algebra B D] [IsLocalization S D]
variable (j : (C ⧸ Ideal.span {algebraMap P C p}) →+* F)
variable (hS : ∀ s : S,
  IsUnit (j (Ideal.Quotient.mk (Ideal.span {algebraMap P C p}) (f s))))

/-- The actual uniformizer centre, after localizing the source, is exactly its extension.
For the power-series application, `j` is the canonical injection of the residue
power-series ring into its fraction field. -/
theorem residueCentre_localization (hj : Function.Injective j) :
    RingHom.ker (localizedResiduePoint (D := D) S
      ((Ideal.Quotient.mk (Ideal.span {algebraMap P C p})).comp f.toRingHom) j hS) =
      (residueCentre p f).map (algebraMap B D) :=
  ker_localizedResiduePoint S _ j hS hj

end ActualCentre

section ModificationPoint

variable {B D C T ι : Type*} [CommRing B] [CommRing D] [CommRing C] [CommRing T]
variable [Algebra B D] (p : B) (g : ι → B)
variable (f : B →+* C) (z : ι → C) (hz : ∀ i, f p * z i = f (g i))
variable (hp : IsRegular (f p)) (c : C →+* T) (d : D →+* T)
variable (hcomm : d.comp (algebraMap B D) = c.comp f)
variable (w : ι → T)
variable (hw : ∀ i, d (algebraMap B D p) * w i = d (algebraMap B D (g i)))
variable (hd : IsRegular (d (algebraMap B D p)))

include hcomm in
/-- The actual local modification lift restricts to the localization of the global lift.
Uniqueness uses only the same original coefficients and regularity; no domain
assumption on the auxiliary source is introduced. -/
theorem lift_comp_baseChangeOriginal :
    (lift (algebraMap B D p) (fun i => algebraMap B D (g i)) d w hw hd).comp
        (baseChangeOriginal (B' := D) p g).toRingHom =
      c.comp (lift p g f z hz hp) := by
  have hc : IsRegular ((c.comp f) p) := by
    rw [← hcomm]
    exact hd
  have hcz (i : ι) : (c.comp f) p * c (z i) = (c.comp f) (g i) := by
    change c (f p) * c (z i) = c (f (g i))
    rw [← map_mul, hz]
  apply (lift_unique p g (c.comp f) (fun i => c (z i)) hcz hc _ ?_).trans
    (lift_unique p g (c.comp f) (fun i => c (z i)) hcz hc _ ?_).symm
  · ext b
    change lift _ _ d w hw hd (baseChangeOriginal p g (of p g b)) = c (f b)
    rw [baseChangeOriginal_of, lift_of]
    exact DFunLike.congr_fun hcomm b
  · ext b
    change c (lift p g f z hz hp (of p g b)) = c (f b)
    rw [lift_of]

end ModificationPoint

end Algebra.NeronModification
