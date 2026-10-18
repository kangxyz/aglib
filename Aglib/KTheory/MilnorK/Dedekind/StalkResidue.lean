/-
Copyright (c) 2026 Motivic Cohomology contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.DedekindPointStalk
public import Aglib.KTheory.MilnorK.Dedekind.ResidueSupport
public import Aglib.KTheory.MilnorK.CompleteDVRResidueEquiv
public import Aglib.KTheory.MilnorK.DVRValueCartierLength

/-! # Original field residues in actual Dedekind scheme stalks -/

@[expose] public noncomputable section
namespace MilnorK.DedekindStalkResidue

open AlgebraicGeometry IsDedekindDomain
attribute [local instance] DedekindPointStalk.stalkLocalization
  DedekindPointStalk.stalkDomain DedekindPointStalk.stalkLocal

variable (S E : Type*) [CommRing S] [IsDedekindDomain S]
  [Field E] [Algebra S E] [IsFractionRing S E]

/-- The actual scheme stalk maps into the unchanged original fraction field. -/
instance fractionAlgebra (q : HeightOneSpectrum S) :
    Algebra ((Spec.structureSheaf S).presheaf.stalk (DedekindPointStalk.point q)) E :=
  ((algebraMap (Localization.AtPrime q.asIdeal) E).comp
    (DedekindPointStalk.localizationEquiv q).symm.toRingHom).toAlgebra

/-- This exact map extends the original ring map, not an unrelated field embedding. -/
instance fractionTower (q : HeightOneSpectrum S) :
    IsScalarTower S ((Spec.structureSheaf S).presheaf.stalk (DedekindPointStalk.point q)) E := by
  apply IsScalarTower.of_algebraMap_eq
  intro s
  change algebraMap S E s = algebraMap (Localization.AtPrime q.asIdeal) E
    ((DedekindPointStalk.localizationEquiv q).symm
      (algebraMap S ((Spec.structureSheaf S).presheaf.stalk (DedekindPointStalk.point q)) s))
  rw [(DedekindPointStalk.localizationEquiv q).symm.commutes]
  exact IsScalarTower.algebraMap_apply S (Localization.AtPrime q.asIdeal) E s

/-- The original function field is a fraction field of this actual stalk. -/
instance fractionRing (q : HeightOneSpectrum S) :
    IsFractionRing ((Spec.structureSheaf S).presheaf.stalk (DedekindPointStalk.point q)) E :=
  (IsFractionRing.isFractionRing_iff_of_base_ringEquiv E
    (DedekindPointStalk.localizationEquiv q).toRingEquiv).mp inferInstance

/-- The actual scheme-stalk residue is the original Dedekind residue transported
by the canonical local residue equivalence, on the unchanged original class. -/
theorem residue_eq (q : HeightOneSpectrum S) (n : ℕ) (x : K E (n + 1)) :
    MilnorK.map n (DedekindPointStalk.residueEquiv q).toRingHom
      (DVR.residue (Localization.AtPrime q.asIdeal) E n x) =
        DVR.residue ((Spec.structureSheaf S).presheaf.stalk (DedekindPointStalk.point q))
          E n x := by
  have h := DVR.residue_equiv_apply (DedekindPointStalk.localizationEquiv q).toRingEquiv
    (RingEquiv.refl E) (fun s => by
      change algebraMap (Localization.AtPrime q.asIdeal) E s =
        algebraMap (Localization.AtPrime q.asIdeal) E
          ((DedekindPointStalk.localizationEquiv q).symm
            ((DedekindPointStalk.localizationEquiv q) s))
      rw [AlgEquiv.symm_apply_apply]) n x
  have hid : (RingEquiv.refl E).toRingHom = RingHom.id E := rfl
  simpa only [DedekindPointStalk.residueEquiv, hid, MilnorK.map_id,
    LinearMap.id_apply] using h

/-- The Milnor integer orders agree under the same original local-to-stalk map. -/
theorem value_eq (q : HeightOneSpectrum S) (b : Eˣ) :
    MilnorK.K2.DVR.value (Localization.AtPrime q.asIdeal) E (Additive.ofMul b) =
      MilnorK.K2.DVR.value
        ((Spec.structureSheaf S).presheaf.stalk (DedekindPointStalk.point q)) E
          (Additive.ofMul b) := by
  have h := congrArg (zeroEquiv
    (IsLocalRing.ResidueField
      ((Spec.structureSheaf S).presheaf.stalk (DedekindPointStalk.point q))))
    (residue_eq S E q 0 (unitsToOne E (Additive.ofMul b)))
  rw [zeroEquiv_map, DVR.zeroEquiv_residue, DVR.zeroEquiv_residue] at h
  have hu : oneEquiv E (unitsToOne E (Additive.ofMul b)) = Additive.ofMul b :=
    (oneEquiv E).apply_symm_apply _
  simpa only [hu] using h

/-- The original scalar's Milnor order equals the actual scheme-stalk Cartier
multiplicity, before any finite-fiber reindexing. -/
theorem value_scalar_eq_stalkLength (q : HeightOneSpectrum S) (s : S) (hs : s ≠ 0) :
    MilnorK.K2.DVR.value (Localization.AtPrime q.asIdeal) E
      (Additive.ofMul (Units.mk0 (algebraMap S E s)
        ((map_ne_zero_iff (algebraMap S E) (IsFractionRing.injective S E)).mpr hs))) =
      ((Module.length
        ((Spec.structureSheaf S).presheaf.stalk (DedekindPointStalk.point q))
        (((Spec.structureSheaf S).presheaf.stalk (DedekindPointStalk.point q)) ⧸
          Ideal.ofList [algebraMap S
            ((Spec.structureSheaf S).presheaf.stalk
              (DedekindPointStalk.point q)) s])).toNat : ℤ) := by
  let T := (Spec.structureSheaf S).presheaf.stalk (DedekindPointStalk.point q)
  have ht : algebraMap S T s ≠ 0 :=
    (map_ne_zero_iff (algebraMap S T)
      (IsLocalization.injective T q.asIdeal.primeCompl_le_nonZeroDivisors)).mpr hs
  rw [value_eq S E q]
  have h := MilnorK.K2.DVR.value_ringElement_eq_cartierLength T E (algebraMap S T s) ht
  convert h using 2
  apply congrArg Additive.ofMul
  apply Units.ext
  exact IsScalarTower.algebraMap_apply S T E s

end MilnorK.DedekindStalkResidue
