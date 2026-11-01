/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.Spec.PowerSeriesFiniteEtaleMaps
public import Aglib.AlgebraicGeometry.Morphisms.FiniteEtale.BaseChange.RestrictIso
public import Aglib.RingTheory.Smooth.SplitSectionAugmentation

/-! # Finite-etale maps on original smooth section completions

The power-series presentation and its whole augmentation square are constructed
from the original smooth algebra and section. Transport uses the same native
completion and the actual chosen open, without an input completion comparison.
-/

@[expose] public noncomputable section

open CategoryTheory

namespace AlgebraicGeometry.Scheme

open FiniteEtale
universe u

/-- Actual finite-etale restriction to a punctured section of its original smooth
section-adic completion is fully faithful over a normal Noetherian local domain. -/
def smoothSplitSectionPuncturedFiniteEtale_fullyFaithful
    {R B : Type u} [CommRing R] [IsDomain R] [IsLocalRing R]
    [IsNoetherianRing R] [IsIntegrallyClosed R] [CommRing B] [Algebra R B]
    [Algebra.Smooth R B] (ε : B →ₐ[R] R)
    (W : (Spec (.of (AdicCompletion (RingHom.ker ε.toRingHom) B))).Opens)
    (hdim : 2 ≤ ringKrullDim R)
    (hW : splitSectionOpen
      (AdicCompletion.kerProj (Algebra.Smooth.splitSection_surjective ε)).toRingHom W =
        puncturedSpecOpen R) :
    (baseChange (Spec.map (CommRingCat.ofHom
      (AdicCompletion.kerProj (Algebra.Smooth.splitSection_surjective ε)).toRingHom)
        ∣_ W)).FullyFaithful := by
  apply Classical.choice
  obtain ⟨n, x, e, he, hε⟩ := Algebra.Smooth.exists_fin_splitSectionCompletion_augmentation ε
  let s := Spec.map (CommRingCat.ofHom
    (MvPowerSeries.constantCoeff : MvPowerSeries (Fin n) R →+* R))
  let k := Spec.map (CommRingCat.ofHom e.symm.toRingHom)
  let : IsIso k := by
    change IsIso (Scheme.Spec.mapIso e.toRingEquiv.symm.toCommRingCatIso.op).hom
    infer_instance
  have hs : s ≫ k = Spec.map (CommRingCat.ofHom
      (AdicCompletion.kerProj (Algebra.Smooth.splitSection_surjective ε)).toRingHom) := by
    change Spec.map _ ≫ Spec.map _ = Spec.map _
    rw [← Spec.map_comp, ← CommRingCat.ofHom_comp]
    apply congrArg (fun φ => Spec.map (CommRingCat.ofHom φ))
    ext z
    have h := RingHom.congr_fun hε (e.symm z)
    change AdicCompletion.kerProj (Algebra.Smooth.splitSection_surjective ε)
      (e (e.symm z)) = MvPowerSeries.constantCoeff (e.symm z) at h
    rw [AlgEquiv.apply_symm_apply] at h
    exact h.symm
  have hV : splitSectionOpen
      (MvPowerSeries.constantCoeff : MvPowerSeries (Fin n) R →+* R) (k ⁻¹ᵁ W) =
        puncturedSpecOpen R := by
    change s ⁻¹ᵁ k ⁻¹ᵁ W = _
    rw [← Hom.comp_preimage, hs]
    exact hW
  let hf := powerSeriesPuncturedFiniteEtale_zeroSection_fullyFaithful (k ⁻¹ᵁ W) hdim hV
  let hc := restriction_fullyFaithful_comp_iso s k W hf
  exact ⟨Eq.mp (congrArg
    (fun f => (baseChange (f ∣_ W)).FullyFaithful) hs) hc⟩

end AlgebraicGeometry.Scheme
