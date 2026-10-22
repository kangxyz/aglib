/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.Blowup.AdmissibleSequence.Refinement
public import Aglib.AlgebraicGeometry.Blowup.AdmissibleSequence.ProtectedOpen
public import Aglib.AlgebraicGeometry.Blowup.AdmissibleSequence.Density
public import Aglib.AlgebraicGeometry.SchemeTheoreticImage.ClosedIdentification
public import Aglib.AlgebraicGeometry.Morphisms.IsIso.OpenHomExt
public import Aglib.AlgebraicGeometry.Morphisms.SchemeTheoreticallyDominant

/-!
# The reverse domain is the actual replayed modification

An admissible sequence is replayed along the original partial map. Its closed
comparison and the reverse closed graph have the same schematically dense
original source. Their native kernel ideals therefore identify the reverse
domain with the replayed sequence, preserving both structural projections.
-/

@[expose] public noncomputable section

open CategoryTheory Limits

universe u

namespace AlgebraicGeometry.Scheme.QuasiDomination

/-- Identification with an actual replayed sequence, not merely a proper map.
The quasi-compactness of the original open is used only for propagation of
schematic density along the replayed sequence. -/
theorem exists_reverse_domain_identification
    {X T V W : Scheme.{u}} (U : X.Opens) (β : T ⟶ X)
    (hβ : Blowup.AdmissibleSequence U β)
    (φ : V ⟶ X) [LocallyOfFiniteType φ]
    (u : U.toScheme ⟶ V) [IsOpenImmersion u] [QuasiCompact u]
    [IsSchemeTheoreticallyDominant u] (hu : u ≫ φ = U.ι)
    (j : W ⟶ T) (ψ : W ⟶ V) (w : j ≫ β = ψ ≫ φ)
    [IsClosedImmersion (pullback.lift j ψ w)]
    (k : U.toScheme ⟶ W) [IsSchemeTheoreticallyDominant k]
    (hkj : k ≫ j ≫ β = U.ι) (hkψ : k ≫ ψ = u) :
    ∃ (Vn : Scheme.{u}) (γ : Vn ⟶ V) (a : Vn ⟶ T)
      (t : U.toScheme ⟶ Vn) (e : W ≅ Vn),
      Blowup.AdmissibleSequence u.opensRange γ ∧
      IsSchemeTheoreticallyDominant t ∧ t ≫ γ = u ∧
      e.hom ≫ γ = ψ ∧ e.hom ≫ a = j ∧ k ≫ e.hom = t ∧
      Blowup.AdmissibleSequence u.opensRange ψ := by
  classical
  obtain ⟨Vn, γ, a, he, hγ, hc⟩ := hβ.exists_closed_domination φ
  let UV := u.opensRange
  have hUV : UV ≤ φ ⁻¹ᵁ U := by
    intro x hx
    obtain ⟨z, rfl⟩ := hx
    change (u ≫ φ) z ∈ U
    rw [hu]
    exact z.property
  have hγU : Blowup.AdmissibleSequence UV γ := hγ.mono hUV
  let : IsIso (γ ∣_ UV) := hγU.restrict_isIso
  let : IsIso (β ∣_ U) := hβ.restrict_isIso
  let E := asIso (γ ∣_ UV)
  let : QuasiCompact UV.ι := by
    rw [← u.isoOpensRange_inv_comp]
    infer_instance
  let : IsSchemeTheoreticallyDominant UV.ι := by
    rw [← u.isoOpensRange_inv_comp]
    infer_instance
  let : IsSchemeTheoreticallyDominant (γ ⁻¹ᵁ UV).ι :=
    hγU.preimage_open_isSchemeTheoreticallyDominant
  let t := u.isoOpensRange.hom ≫ E.inv ≫ (γ ⁻¹ᵁ UV).ι
  let : IsSchemeTheoreticallyDominant t := inferInstance
  have htγ : t ≫ γ = u := by
    calc
      t ≫ γ = u.isoOpensRange.hom ≫ E.inv ≫ (γ ∣_ UV) ≫ UV.ι := by
        simp only [t, Category.assoc, morphismRestrict_ι]
      _ = u.isoOpensRange.hom ≫ UV.ι :=
        congrArg (fun z ↦ u.isoOpensRange.hom ≫ z) (Iso.inv_hom_id_assoc E UV.ι)
      _ = u := u.isoOpensRange_hom_ι
  have hta : t ≫ a = k ≫ j := by
    apply β.ext_of_isIso_restriction U (𝟙 U.toScheme)
    · rw [Category.assoc, he, ← Category.assoc t γ, htγ, hu, Category.id_comp]
    · simpa only [Category.assoc, Category.id_comp] using hkj
  let c := pullback.lift a γ he
  let cW := pullback.lift j ψ w
  let : IsClosedImmersion c := hc
  have ht : k ≫ cW = t ≫ c := by
    apply pullback.hom_ext
    · simpa only [cW, c, Category.assoc, pullback.lift_fst] using hta.symm
    · simpa only [cW, c, Category.assoc, pullback.lift_snd] using hkψ.trans htγ.symm
  let e := closedIsoOfCommonDenseSource cW c k t ht
  have hec : e.hom ≫ c = cW :=
    closedIsoOfCommonDenseSource_hom_comp cW c k t ht
  have heγ : e.hom ≫ γ = ψ := by
    have H := congrArg (fun z ↦ z ≫ pullback.snd β φ) hec
    simpa only [c, cW, Category.assoc, pullback.lift_snd] using H
  have hea : e.hom ≫ a = j := by
    have H := congrArg (fun z ↦ z ≫ pullback.fst β φ) hec
    simpa only [c, cW, Category.assoc, pullback.lift_fst] using H
  have hψ : Blowup.AdmissibleSequence UV ψ := by
    have H := hγU.iso e
    rwa [heγ] at H
  exact ⟨Vn, γ, a, t, e, hγU, inferInstance, htγ, heγ, hea,
    comp_closedIsoOfCommonDenseSource_hom cW c k t ht, hψ⟩

end AlgebraicGeometry.Scheme.QuasiDomination
