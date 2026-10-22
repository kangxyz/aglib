/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.RationalMap.QuasiDomination.GraphPullback
public import Aglib.AlgebraicGeometry.Morphisms.IsIso.OpenHomExt
public import Mathlib.AlgebraicGeometry.Morphisms.Immersion

/-!
# Transporting a target-chart graph to a common refinement

The literal domain pullback carries a closed graph in the target-open product.
The original protected graph factors through it using the protected base
isomorphism. No flatness or schematic-density claim about comparisons is used.
-/

@[expose] public noncomputable section

open CategoryTheory Limits

universe u

namespace AlgebraicGeometry.Scheme.QuasiDomination

/-- A closed graph on one target chart remains closed on the actual pulled
back domain, and contains the restriction of the original protected graph. -/
theorem exists_pulled_targetOpen_graph
    {X Y B Bi D : Scheme.{u}} (U : X.Opens) (f : Y ⟶ X)
    (g : U.toScheme ⟶ Y) (_hg : g ≫ f = U.ι) (O : Y.Opens)
    (βi : Bi ⟶ X) (β : B ⟶ X) (a : B ⟶ Bi) (ha : a ≫ βi = β)
    [IsIso (βi ∣_ U)] (d : D ⟶ Bi) [IsImmersion d]
    (h : D ⟶ O.toScheme) (k : (g ⁻¹ᵁ O).toScheme ⟶ D)
    (hw : d ≫ βi = h ≫ (O.ι ≫ f))
    (hk : k ≫ d ≫ βi = (g ⁻¹ᵁ O).ι ≫ U.ι)
    (hkh : k ≫ h = g ∣_ O) [IsClosedImmersion (pullback.lift d h hw)]
    (γ : (β ⁻¹ᵁ U).toScheme ⟶ pullback β f)
    (hγfst : γ ≫ pullback.fst β f = (β ⁻¹ᵁ U).ι)
    (hγsnd : γ ≫ pullback.snd β f = (β ∣_ U) ≫ g) :
    ∃ c : pullback d a ⟶ ((pullback.snd β f) ⁻¹ᵁ O).toScheme,
      IsClosedImmersion c ∧
      Function.Injective (c ≫ ((pullback.snd β f) ⁻¹ᵁ O).ι ≫ pullback.fst β f) ∧
      Set.range (γ ∣_ ((pullback.snd β f) ⁻¹ᵁ O)) ⊆ Set.range c := by
  subst β
  let p := a ≫ βi
  let Q := (pullback.snd p f) ⁻¹ᵁ O
  let E : pullback p (O.ι ≫ f) ≅ Q.toScheme :=
    (pullbackLeftPullbackSndIso p f O.ι).symm ≪≫
      pullbackRestrictIsoRestrict (pullback.snd p f) O
  let c := baseChangeGraph d h βi (O.ι ≫ f) hw a ≫ E.hom
  have hc₁ : c ≫ Q.ι ≫ pullback.fst p f = pullback.snd d a := by
    dsimp only [c, E, Iso.trans_hom, Iso.symm_hom, Q]
    rw [Category.assoc, Category.assoc, pullbackRestrictIsoRestrict_hom_ι_assoc,
      pullbackLeftPullbackSndIso_inv_fst, baseChangeGraph_fst]
  have hc₂ : c ≫ Q.ι ≫ pullback.snd p f = pullback.fst d a ≫ h ≫ O.ι := by
    dsimp only [c, E, Iso.trans_hom, Iso.symm_hom, Q]
    rw [Category.assoc, Category.assoc, pullbackRestrictIsoRestrict_hom_ι_assoc,
      pullbackLeftPullbackSndIso_inv_fst_snd, ← Category.assoc, baseChangeGraph_snd];
      simp only [Category.assoc]
  let L := γ ⁻¹ᵁ Q
  let t : L.toScheme ⟶ U.toScheme := L.ι ≫ (p ∣_ U)
  let H := isPullback_morphismRestrict g O
  have ht : ((γ ∣_ Q) ≫ (pullback.snd p f ∣_ O)) ≫ O.ι = t ≫ g := by
    rw [Category.assoc, morphismRestrict_ι, ← Category.assoc,
      morphismRestrict_ι, Category.assoc, hγsnd]
    rfl
  let l := H.lift ((γ ∣_ Q) ≫ (pullback.snd p f ∣_ O)) t ht
  have hl : l ≫ (g ⁻¹ᵁ O).ι = t := H.lift_snd _ _ _
  have hkbase : (l ≫ k ≫ d) ≫ βi = t ≫ U.ι := by
    rw [Category.assoc, Category.assoc, hk, ← Category.assoc, hl]
  have habase : (L.ι ≫ (p ⁻¹ᵁ U).ι ≫ a) ≫ βi = t ≫ U.ι := by
    simpa only [t, p, Category.assoc] using
      (congrArg (fun z => L.ι ≫ z) (morphismRestrict_ι p U)).symm
  have he := Hom.ext_of_isIso_restriction βi U t
    (l ≫ k ≫ d) (L.ι ≫ (p ⁻¹ᵁ U).ι ≫ a) hkbase habase
  let m : L.toScheme ⟶ pullback d a :=
    pullback.lift (l ≫ k) (L.ι ≫ (p ⁻¹ᵁ U).ι) (by
      simpa only [Category.assoc] using he)
  have hm : m ≫ c = γ ∣_ Q := by
    apply (cancel_mono Q.ι).mp
    apply pullback.hom_ext
    · rw [Category.assoc, Category.assoc, hc₁, pullback.lift_snd]
      simpa only [p, Category.assoc, hγfst] using
        (congrArg (fun z => z ≫ pullback.fst p f) (morphismRestrict_ι γ Q)).symm
    · rw [Category.assoc, Category.assoc, hc₂, ← Category.assoc,
        pullback.lift_fst, Category.assoc, Category.assoc]
      calc
        l ≫ k ≫ h ≫ O.ι = l ≫ (g ∣_ O) ≫ O.ι := by
          rw [← Category.assoc k h O.ι, hkh]
        _ = t ≫ g := by rw [morphismRestrict_ι, ← Category.assoc, hl]
        _ = (γ ∣_ Q) ≫ Q.ι ≫ pullback.snd p f := by
          simpa only [t, p, Category.assoc, hγsnd] using
            (congrArg (fun z => z ≫ pullback.snd p f) (morphismRestrict_ι γ Q)).symm
  refine ⟨c, inferInstance, ?_, ?_⟩
  · rw [hc₁]
    exact (pullback.snd d a).isEmbedding.injective
  · rintro _ ⟨x, rfl⟩
    exact ⟨m x, congrArg (fun z => z x) hm⟩

end AlgebraicGeometry.Scheme.QuasiDomination
