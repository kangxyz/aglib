/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.RationalMap.QuasiDomination.Uniqueness
public import Aglib.AlgebraicGeometry.RationalMap.QuasiDomination.GraphPullback
public import Aglib.AlgebraicGeometry.Limits.Range
public import Mathlib.AlgebraicGeometry.Noetherian
public import Mathlib.AlgebraicGeometry.PullbackCarrier

/-!
# Common domains on the original product image

Closed partial graphs pulled back to a common schematically dense ambient
source have identical open domains. Schematic density is used only on that
common ambient scheme, not on the individual original models.
-/

@[expose] public noncomputable section
set_option autoImplicit false
open CategoryTheory Limits TopologicalSpace
universe u v

namespace AlgebraicGeometry.Scheme.Compactification

private theorem closedGraph_baseChange_over
    {Y M X S : Scheme.{u}} (pY : Y ⟶ S) (pM : M ⟶ S) (pX : X ⟶ S)
    (π : M ⟶ Y) (hπ : π ≫ pY = pM)
    (V : Y.Opens) (q : V.toScheme ⟶ X) (hq : V.ι ≫ pY = q ≫ pX)
    [IsClosedImmersion (pullback.lift V.ι q hq)]
    (hw : pullback.snd V.ι π ≫ pM = (pullback.fst V.ι π ≫ q) ≫ pX) :
    IsClosedImmersion (pullback.lift (pullback.snd V.ι π)
      (pullback.fst V.ι π ≫ q) hw) := by
  subst pM
  exact QuasiDomination.baseChangeGraph_isClosedImmersion V.ι q pY pX hq π

private theorem pulled_closedGraph
    {Y M X S T : Scheme.{u}} [IsNoetherian M]
    (pY : Y ⟶ S) (pM : M ⟶ S) (pX : X ⟶ S)
    (π : M ⟶ Y) (hπ : π ≫ pY = pM)
    (V : Y.Opens) (q : V.toScheme ⟶ X) (hq : V.ι ≫ pY = q ≫ pX)
    [IsClosedImmersion (pullback.lift V.ι q hq)]
    (j : T ⟶ M) [IsSchemeTheoreticallyDominant j]
    (g : T ⟶ X) (a : T ⟶ V.toScheme)
    (ha : a ≫ V.ι = j ≫ π) (_hag : a ≫ q = g) :
    ∃ hw : pullback.snd V.ι π ≫ pM = (pullback.fst V.ι π ≫ q) ≫ pX,
      IsSchemeTheoreticallyDominant (pullback.lift a j ha) ∧
      IsClosedImmersion (pullback.lift (pullback.snd V.ι π)
        (pullback.fst V.ι π ≫ q) hw) := by
  let D := pullback V.ι π
  let d : D ⟶ M := pullback.snd V.ι π
  let h : D ⟶ X := pullback.fst V.ι π ≫ q
  let t : T ⟶ D := pullback.lift a j ha
  let : IsOpenImmersion d := show IsOpenImmersion (pullback.snd V.ι π) from inferInstance
  let : NoetherianSpace D := d.isOpenEmbedding.isEmbedding.isInducing.noetherianSpace
  have htd : t ≫ d = j := pullback.lift_snd _ _ _
  let : IsSchemeTheoreticallyDominant (t ≫ d) := by rw [htd]; infer_instance
  let : IsSchemeTheoreticallyDominant t :=
    IsSchemeTheoreticallyDominant.of_comp_left_of_isOpenImmersion t d
  have hw : d ≫ pM = h ≫ pX := by
    rw [← hπ]
    change pullback.snd V.ι π ≫ π ≫ pY = (pullback.fst V.ι π ≫ q) ≫ pX
    rw [← pullback.condition_assoc, hq, Category.assoc]
  have hc : IsClosedImmersion (pullback.lift d h hw) :=
    closedGraph_baseChange_over pY pM pX π hπ V q hq hw
  exact ⟨hw, inferInstance, hc⟩

/-- Actual pullback domains are canonically isomorphic, preserving both
projections and the original common source. -/
theorem exists_pullback_domainIso_of_common_closedGraphs
    {M X S T : Scheme.{u}} [IsNoetherian M] {ι : Type v}
    {Y : ι → Scheme.{u}} (pY : ∀ i, Y i ⟶ S)
    (pM : M ⟶ S) (pX : X ⟶ S)
    (π : ∀ i, M ⟶ Y i) (hπ : ∀ i, π i ≫ pY i = pM)
    (V : ∀ i, (Y i).Opens) (q : ∀ i, (V i).toScheme ⟶ X)
    (hq : ∀ i, (V i).ι ≫ pY i = q i ≫ pX)
    [∀ i, IsClosedImmersion (pullback.lift (V i).ι (q i) (hq i))]
    (j : T ⟶ M) [IsSchemeTheoreticallyDominant j] (g : T ⟶ X)
    (a : ∀ i, T ⟶ (V i).toScheme)
    (ha : ∀ i, a i ≫ (V i).ι = j ≫ π i)
    (hag : ∀ i, a i ≫ q i = g) (i k : ι) :
    ∃ e : pullback (V i).ι (π i) ≅ pullback (V k).ι (π k),
      e.hom ≫ pullback.snd (V k).ι (π k) = pullback.snd (V i).ι (π i) ∧
      e.hom ≫ pullback.fst (V k).ι (π k) ≫ q k =
        pullback.fst (V i).ι (π i) ≫ q i ∧
      pullback.lift (a i) j (ha i) ≫ e.hom = pullback.lift (a k) j (ha k) := by
  obtain ⟨w₁, ht₁, hc₁⟩ :=
    pulled_closedGraph (pY i) pM pX (π i) (hπ i) (V i) (q i) (hq i)
      j g (a i) (ha i) (hag i)
  obtain ⟨w₂, ht₂, hc₂⟩ :=
    pulled_closedGraph (pY k) pM pX (π k) (hπ k) (V k) (q k) (hq k)
      j g (a k) (ha k) (hag k)
  let t₁ := pullback.lift (a i) j (ha i)
  let t₂ := pullback.lift (a k) j (ha k)
  let : IsSchemeTheoreticallyDominant t₁ := ht₁
  let : IsSchemeTheoreticallyDominant t₂ := ht₂
  let : IsClosedImmersion (pullback.lift (pullback.snd (V i).ι (π i))
    (pullback.fst (V i).ι (π i) ≫ q i) w₁) := hc₁
  let : IsClosedImmersion (pullback.lift (pullback.snd (V k).ι (π k))
    (pullback.fst (V k).ι (π k) ≫ q k) w₂) := hc₂
  exact QuasiDomination.exists_domainIso_of_common_schematicallyDense_source
    (pullback.snd (V i).ι (π i)) (pullback.snd (V k).ι (π k))
    (pullback.fst (V i).ι (π i) ≫ q i) (pullback.fst (V k).ι (π k) ≫ q k)
    pM pX w₁ w₂ t₁ t₂
    ((pullback.lift_snd (a i) j (ha i)).trans
      (pullback.lift_snd (a k) j (ha k)).symm)
    (by simp only [t₁, t₂, pullback.lift_fst_assoc, hag])

/-- In particular, all actual inverse-image open domains agree. -/
theorem preimage_open_eq_of_common_closedGraphs
    {M X S T : Scheme.{u}} [IsNoetherian M] {ι : Type v}
    {Y : ι → Scheme.{u}} (pY : ∀ i, Y i ⟶ S)
    (pM : M ⟶ S) (pX : X ⟶ S)
    (π : ∀ i, M ⟶ Y i) (hπ : ∀ i, π i ≫ pY i = pM)
    (V : ∀ i, (Y i).Opens) (q : ∀ i, (V i).toScheme ⟶ X)
    (hq : ∀ i, (V i).ι ≫ pY i = q i ≫ pX)
    [∀ i, IsClosedImmersion (pullback.lift (V i).ι (q i) (hq i))]
    (j : T ⟶ M) [IsSchemeTheoreticallyDominant j] (g : T ⟶ X)
    (a : ∀ i, T ⟶ (V i).toScheme)
    (ha : ∀ i, a i ≫ (V i).ι = j ≫ π i)
    (hag : ∀ i, a i ≫ q i = g) (i k : ι) :
    π i ⁻¹ᵁ V i = π k ⁻¹ᵁ V k := by
  obtain ⟨e, he, _, _⟩ := exists_pullback_domainIso_of_common_closedGraphs
    pY pM pX π hπ V q hq j g a ha hag i k
  apply SetLike.coe_injective
  have hr : Set.range (pullback.snd (V i).ι (π i)) =
      Set.range (pullback.snd (V k).ι (π k)) :=
    (congrArg (fun f : pullback (V i).ι (π i) ⟶ M => Set.range f) he.symm).trans
      (Hom.Range.range_iso_comp e (pullback.snd (V k).ι (π k)))
  change π i ⁻¹' (V i : Set (Y i)) = π k ⁻¹' (V k : Set (Y k))
  simpa only [Scheme.Pullback.range_snd, Opens.range_ι] using hr

end AlgebraicGeometry.Scheme.Compactification
