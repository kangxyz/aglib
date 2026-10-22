/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.RationalMap.QuasiDomination.TargetOpen
public import Aglib.AlgebraicGeometry.RationalMap.QuasiDomination.RelativeTwoOpen
public import Aglib.AlgebraicGeometry.Blowup.AdmissibleSequence.ClosedExtension
public import Aglib.AlgebraicGeometry.QuasiAffine.AffineSource

/-!
# Admissible modification for one affine target chart

The restricted original source is replaced by its actual schematic image.
Relative two-open quasi-domination on that image extends to the original ambient
source by closed-centre extension. The resulting domain is immersed, not in
general open, in the modified ambient source. Its literal graph is closed.
-/

@[expose] public noncomputable section

open CategoryTheory Limits TopologicalSpace

universe u

namespace AlgebraicGeometry.Scheme.QuasiDomination

private theorem relative_of_factorization
    {X Y P S : Scheme.{u}} [IsNoetherian X]
    (U V : X.Opens) (hUV : U ≤ V) (hU : Dense (U : Set X))
    (p : X ⟶ S) (f : Y ⟶ S) (e : Y ⟶ P) (a : P ⟶ S)
    [IsImmersion e] [IsAffineHom a] [QuasiCompact f] [LocallyOfFiniteType f]
    (he : e ≫ a = f) (g : U.toScheme ⟶ Y) (hg : g ≫ f = U.ι ≫ p)
    (hc : IsClosed ((pullback.fst p f ⁻¹ᵁ V).ι ⁻¹'
      Set.range (pullback.lift U.ι g hg.symm))) :
    ∃ (Z : Scheme.{u}) (δ : Z ⟶ X) (D : Scheme.{u}) (d : D ⟶ Z)
      (h : D ⟶ Y) (k : U.toScheme ⟶ D) (hw : d ≫ δ ≫ p = h ≫ f),
      Blowup.AdmissibleSequence V δ ∧ IsOpenImmersion d ∧
      k ≫ d ≫ δ = U.ι ∧ k ≫ h = g ∧
      IsClosedImmersion (pullback.lift d h hw) := by
  subst f
  obtain ⟨Z, δ, D, d, h, k, hw, hs, _, _, hd, _, _, hk, hh, hc⟩ :=
    exists_relative_twoOpen_quasiDomination U V hUV hU p e a g hg hc
  exact ⟨Z, δ, D, d, h, k, hw, hs, hd, hk, hh, hc⟩

private lemma lift_congrHom {A B C Z : Scheme.{u}} {a a' : A ⟶ Z} {b b' : B ⟶ Z}
    (ha : a = a') (hb : b = b') (i : C ⟶ A) (k : C ⟶ B)
    (v : i ≫ a = k ≫ b) (v' : i ≫ a' = k ≫ b') :
    pullback.lift i k v' = pullback.lift i k v ≫ (pullback.congrHom ha hb).hom := by
  subst a'
  subst b'
  simp

/-- One affine target chart admits an ambient admissible modification and a
closed graph with immersed domain, preserving the actual original section. -/
theorem exists_targetOpen_modification
    {X Y : Scheme.{u}} [IsNoetherian X]
    (f : Y ⟶ X) [QuasiCompact f] [LocallyOfFiniteType f]
    (U V : X.Opens) (hUV : U ≤ V)
    (g : U.toScheme ⟶ Y) (hg : g ≫ f = U.ι)
    (hclosed : IsClosed ((pullback.fst (𝟙 X) f ⁻¹ᵁ V).ι ⁻¹'
      Set.range (pullback.lift U.ι g (by simpa using hg.symm))))
    (O : Y.Opens) (hO : IsAffineOpen O) :
    ∃ (B : Scheme.{u}) (β : B ⟶ X) (D : Scheme.{u}) (d : D ⟶ B)
      (h : D ⟶ O.toScheme) (k : (g ⁻¹ᵁ O).toScheme ⟶ D)
      (hw : d ≫ β = h ≫ (O.ι ≫ f)),
      Blowup.AdmissibleSequence V β ∧ IsImmersion d ∧
      k ≫ d ≫ β = (g ⁻¹ᵁ O).ι ≫ U.ι ∧ k ≫ h = g ∣_ O ∧
      IsClosedImmersion (pullback.lift d h hw) := by
  classical
  let : IsLocallyNoetherian Y := LocallyOfFiniteType.isLocallyNoetherian f
  let : IsAffine O.toScheme := hO
  let : CompactSpace U.toScheme := by
    change CompactSpace (U : Set X)
    infer_instance
  let : IsNoetherian U.toScheme := ⟨⟩
  let : CompactSpace (g ⁻¹ᵁ O).toScheme := by
    change CompactSpace ((g ⁻¹ᵁ O) : Set U.toScheme)
    infer_instance
  let : IsNoetherian (g ⁻¹ᵁ O).toScheme := ⟨⟩
  let jO : (g ⁻¹ᵁ O).toScheme ⟶ X := (g ⁻¹ᵁ O).ι ≫ U.ι
  let : IsOpenImmersion jO := inferInstance
  let : QuasiCompact jO := inferInstance
  let : IsLocallyNoetherian jO.image :=
    LocallyOfFiniteType.isLocallyNoetherian jO.imageι
  let : CompactSpace jO.image := QuasiCompact.compactSpace_of_compactSpace jO.imageι
  let : IsNoetherian jO.image := ⟨⟩
  let UI := jO.toImage.opensRange
  let VI := jO.imageι ⁻¹ᵁ V
  let E : (g ⁻¹ᵁ O).toScheme ≅ UI.toScheme := jO.toImage.isoOpensRange
  have hE : E.hom ≫ UI.ι = jO.toImage := Hom.isoOpensRange_hom_ι _
  have hUI : UI ≤ VI := by
    rintro x ⟨z, rfl⟩
    change jO.imageι (jO.toImage z) ∈ V
    have he := congrArg (fun k => k z) jO.toImage_imageι
    rw [← Hom.comp_apply, he]
    exact hUV z.1.property
  have hDense : Dense (UI : Set jO.image) := jO.toImage.denseRange
  let gI : UI.toScheme ⟶ O.toScheme := E.inv ≫ (g ∣_ O)
  let pI := jO.imageι ≫ 𝟙 X
  have hgO : (g ∣_ O) ≫ (O.ι ≫ f) = jO.toImage ≫ pI := by
    simp only [pI, Category.comp_id, Hom.toImage_imageι, ← Category.assoc,
      morphismRestrict_ι]
    exact congrArg (fun k => (g ⁻¹ᵁ O).ι ≫ k) hg
  have hEInv : E.inv ≫ jO.toImage = UI.ι := Hom.isoOpensRange_inv_comp _
  have hgI : gI ≫ (O.ι ≫ f) = UI.ι ≫ pI := by
    dsimp only [gI]
    rw [Category.assoc, hgO, ← Category.assoc, hEInv]
  let γI := pullback.lift UI.ι gI hgI.symm
  let γO := pullback.lift jO.toImage (g ∣_ O) hgO.symm
  have hγI : E.hom ≫ γI = γO := by
    apply pullback.hom_ext
    · simpa only [Category.assoc, γI, γO, pullback.lift_fst] using hE
    · simp only [Category.assoc, γI, γO, pullback.lift_snd, gI,
        Iso.hom_inv_id_assoc]
  have hclosedI : IsClosed ((pullback.fst pI (O.ι ≫ f) ⁻¹ᵁ VI).ι ⁻¹'
      Set.range γI) := by
    have H : IsClosed ((pullback.fst pI (O.ι ≫ f) ⁻¹ᵁ VI).ι ⁻¹'
        Set.range γO) := by
      exact
        isClosed_targetOpenImageGraph_over U.ι g O (𝟙 X) f
          (by simpa using hg.symm) V hclosed
    rw [← hγI, Hom.Range.range_iso_comp] at H
    exact H
  obtain ⟨P, e, a, he, ha, hfac⟩ :=
    exists_immersion_affine_factorization_of_isAffine (O.ι ≫ f)
  let : IsImmersion e := he
  let : IsAffineHom a := ha
  obtain ⟨Z, δ, D, d₀, h, k₀, hw₀, hseq, hd₀, hkbase, hkmap, hgraph⟩ :=
    relative_of_factorization UI VI hUI hDense pI (O.ι ≫ f) e a hfac gI hgI hclosedI
  obtain ⟨B, β, i, hβ, hi, htriangle⟩ :=
    hseq.exists_closed_extension jO.imageι V
  let : IsOpenImmersion d₀ := hd₀
  let : IsClosedImmersion i := hi
  let : IsClosedImmersion (pullback.lift d₀ h hw₀) := hgraph
  let d := d₀ ≫ i
  let k := E.hom ≫ k₀
  have hw : d ≫ β = h ≫ (O.ι ≫ f) := by
    dsimp only [d]
    rw [Category.assoc, htriangle]
    simpa only [pI, Category.comp_id] using hw₀
  have hk₁ : k ≫ d ≫ β = (g ⁻¹ᵁ O).ι ≫ U.ι := by
    dsimp only [k, d]
    simp only [Category.assoc, htriangle]
    rw [reassoc_of% hkbase]
    rw [← Category.assoc, hE, Hom.toImage_imageι]
  have hk₂ : k ≫ h = g ∣_ O := by
    simp [k, hkmap, gI]
  have htriangle' : δ ≫ pI = i ≫ β := by
    simpa only [pI, Category.comp_id] using htriangle.symm
  let L := pullback.congrHom htriangle' (rfl : (O.ι ≫ f) = (O.ι ≫ f))
  have hw₁ : d₀ ≫ (i ≫ β) = h ≫ (O.ι ≫ f) := by
    rw [← htriangle']
    exact hw₀
  let G := pullback.lift d₀ h hw₁
  have hG : G = pullback.lift d₀ h hw₀ ≫ L.hom :=
    lift_congrHom htriangle' rfl d₀ h hw₀ hw₁
  let : IsClosedImmersion G := by rw [hG]; infer_instance
  let m := productBaseChangeMap i β (O.ι ≫ f)
  let : IsClosedImmersion m := by
    dsimp only [m, productBaseChangeMap]
    infer_instance
  have hgraphEq : pullback.lift d h hw = G ≫ m := by
    apply pullback.hom_ext
    · simp only [Category.assoc, m, productBaseChangeMap_fst, G,
        pullback.lift_fst, pullback.lift_fst_assoc, d]
    · simp only [Category.assoc, m, productBaseChangeMap_snd, G, pullback.lift_snd]
  refine ⟨B, β, D, d, h, k, hw, hβ, inferInstance, hk₁, hk₂, ?_⟩
  rw [hgraphEq]
  infer_instance

end AlgebraicGeometry.Scheme.QuasiDomination
