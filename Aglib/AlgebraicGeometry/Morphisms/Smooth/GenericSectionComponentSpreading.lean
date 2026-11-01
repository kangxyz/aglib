/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module
public import Aglib.AlgebraicGeometry.Morphisms.Smooth.ConnectedComponentsAlongSection
public import Aglib.AlgebraicGeometry.Limits.Clopen
public import Aglib.AlgebraicGeometry.Spec.PrincipalBaseChangeLimit

/-! # Spreading the original generic section component

A clopen in the actual generic fibre descends to a clopen at one original
principal stage. Compatibility of the original section with the same limit
makes its entire image land in that clopen after a further principal stage.
No connectedness of the other fibres or relative connected-locus openness is
assumed or concluded.
-/

@[expose] public noncomputable section
open CategoryTheory CategoryTheory.Limits Opposite
open IsLocalization.PrincipalDiagram
open scoped nonZeroDivisors

namespace AlgebraicGeometry.Scheme
universe u

/-- Descend a clopen together with containment of an actual compatible family
of maps. Both the limit preimage and the stage containment are literal opens. -/
theorem exists_clopen_stage_containing_family
    {I : Type u} [Category.{u} I] [IsCofiltered I]
    (D E : I ⥤ Scheme.{u}) (cD : Cone D) (cE : Cone E)
    (hD : IsLimit cD) (hE : IsLimit cE)
    [∀ {i j} (a : i ⟶ j), IsAffineHom (D.map a)]
    [∀ {i j} (a : i ⟶ j), IsAffineHom (E.map a)]
    [∀ i, CompactSpace (D.obj i)] [∀ i, QuasiSeparatedSpace (D.obj i)]
    [∀ i, CompactSpace (E.obj i)] [∀ i, QuasiSeparatedSpace (E.obj i)]
    (a : ∀ i, D.obj i ⟶ E.obj i)
    (ha : ∀ {i j} (r : i ⟶ j), D.map r ≫ a j = a i ≫ E.map r)
    (aLimit : cD.pt ⟶ cE.pt)
    (hcone : ∀ i, cD.π.app i ≫ a i = aLimit ≫ cE.π.app i)
    (U : cE.pt.Opens) (hU : IsClosed (U : Set cE.pt))
    (hsection : aLimit ⁻¹ᵁ U = ⊤) :
    ∃ (i : I) (V : (E.obj i).Opens), IsClosed (V : Set (E.obj i)) ∧
      cE.π.app i ⁻¹ᵁ V = U ∧ a i ⁻¹ᵁ V = ⊤ := by
  obtain ⟨i, V, hV, hpre⟩ := exists_clopen_preimage_eq_of_isLimit E cE hE U hU
  have htop : cD.π.app i ⁻¹ᵁ (a i ⁻¹ᵁ V) = ⊤ := by
    rw [← Scheme.Hom.comp_preimage, hcone, Scheme.Hom.comp_preimage, hpre, hsection]
  obtain ⟨j, r, hr⟩ := AlgebraicGeometry.exists_map_eq_top D cD hD (a i ⁻¹ᵁ V) htop
  refine ⟨j, E.map r ⁻¹ᵁ V, hV.preimage (E.map r).continuous, ?_, ?_⟩
  · rw [← Scheme.Hom.comp_preimage, cE.w, hpre]
  · rw [← Scheme.Hom.comp_preimage, ← ha, Scheme.Hom.comp_preimage]
    exact hr

end AlgebraicGeometry.Scheme

namespace AlgebraicGeometry.Scheme.PrincipalNeighborhoodLimit
universe u
variable {R : Type u} [CommRing R] (M : Submonoid R)
  {X : Scheme.{u}} (p : X ⟶ Spec (.of R))
  (σ : Spec (.of R) ⟶ X) (hσ : σ ≫ p = 𝟙 _)

/-- The complete section construction at an arbitrary original base map. -/
def sectionBaseChange {T : Scheme.{u}} (b : T ⟶ Spec (.of R)) : T ⟶ pullback b p :=
  pullback.lift (𝟙 _) (b ≫ σ) (by simp only
    [Category.assoc, hσ, Category.comp_id, Category.id_comp])

/-- Naturality of the complete actual pullback section, before specialization. -/
lemma sectionBaseChange_naturality {T U : Scheme.{u}} (b : T ⟶ Spec (.of R))
    (c : U ⟶ Spec (.of R)) (r : T ⟶ U) (hr : r ≫ c = b) :
    r ≫ sectionBaseChange p σ hσ c = sectionBaseChange p σ hσ b ≫
      pullback.lift (pullback.fst b p ≫ r) (pullback.snd b p)
        (by rw [Category.assoc, hr, pullback.condition]) := by
  apply pullback.hom_ext
  · let m : pullback b p ⟶ pullback c p :=
      pullback.lift (pullback.fst b p ≫ r) (pullback.snd b p)
        (by rw [Category.assoc, hr, pullback.condition])
    have hc : sectionBaseChange p σ hσ c ≫ pullback.fst c p = 𝟙 _ :=
      pullback.lift_fst _ _ _
    have hb : sectionBaseChange p σ hσ b ≫ pullback.fst b p = 𝟙 _ :=
      pullback.lift_fst _ _ _
    have hm : m ≫ pullback.fst c p = pullback.fst b p ≫ r :=
      pullback.lift_fst _ _ _
    have hl : (r ≫ sectionBaseChange p σ hσ c) ≫ pullback.fst c p = r :=
      (Category.assoc _ _ _).trans ((congrArg (fun t => r ≫ t) hc).trans
        (Category.comp_id _))
    have hh : (sectionBaseChange p σ hσ b ≫ m) ≫ pullback.fst c p = r :=
      (Category.assoc _ _ _).trans
        ((congrArg (fun t => sectionBaseChange p σ hσ b ≫ t) hm).trans
          ((Category.assoc _ _ _).symm.trans
            ((congrArg (fun t => t ≫ r) hb).trans (Category.id_comp _))))
    exact hl.trans hh.symm
  · simpa only [Category.assoc, sectionBaseChange, pullback.lift_snd,
      pullback.lift_snd_assoc] using congrArg (fun t => t ≫ σ) hr

/-- The original two projection equations identify the section on a cone. -/
lemma sectionBaseChange_projection {T U : Scheme.{u}} (b : T ⟶ Spec (.of R))
    (c : U ⟶ Spec (.of R)) (r : U ⟶ T) (hr : r ≫ b = c)
    (q : pullback p c ⟶ pullback b p)
    (hq₁ : q ≫ pullback.fst b p = pullback.snd p c ≫ r)
    (hq₂ : q ≫ pullback.snd b p = pullback.fst p c)
    (o : U ⟶ pullback p c)
    (ho₁ : o ≫ pullback.fst p c = c ≫ σ)
    (ho₂ : o ≫ pullback.snd p c = 𝟙 _) :
    r ≫ sectionBaseChange p σ hσ b = o ≫ q := by
  apply pullback.hom_ext
  · simp only [Category.assoc, sectionBaseChange, pullback.lift_fst, Category.comp_id,
      hq₁, ← Category.assoc o, ho₂, Category.id_comp]
  · simp only [Category.assoc, sectionBaseChange, pullback.lift_snd, hq₂, ho₁]
    exact (Category.assoc _ _ _).symm.trans (congrArg (fun t => t ≫ σ) hr)

/-- The original section at an original principal stage. -/
def principalSection (s : (Finset M)ᵒᵖ) :
    (specDiagram M).obj s ⟶ (baseChangeDiagram M p).obj s :=
  sectionBaseChange p σ hσ (Spec.algebraMap R (stage M s.unop))

@[reassoc]
lemma principalSection_fst (s : (Finset M)ᵒᵖ) :
    principalSection M p σ hσ s ≫
      pullback.fst (Spec.algebraMap R (stage M s.unop)) p = 𝟙 _ :=
  pullback.lift_fst _ _ _

@[reassoc]
lemma principalSection_snd (s : (Finset M)ᵒᵖ) :
    principalSection M p σ hσ s ≫ ((schemeDiagram M p).obj s).hom =
      (baseStructure M).app s ≫ σ := pullback.lift_snd _ _ _

/-- Naturality uses the unchanged base and base-change diagrams. -/
lemma principalSection_naturality {s t : (Finset M)ᵒᵖ} (r : s ⟶ t) :
    (specDiagram M).map r ≫ principalSection M p σ hσ t =
      principalSection M p σ hσ s ≫ (baseChangeDiagram M p).map r := by
  have hb : (specDiagram M).map r ≫ (baseStructure M).app t = (baseStructure M).app s :=
    ((baseStructure M).naturality r).trans (Category.comp_id _)
  exact sectionBaseChange_naturality p σ hσ
    ((baseStructure M).app s) ((baseStructure M).app t) ((specDiagram M).map r) hb

variable (K : Type u) [CommRing K] [Algebra R K] [IsLocalization M K]

/-- The original localization pullback has its original section, in its
standard pullback order. -/
def localizationSection : Spec (.of K) ⟶ pullback p (Spec.algebraMap R K) :=
  pullback.lift (Spec.algebraMap R K ≫ σ) (𝟙 _) (by
    rw [Category.assoc, hσ, Category.comp_id, Category.id_comp])

/-- Original section compatibility with every original cone projection. -/
lemma localizationSection_projection (s : (Finset M)ᵒᵖ) :
    (specCone M K).π.app s ≫ principalSection M p σ hσ s =
      localizationSection p σ hσ K ≫ baseChangeProjection M K p s := by
  exact sectionBaseChange_projection p σ hσ
    ((baseStructure M).app s) (Spec.algebraMap R K) ((specCone M K).π.app s)
    (baseStructure_fac M K s) (baseChangeProjection M K p s)
    (baseChangeProjection_field M K p s.unop) (baseChangeProjection_base M K p s)
    (localizationSection p σ hσ K) (pullback.lift_fst _ _ _) (pullback.lift_snd _ _ _)

/-- Original localization clopens and the original section descend together
without a descent certificate or a connected-fibre assumption. -/
theorem exists_principal_clopen_containing_section [CompactSpace X] [QuasiSeparatedSpace X]
    (U : (pullback p (Spec.algebraMap R K)).Opens)
    (hU : IsClosed (U : Set (pullback p (Spec.algebraMap R K) : Scheme.{u})))
    (hsection : localizationSection p σ hσ K ⁻¹ᵁ U = ⊤) :
    ∃ (s : Finset M) (V : ((baseChangeDiagram M p).obj (op s)).Opens),
      IsClosed (V : Set ((baseChangeDiagram M p).obj (op s))) ∧
      baseChangeProjection M K p (op s) ⁻¹ᵁ V = U ∧
      principalSection M p σ hσ (op s) ⁻¹ᵁ V = ⊤ := by
  have (i : (Finset M)ᵒᵖ) : CompactSpace ((specDiagram M).obj i) := by
    change CompactSpace (Spec _)
    infer_instance
  have (i : (Finset M)ᵒᵖ) : QuasiSeparatedSpace ((specDiagram M).obj i) := by
    change QuasiSeparatedSpace (Spec _)
    infer_instance
  obtain ⟨s, V, hV, he, hs⟩ := exists_clopen_stage_containing_family
    (specDiagram M) (baseChangeDiagram M p) (specCone M K) (baseChangeCone M K p)
    (specConeIsLimit M K) (baseChangeConeIsLimit M K p)
    (principalSection M p σ hσ) (principalSection_naturality M p σ hσ)
    (localizationSection p σ hσ K) (localizationSection_projection M p σ hσ K)
    U hU hsection
  exact ⟨s.unop, V, hV, he, hs⟩

end AlgebraicGeometry.Scheme.PrincipalNeighborhoodLimit

namespace AlgebraicGeometry.Scheme.PrincipalNeighborhoodLimit
universe u
variable {R : Type u} [CommRing R] [IsDomain R]
  (K : Type u) [Field K] [Algebra R K] [IsFractionRing R K]
  {X : Scheme.{u}} (p : X ⟶ Spec (.of R)) [Smooth p]
  [CompactSpace X] [QuasiSeparatedSpace X]
  (σ : Spec (.of R) ⟶ X) (hσ : σ ≫ p = 𝟙 _)

/-- The actual generic section component spreads to a genuine clopen over a
nonzero original principal denominator, and the original section lifts into it.
The other fibres are not asserted connected. -/
theorem exists_principal_genericSectionComponent :
    ∃ (s : Finset R⁰) (V : ((baseChangeDiagram R⁰ p).obj (op s)).Opens),
      denominator R⁰ s ≠ 0 ∧
      IsClosed (V : Set ((baseChangeDiagram R⁰ p).obj (op s))) ∧
      baseChangeProjection R⁰ K p (op s) ⁻¹ᵁ V =
        SmoothSectionComponent.componentOpen (pullback.snd p (Spec.algebraMap R K))
          (localizationSection p σ hσ K) ∧
      ∃ τ : Spec (.of (stage R⁰ s)) ⟶ V.toScheme,
        τ ≫ V.ι = principalSection R⁰ p σ hσ (op s) ∧
        τ ≫ V.ι ≫ pullback.fst (Spec.algebraMap R (stage R⁰ s)) p = 𝟙 _ := by
  let q := pullback.snd p (Spec.algebraMap R K)
  let o := localizationSection p σ hσ K
  let U := SmoothSectionComponent.componentOpen q o
  have hU : IsClosed (U : Set (pullback p (Spec.algebraMap R K) : Scheme.{u})) :=
    SmoothSectionComponent.componentOpen_isClosed q o
  have ho : o ⁻¹ᵁ U = ⊤ := by
    apply top_unique
    intro x _
    change o x ∈ U
    have hx : x = IsLocalRing.closedPoint K := Subsingleton.elim _ _
    rw [hx]
    exact SmoothSectionComponent.mem_componentOpen q o
  obtain ⟨s, V, hV, he, hs⟩ :=
    exists_principal_clopen_containing_section R⁰ p σ hσ K U hU ho
  have hrange : Set.range (principalSection R⁰ p σ hσ (op s)) ⊆ Set.range V.ι := by
    rw [Opens.range_ι]
    rintro _ ⟨x, rfl⟩
    change x ∈ principalSection R⁰ p σ hσ (op s) ⁻¹ᵁ V
    rw [hs]
    trivial
  let τ := IsOpenImmersion.lift V.ι (principalSection R⁰ p σ hσ (op s)) hrange
  have hτ : τ ≫ V.ι = principalSection R⁰ p σ hσ (op s) :=
    IsOpenImmersion.lift_fac _ _ _
  refine ⟨s, V, nonZeroDivisors.ne_zero (denominator_mem R⁰ s), hV, he, τ, hτ, ?_⟩
  exact (Category.assoc _ _ _).symm.trans
    ((congrArg (fun a => a ≫ pullback.fst (Spec.algebraMap R (stage R⁰ s)) p) hτ).trans
      (principalSection_fst R⁰ p σ hσ (op s)))

end AlgebraicGeometry.Scheme.PrincipalNeighborhoodLimit
