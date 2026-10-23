/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.ProjectiveBundle.RankTwoExtension
public import Aglib.AlgebraicGeometry.Modules.StructureSheaf.Hom
public import Mathlib.RingTheory.Polynomial.Ideal
public import Mathlib.AlgebraicGeometry.PullbackCarrier

/-!
# The actual complement of the quotient section

The complement of the original infinity section is its original affine chart
zero over every commutative ring. The corresponding open in the constructed
extension bundle is affine over the original base. All local maps retain the
original chart inclusions and projection triangles.
-/

@[expose] public noncomputable section

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Opposite TopologicalSpace
open Scheme.Modules Scheme.ProjectiveLine Polynomial
open scoped Polynomial

universe u

namespace AlgebraicGeometry.Scheme.ProjectiveLine.Sections

variable (R : Type u) [CommRing R]

/-- The actual infinity section is disjoint from the original chart zero. -/
theorem infinity_not_mem_chart_zero (x : Spec (.of R)) :
    infinity R x ∉ (chart R 0).opensRange := by
  change x ∉ infinity R ⁻¹ᵁ (chart R 0).opensRange
  rw [infinity, chartSection, Scheme.Hom.comp_preimage, chart_opensRange,
    chart_preimage_linear R 1 _ (MvPolynomial.isHomogeneous_X R (0 : Fin 2))]
  simp only [dehomogenizePolynomial, MvPolynomial.eval₂Hom_X',
    show (0 : Fin 2) ≠ 1 by decide, ite_false]
  change ¬¬((Polynomial.evalRingHom (0 : R)) Polynomial.X ∈ x.asIdeal)
  simp

/-- The actual infinity image is exactly the complement of the original chart zero. -/
theorem infinity_range : Set.range (infinity R) = ((chart R 0).opensRange : Set _)ᶜ := by
  ext z
  constructor
  · rintro ⟨x, rfl⟩
    exact infinity_not_mem_chart_zero R x
  · intro hz
    obtain ⟨j, y, rfl⟩ := chart_covered R z
    fin_cases j
    · exact False.elim (hz ⟨y, rfl⟩)
    · have hy : (Polynomial.X : R[X]) ∈ y.asIdeal := by
        change y ∉ chart R 1 ⁻¹ᵁ (chart R 0).opensRange at hz
        rw [chart_opensRange,
          chart_preimage_linear R 1 _ (MvPolynomial.isHomogeneous_X R (0 : Fin 2))] at hz
        simp only [dehomogenizePolynomial, MvPolynomial.eval₂Hom_X',
          show (0 : Fin 2) ≠ 1 by decide, ite_false] at hz
        exact not_not.mp hz
      have hyker : y ∈ PrimeSpectrum.zeroLocus (RingHom.ker (Polynomial.evalRingHom (0 : R))) := by
        change RingHom.ker (Polynomial.evalRingHom (0 : R)) ≤ y.asIdeal
        rw [Polynomial.ker_evalRingHom, Polynomial.C_0, sub_zero]
        exact Ideal.span_le.mpr (Set.singleton_subset_iff.mpr hy)
      rw [← range_comap_of_surjective R (Polynomial.evalRingHom (0 : R))
        (fun r : R => ⟨Polynomial.C r, Polynomial.eval_C⟩)] at hyker
      obtain ⟨x, hx⟩ := hyker
      exact ⟨x, congrArg (chart R 1) hx⟩

/-- The literal affine section is disjoint from the literal infinity section. -/
theorem affinePoint_disjoint_infinity (a : R) :
    Disjoint (Set.range (affinePoint R a)) (Set.range (infinity R)) := by
  rw [Set.disjoint_left]
  rintro _ ⟨x, rfl⟩ ⟨y, hy⟩
  apply infinity_not_mem_chart_zero R y
  rw [hy]
  exact ⟨Spec.map (CommRingCat.ofHom (Polynomial.evalRingHom a)) x, rfl⟩

end AlgebraicGeometry.Scheme.ProjectiveLine.Sections

namespace AlgebraicGeometry.Scheme.ProjectiveBundle.RankTwoExtension

variable {X : Scheme.{u}} {E : X.Modules}
variable (i : (SheafOfModules.unit X.ringCatSheaf : X.Modules) ⟶ E)
  (g : E ⟶ (SheafOfModules.unit X.ringCatSheaf : X.Modules))
  (hig : i ≫ g = 0) (hS : (extensionComplex i g hig).ShortExact)

/-- The open complement of the image of the actual quotient section. -/
def quotientComplement : (projectiveBundle i g hig hS).Opens :=
  ⟨(Set.range (quotientSection i g hig hS))ᶜ,
    (IsClosedImmersion.isClosedEmbedding (quotientSection i g hig hS)).isClosed_range.isOpen_compl⟩

/-- The projection of the actual complement to the original base. -/
def complementProjection : (quotientComplement i g hig hS).toScheme ⟶ X :=
  (quotientComplement i g hig hS).ι ≫ projection i g hig hS

private theorem chart_preimage_quotient_range (a : AffineFrame g) :
    (chartInclusion i g hig hS a) ⁻¹' Set.range (quotientSection i g hig hS) =
      Set.range (Sections.infinity Γ(X, a.U.1)) := by
  ext z
  constructor
  · rintro ⟨x, hx⟩
    obtain ⟨y, hy, hz⟩ := exists_preimage_of_isPullback
      (quotientSection_chart_isPullback i g hig hS a) x z hx
    exact ⟨a.isoSpec.hom y, hz⟩
  · rintro ⟨y, rfl⟩
    refine ⟨a.U.1.ι (a.isoSpec.inv y), ?_⟩
    have h := congrArg
      (fun f : a.U.1.toScheme ⟶ projectiveBundle i g hig hS => a.isoSpec.inv ≫ f)
      (quotientSection_chart i g hig hS a)
    simp only [localQuotientSection, Category.assoc, Iso.inv_hom_id_assoc] at h
    exact congrArg (fun f : Spec Γ(X, a.U.1) ⟶ projectiveBundle i g hig hS => f y) h

/-- The original frame chart meets the actual complement in its original affine chart zero. -/
theorem chart_preimage_quotientComplement (a : AffineFrame g) :
    chartInclusion i g hig hS a ⁻¹ᵁ quotientComplement i g hig hS =
      (chart Γ(X, a.U.1) 0).opensRange := by
  apply Opens.ext
  change (chartInclusion i g hig hS a) ⁻¹' (Set.range (quotientSection i g hig hS))ᶜ = _
  rw [Set.preimage_compl, chart_preimage_quotient_range, Sections.infinity_range,
    compl_compl]

/-- The original affine chart zero lands in the actual complement. -/
def complementChart (a : AffineFrame g) :
    Spec (.of (Polynomial (Γ(X, a.U.1)))) ⟶ (quotientComplement i g hig hS).toScheme :=
  IsOpenImmersion.lift (quotientComplement i g hig hS).ι
    (chart Γ(X, a.U.1) 0 ≫ chartInclusion i g hig hS a) (by
      rintro _ ⟨z, rfl⟩
      rw [Scheme.Opens.range_ι]
      change chart Γ(X, a.U.1) 0 z ∈
        chartInclusion i g hig hS a ⁻¹ᵁ quotientComplement i g hig hS
      rw [chart_preimage_quotientComplement]
      exact ⟨z, rfl⟩)

@[reassoc] theorem complementChart_ι (a : AffineFrame g) :
    complementChart i g hig hS a ≫ (quotientComplement i g hig hS).ι =
      chart Γ(X, a.U.1) 0 ≫ chartInclusion i g hig hS a :=
  IsOpenImmersion.lift_fac _ _ _

instance complementChart_isOpenImmersion (a : AffineFrame g) :
    IsOpenImmersion (complementChart i g hig hS a) := by
  unfold complementChart
  infer_instance

/-- The actual affine complement chart has the original coefficient projection triangle. -/
@[reassoc] theorem complementChart_projection (a : AffineFrame g) :
    complementChart i g hig hS a ≫ complementProjection i g hig hS =
      Spec.map (CommRingCat.ofHom (Polynomial.C : Γ(X, a.U.1) →+* Polynomial (Γ(X, a.U.1)))) ≫
        a.isoSpec.inv ≫ a.U.1.ι := by
  rw [complementProjection, ← Category.assoc, complementChart_ι, Category.assoc,
    chartInclusion_projection]
  simp only [chartProjection, Category.assoc, chart_over_assoc, Polynomial.algebraMap_eq]

/-- The original complement chart is precisely the inverse image of its original base open. -/
theorem complementChart_opensRange (a : AffineFrame g) :
    (complementChart i g hig hS a).opensRange =
      complementProjection i g hig hS ⁻¹ᵁ a.U.1 := by
  have hframe : projection i g hig hS ⁻¹ᵁ a.U.1 =
      (chartInclusion i g hig hS a).opensRange := by
    simpa using (IsOpenImmersion.image_preimage_eq_preimage_image_of_isPullback
      (chartInclusion_isPullback i g hig hS a).flip (⊤ : a.U.1.toScheme.Opens)).symm
  ext z
  constructor
  · rintro ⟨w, rfl⟩
    have h := congrArg (fun f => f w) (complementChart_projection i g hig hS a)
    change complementProjection i g hig hS (complementChart i g hig hS a w) ∈ a.U.1
    rw [← Scheme.Hom.comp_apply, h]
    exact (a.isoSpec.inv (Spec.map (CommRingCat.ofHom
      (Polynomial.C : Γ(X, a.U.1) →+* Polynomial (Γ(X, a.U.1)))) w)).property
  · intro hz
    have hp : (quotientComplement i g hig hS).ι z ∈
        (chartInclusion i g hig hS a).opensRange := by
      rw [← hframe]
      exact hz
    obtain ⟨p, hp⟩ := hp
    have hp0 : p ∈ (chart Γ(X, a.U.1) 0).opensRange := by
      rw [← chart_preimage_quotientComplement]
      change chartInclusion i g hig hS a p ∈ quotientComplement i g hig hS
      rw [hp]
      exact z.property
    obtain ⟨w, hw⟩ := hp0
    refine ⟨w, ?_⟩
    apply (quotientComplement i g hig hS).ι.injective
    have h := congrArg (fun f => f w) (complementChart_ι i g hig hS a)
    exact h.trans ((congrArg (chartInclusion i g hig hS a) hw).trans hp)

/-- The actual affine chart retains its cartesian square over the original base. -/
theorem complementChart_isPullback (a : AffineFrame g) :
    IsPullback (complementChart i g hig hS a)
      (Spec.map (CommRingCat.ofHom
        (Polynomial.C : Γ(X, a.U.1) →+* Polynomial (Γ(X, a.U.1)))) ≫ a.isoSpec.inv)
      (complementProjection i g hig hS) a.U.1.ι := by
  apply IsPullback.flip
  apply IsOpenImmersion.isPullback
  · simpa only [Category.assoc] using complementChart_projection i g hig hS a
  · simpa using (complementChart_opensRange i g hig hS a).symm

/-- The complement of the actual quotient section is affine over the original base. -/
instance complementProjection_isAffine : IsAffineHom (complementProjection i g hig hS) := by
  let : Epi g := hS.epi_g
  apply IsZariskiLocalAtTarget.of_openCover (P := @IsAffineHom) (frameCover g)
  intro a
  change AffineFrame g at a
  change IsAffineHom (pullback.snd (complementProjection i g hig hS) a.U.1.ι)
  let : IsAffine a.U.1.toScheme := a.U.2
  let : IsAffine (Limits.pullback (complementProjection i g hig hS) a.U.1.ι) :=
    IsAffine.of_isIso (complementChart_isPullback i g hig hS a).isoPullback.inv
  infer_instance


/-- The original affine quotient frames whose opens lie in the specified original open. -/
abbrev FrameOn (W : X.Opens) := {a : AffineFrame g // a.U.1 ≤ W}

/-- The same actual frames cover the specified open of the original base. -/
def frameCoverOn (W : X.Opens) [Epi g] : W.toScheme.OpenCover where
  I₀ := FrameOn g W
  X a := a.val.U.1.toScheme
  f a := X.homOfLE a.property
  mem₀ := by
    rw [presieve₀_mem_precoverage_iff]
    refine ⟨fun x => ?_, inferInstance⟩
    obtain ⟨a, hxa, haW⟩ := exists_frame_le g W x.val x.property
    refine ⟨⟨a, haW⟩, ⟨⟨x.val, hxa⟩, ?_⟩⟩
    apply Subtype.ext
    exact Scheme.homOfLE_apply (X := X) haW ⟨x.val, hxa⟩

instance (W : X.Opens) [Epi g] : Preorder (frameCoverOn g W).I₀ :=
  inferInstanceAs (Preorder (FrameOn g W))

instance (W : X.Opens) [Epi g] :
    (frameCoverOn g W).LocallyDirected := by
  apply Scheme.Cover.LocallyDirected.ofIsBasisOpensRange
  · intro a b
    change a.val.U.1 ≤ b.val.U.1 ↔ _
    simp only [frameCoverOn, Scheme.opensRange_homOfLE]
    constructor
    · intro h x hx
      exact h hx
    · intro h x hx
      exact h (show (⟨x, a.property hx⟩ : W.toScheme) ∈ W.ι ⁻¹ᵁ a.val.U.1 from hx)
  · rw [Opens.isBasis_iff_nbhd]
    intro V x hx
    obtain ⟨a, hxa, haV⟩ := exists_frame_le g (W.ι ''ᵁ V) x.val
      (show x.val ∈ W.ι ''ᵁ V from ⟨x, hx, rfl⟩)
    have haW : a.U.1 ≤ W := by
      intro y hy
      obtain ⟨z, hz, rfl⟩ := haV hy
      exact z.property
    refine ⟨W.ι ⁻¹ᵁ a.U.1, ⟨⟨a, haW⟩, ?_⟩, hxa, ?_⟩
    · simp only [frameCoverOn, Scheme.opensRange_homOfLE]
    · intro y hy
      obtain ⟨z, hz, hzy⟩ := haV hy
      have he : z = y := Subtype.ext hzy
      rwa [← he]

private theorem frameCoverOn_trans [Epi g] {W : X.Opens} {a b : FrameOn g W} (h : a ⟶ b) :
    (frameCoverOn g W).trans h = X.homOfLE (show a.val.U.1 ≤ b.val.U.1 from leOfHom h) := by
  apply (cancel_mono (X.homOfLE b.property)).mp
  exact ((frameCoverOn g W).trans_map h).trans
    (by simp only [frameCoverOn, Scheme.homOfLE_homOfLE])

variable {W : X.Opens}
  (r : E.over W ⟶ (SheafOfModules.unit X.ringCatSheaf).over W)
  (hr : (SheafOfModules.overFunctor X.ringCatSheaf W).map i ≫ r = 𝟙 _)

/-- The complementary parameter is the image of the original lift under the supplied retraction. -/
def complementaryParameter (a : FrameOn g W) : Γ(X, a.val.U.1) :=
  r.val.app (op (Over.mk (homOfLE a.property))) a.val.lift

include hr in
/-- The supplied original retraction and original transition equation determine parameter change. -/
theorem complementaryParameter_transition {a b : FrameOn g W} (h : a ≤ b) :
    scalarRestriction (show a.val.U.1 ≤ b.val.U.1 from h) (complementaryParameter g r b) =
      complementaryParameter g r a + transition i g hig hS (show a.val ≤ b.val from h) := by
  let q : Over.mk (homOfLE a.property) ⟶ Over.mk (homOfLE b.property) :=
    Over.homMk (homOfLE (show a.val.U.1 ≤ b.val.U.1 from h))
  have hn := PresheafOfModules.naturality_apply r.val q.op b.val.lift
  have hi := congrArg (fun f => f.val.app (op (Over.mk (homOfLE a.property)))
    (transition i g hig hS (show a.val ≤ b.val from h))) hr
  have ht := congrArg (r.val.app (op (Over.mk (homOfLE a.property))))
    (transition_spec i g hig hS (show a.val ≤ b.val from h))
  change r.val.app (op (Over.mk (homOfLE a.property)))
    (Scheme.Modules.Hom.app i a.val.U.1 (transition i g hig hS h)) =
      transition i g hig hS h at hi
  rw [hi, map_sub] at ht
  change r.val.app (op (Over.mk (homOfLE a.property)))
    (E.presheaf.map (homOfLE (show a.val.U.1 ≤ b.val.U.1 from h)).op b.val.lift) =
      scalarRestriction (show a.val.U.1 ≤ b.val.U.1 from h) (complementaryParameter g r b) at hn
  rw [hn] at ht
  exact eq_add_of_sub_eq' ht.symm

/-- The complementary section in the original frame, landing in the actual complement. -/
def localComplementarySection (a : FrameOn g W) :
    a.val.U.1.toScheme ⟶ (quotientComplement i g hig hS).toScheme :=
  a.val.isoSpec.hom ≫
    Spec.map (CommRingCat.ofHom (Polynomial.evalRingHom (complementaryParameter g r a))) ≫
      complementChart i g hig hS a.val

@[reassoc] theorem localComplementarySection_ι (a : FrameOn g W) :
    localComplementarySection i g hig hS r a ≫ (quotientComplement i g hig hS).ι =
      (a.val.isoSpec.hom ≫ Sections.affinePoint Γ(X, a.val.U.1)
        (complementaryParameter g r a)) ≫ chartInclusion i g hig hS a.val := by
  simp only [localComplementarySection, Category.assoc, complementChart_ι,
    Sections.affinePoint, Sections.chartSection]

include hr in
private theorem localComplementarySection_compatible {a b : FrameOn g W} (h : a ≤ b) :
    X.homOfLE (show a.val.U.1 ≤ b.val.U.1 from h) ≫
      localComplementarySection i g hig hS r b = localComplementarySection i g hig hS r a := by
  have hc : a.val.isoSpec.hom ≫ Spec.map (CommRingCat.ofHom
      (scalarRestriction (show a.val.U.1 ≤ b.val.U.1 from h))) =
      X.homOfLE h ≫ b.val.isoSpec.hom :=
    a.val.U.1.toSpecΓ_SpecMap_presheaf_map b.val.U.1 h
  have ha : (a.val.isoSpec.hom ≫ Sections.affinePoint Γ(X, a.val.U.1)
      (complementaryParameter g r a)) ≫ chartMap i g hig hS h =
      X.homOfLE h ≫ b.val.isoSpec.hom ≫ Sections.affinePoint Γ(X, b.val.U.1)
        (complementaryParameter g r b) := by
    simp only [chartMap, transitionMatrix, Category.assoc]
    rw [Sections.affinePoint_translation_assoc,
      ← complementaryParameter_transition i g hig hS r hr h,
      Sections.affinePoint_coefficient, ← Category.assoc, hc, Category.assoc]
  apply (cancel_mono (quotientComplement i g hig hS).ι).mp
  rw [Category.assoc, localComplementarySection_ι, localComplementarySection_ι]
  have hmap := congrArg (fun f => f ≫ chartInclusion i g hig hS b.val) ha
  simpa only [Category.assoc, chartMap_chartInclusion] using hmap.symm

include hr in
/-- The constructed complementary chart maps satisfy the original cover matching equation. -/
theorem localComplementarySection_coverCompatible [Epi g]
    {a b : FrameOn g W} (h : a ⟶ b) :
    (frameCoverOn g W).trans h ≫ localComplementarySection i g hig hS r b =
      localComplementarySection i g hig hS r a := by
  rw [frameCoverOn_trans]
  exact localComplementarySection_compatible i g hig hS r hr (leOfHom h)

/-- The supplied splitting over the original open constructs the complementary section. -/
def complementarySection : W.toScheme ⟶ (quotientComplement i g hig hS).toScheme := by
  letI : Epi g := hS.epi_g
  exact (frameCoverOn g W).glueMorphismsOfLocallyDirected
    (fun a => localComplementarySection i g hig hS r a)
    (fun {_ _} h => localComplementarySection_coverCompatible i g hig hS r hr h)

/-- The constructed complementary section has its original local formula. -/
@[reassoc] theorem complementarySection_chart (a : FrameOn g W) :
    X.homOfLE a.property ≫ complementarySection i g hig hS r hr =
      localComplementarySection i g hig hS r a := by
  let : Epi g := hS.epi_g
  exact (frameCoverOn g W).map_glueMorphismsOfLocallyDirected
    (fun a => localComplementarySection i g hig hS r a)
    (fun {_ _} h => localComplementarySection_coverCompatible i g hig hS r hr h) a

/-- The complementary section retains the exact original-open projection triangle. -/
@[reassoc] theorem complementarySection_projection :
    complementarySection i g hig hS r hr ≫ complementProjection i g hig hS = W.ι := by
  let : Epi g := hS.epi_g
  apply (frameCoverOn g W).hom_ext
  intro a
  change FrameOn g W at a
  change X.homOfLE a.property ≫ _ = X.homOfLE a.property ≫ W.ι
  rw [← Category.assoc, complementarySection_chart]
  rw [complementProjection, ← Category.assoc, localComplementarySection_ι,
    Category.assoc, chartInclusion_projection]
  simp only [chartProjection, Category.assoc, Sections.affinePoint_over_assoc,
    Iso.hom_inv_id_assoc, Scheme.homOfLE_ι]

/-- The section over the split open is disjoint from the entire actual quotient section. -/
theorem complementarySection_disjoint :
    Disjoint (Set.range (complementarySection i g hig hS r hr ≫ (quotientComplement i g hig hS).ι))
      (Set.range (quotientSection i g hig hS)) := by
  rw [Set.disjoint_left]
  rintro _ ⟨x, rfl⟩ hx
  exact (complementarySection i g hig hS r hr x).property hx

section Converse

variable (s : W.toScheme ⟶ (quotientComplement i g hig hS).toScheme)
  (hs : s ≫ complementProjection i g hig hS = W.ι)

/-- The actual complementary section in the original affine chart over a frame. -/
def complementSectionChart (a : FrameOn g W) :
    a.val.U.1.toScheme ⟶ Spec (.of (Polynomial Γ(X, a.val.U.1))) :=
  (complementChart_isPullback i g hig hS a.val).lift
    (X.homOfLE a.property ≫ s) (𝟙 _) (by
      rw [Category.assoc, hs, Scheme.homOfLE_ι, Category.id_comp])

@[reassoc] theorem complementSectionChart_chart (a : FrameOn g W) :
    complementSectionChart i g hig hS s hs a ≫ complementChart i g hig hS a.val =
      X.homOfLE a.property ≫ s :=
  (complementChart_isPullback i g hig hS a.val).lift_fst _ _ _

private theorem complementSectionChart_over (a : FrameOn g W) :
    (a.val.isoSpec.inv ≫ complementSectionChart i g hig hS s hs a) ≫
      Spec.map (CommRingCat.ofHom (Polynomial.C : Γ(X, a.val.U.1) →+*
        Polynomial Γ(X, a.val.U.1))) = 𝟙 _ := by
  have h := (complementChart_isPullback i g hig hS a.val).lift_snd
    (X.homOfLE a.property ≫ s) (𝟙 _) (by
      rw [Category.assoc, hs, Scheme.homOfLE_ι, Category.id_comp])
  have hh := congrArg (fun q => a.val.isoSpec.inv ≫ q ≫ a.val.isoSpec.hom) h
  simpa only [complementSectionChart, Category.assoc, Iso.inv_hom_id,
    Iso.inv_hom_id_assoc, Category.id_comp, Category.comp_id] using hh

/-- The literal polynomial parameter extracted from the original complementary section. -/
def complementSectionParameter (a : FrameOn g W) : Γ(X, a.val.U.1) :=
  Sections.polynomialSectionParameter
    (a.val.isoSpec.inv ≫ complementSectionChart i g hig hS s hs a)

/-- The extracted parameter recovers the actual section in its original affine chart. -/
@[reassoc] theorem complementSection_parameter_chart (a : FrameOn g W) :
    a.val.isoSpec.hom ≫
      Spec.map (CommRingCat.ofHom (Polynomial.evalRingHom
        (complementSectionParameter i g hig hS s hs a))) ≫
      complementChart i g hig hS a.val = X.homOfLE a.property ≫ s := by
  have h := Sections.polynomialSection_eq
    (a.val.isoSpec.inv ≫ complementSectionChart i g hig hS s hs a)
    (complementSectionChart_over i g hig hS s hs a)
  have hh := congrArg (fun q => a.val.isoSpec.hom ≫ q ≫
    complementChart i g hig hS a.val) h
  simpa only [complementSectionParameter, Category.assoc, Iso.hom_inv_id_assoc,
    complementSectionChart_chart] using hh.symm

/-- The recovered affine parameter retains the original total-bundle chart formula. -/
@[reassoc] theorem complementSection_parameter_projective (a : FrameOn g W) :
    a.val.isoSpec.hom ≫ Sections.affinePoint Γ(X, a.val.U.1)
      (complementSectionParameter i g hig hS s hs a) ≫ chartInclusion i g hig hS a.val =
      X.homOfLE a.property ≫ s ≫ (quotientComplement i g hig hS).ι := by
  have h := congrArg (fun f => f ≫ (quotientComplement i g hig hS).ι)
    (complementSection_parameter_chart i g hig hS s hs a)
  simpa only [Category.assoc, complementChart_ι, Sections.affinePoint,
    Sections.chartSection] using h

/-- The parameters of an actual complementary section obey the original translation cocycle. -/
theorem complementSectionParameter_transition {a b : FrameOn g W} (h : a ≤ b) :
    scalarRestriction (show a.val.U.1 ≤ b.val.U.1 from h)
      (complementSectionParameter i g hig hS s hs b) =
      complementSectionParameter i g hig hS s hs a +
        transition i g hig hS (show a.val ≤ b.val from h) := by
  let f := scalarRestriction (show a.val.U.1 ≤ b.val.U.1 from h)
  let pa := complementSectionParameter i g hig hS s hs a
  let pb := complementSectionParameter i g hig hS s hs b
  let t := transition i g hig hS (show a.val ≤ b.val from h)
  have hc : a.val.isoSpec.hom ≫ Spec.map (CommRingCat.ofHom f) =
      X.homOfLE h ≫ b.val.isoSpec.hom :=
    a.val.U.1.toSpecΓ_SpecMap_presheaf_map b.val.U.1 h
  have ho : a.val.isoSpec.hom ≫ Sections.affinePoint Γ(X, a.val.U.1) pa ≫
      chartMap i g hig hS h =
      X.homOfLE h ≫ b.val.isoSpec.hom ≫ Sections.affinePoint Γ(X, b.val.U.1) pb := by
    apply (cancel_mono (chartInclusion i g hig hS b.val)).mp
    simp only [Category.assoc, chartMap_chartInclusion, pa, pb,
      complementSection_parameter_projective, Scheme.homOfLE_homOfLE_assoc]
  have hp : Sections.affinePoint Γ(X, a.val.U.1) (pa + t) ≫ LinearChange.coefficientMap f =
      Sections.affinePoint Γ(X, a.val.U.1) (f pb) ≫ LinearChange.coefficientMap f := by
    apply (cancel_epi a.val.isoSpec.hom).mp
    calc
      a.val.isoSpec.hom ≫ (Sections.affinePoint Γ(X, a.val.U.1) (pa + t) ≫
          LinearChange.coefficientMap f) =
          a.val.isoSpec.hom ≫ Sections.affinePoint Γ(X, a.val.U.1) pa ≫
            chartMap i g hig hS h := by
        simp only [chartMap, transitionMatrix,
          Sections.affinePoint_translation_assoc, f, t]
      _ = X.homOfLE h ≫ b.val.isoSpec.hom ≫
          Sections.affinePoint Γ(X, b.val.U.1) pb := ho
      _ = a.val.isoSpec.hom ≫ Spec.map (CommRingCat.ofHom f) ≫
          Sections.affinePoint Γ(X, b.val.U.1) pb := by
        simpa only [Category.assoc] using congrArg
          (fun q => q ≫ Sections.affinePoint Γ(X, b.val.U.1) pb) hc.symm
      _ = a.val.isoSpec.hom ≫ (Sections.affinePoint Γ(X, a.val.U.1) (f pb) ≫
          LinearChange.coefficientMap f) := by rw [Sections.affinePoint_coefficient]
  have he : Sections.affinePoint Γ(X, a.val.U.1) (pa + t) =
      Sections.affinePoint Γ(X, a.val.U.1) (f pb) :=
    (LinearChange.coefficientMap_isPullback f).hom_ext hp
      (by simp only [Sections.affinePoint_over])
  exact (Sections.affinePoint_injective he).symm

/-- Removing the extracted parameter from the original lift gives the local lift that glues. -/
def adjustedComplementLift (a : FrameOn g W) : Γ(E, a.val.U.1) :=
  a.val.lift - Scheme.Modules.Hom.app i a.val.U.1 (complementSectionParameter i g hig hS s hs a)

/-- The actual adjusted lifts agree under the original module restriction maps. -/
theorem adjustedComplementLift_restrict {a b : FrameOn g W} (h : a ≤ b) :
    E.presheaf.map (homOfLE (show a.val.U.1 ≤ b.val.U.1 from h)).op
      (adjustedComplementLift i g hig hS s hs b) =
      adjustedComplementLift i g hig hS s hs a := by
  have hn := ConcreteCategory.congr_hom
    ((Scheme.Modules.Hom.mapPresheaf i).naturality
      (homOfLE (show a.val.U.1 ≤ b.val.U.1 from h)).op)
      (complementSectionParameter i g hig hS s hs b)
  change Scheme.Modules.Hom.app i a.val.U.1 (scalarRestriction h
      (complementSectionParameter i g hig hS s hs b)) =
    E.presheaf.map (homOfLE (show a.val.U.1 ≤ b.val.U.1 from h)).op
      (Scheme.Modules.Hom.app i b.val.U.1 (complementSectionParameter i g hig hS s hs b)) at hn
  rw [adjustedComplementLift, map_sub, ← hn,
    complementSectionParameter_transition i g hig hS s hs h, map_add,
    transition_spec i g hig hS (show a.val ≤ b.val from h), adjustedComplementLift]
  abel

private theorem frameOpens_cover (V : X.Opens) [Epi g] :
    V ≤ ⨆ a : FrameOn g V, a.val.U.1 := by
  intro x hx
  obtain ⟨a, hxa, haV⟩ := exists_frame_le g V x hx
  exact Opens.mem_iSup.mpr ⟨⟨a, haV⟩, hxa⟩

private theorem adjustedComplementLift_compatible :
    TopCat.Presheaf.IsCompatible E.presheaf (fun a : FrameOn g W => a.val.U.1)
      (adjustedComplementLift i g hig hS s hs) := by
  let : Epi g := hS.epi_g
  intro a b
  apply TopCat.Sheaf.eq_of_locally_eq' ⟨E.presheaf, E.isSheaf⟩
    (fun c : FrameOn g (a.val.U.1 ⊓ b.val.U.1) => c.val.U.1) _
    (fun c => homOfLE c.property) (frameOpens_cover g _)
  intro c
  let d : FrameOn g W := ⟨c.val, c.property.trans (inf_le_left.trans a.property)⟩
  have hda : d ≤ a := c.property.trans inf_le_left
  have hdb : d ≤ b := c.property.trans inf_le_right
  simp only [← Functor.map_comp_apply, ← op_comp]
  exact (adjustedComplementLift_restrict i g hig hS s hs hda).trans
    (adjustedComplementLift_restrict i g hig hS s hs hdb).symm

/-- The adjusted original frame lifts glue uniquely in the original module sheaf. -/
theorem existsUnique_complementLift :
    ∃! z : Γ(E, W), ∀ a : FrameOn g W,
      E.presheaf.map (homOfLE a.property).op z = adjustedComplementLift i g hig hS s hs a := by
  let : Epi g := hS.epi_g
  exact TopCat.Sheaf.existsUnique_gluing' ⟨E.presheaf, E.isSheaf⟩
    (fun a : FrameOn g W => a.val.U.1) W (fun a => homOfLE a.property)
    (frameOpens_cover g W) (adjustedComplementLift i g hig hS s hs)
    (adjustedComplementLift_compatible i g hig hS s hs)

/-- The complementary section constructs an actual lift of one in the original module. -/
def complementLift : Γ(E, W) :=
  (existsUnique_complementLift i g hig hS s hs).choose

/-- The original restrictions of the constructed lift are its adjusted local frame lifts. -/
theorem complementLift_restrict (a : FrameOn g W) :
    E.presheaf.map (homOfLE a.property).op (complementLift i g hig hS s hs) =
      adjustedComplementLift i g hig hS s hs a :=
  (existsUnique_complementLift i g hig hS s hs).choose_spec.1 a

/-- The actual glued lift maps to one under the original quotient map. -/
theorem complementLift_quotient :
    Scheme.Modules.Hom.app g W (complementLift i g hig hS s hs) = (1 : Γ(X, W)) := by
  let : Epi g := hS.epi_g
  let O : X.Modules := SheafOfModules.unit X.ringCatSheaf
  apply TopCat.Sheaf.eq_of_locally_eq'
    ⟨O.presheaf, O.isSheaf⟩
    (fun a : FrameOn g W => a.val.U.1) W (fun a => homOfLE a.property)
    (frameOpens_cover g W)
  intro a
  have hn := ConcreteCategory.congr_hom
    ((Scheme.Modules.Hom.mapPresheaf g).naturality (homOfLE a.property).op)
    (complementLift i g hig hS s hs)
  change Scheme.Modules.Hom.app g a.val.U.1
      (E.presheaf.map (homOfLE a.property).op (complementLift i g hig hS s hs)) =
    scalarRestriction a.property
      (Scheme.Modules.Hom.app g W (complementLift i g hig hS s hs)) at hn
  have hz := congrArg
    (fun q : (SheafOfModules.unit X.ringCatSheaf : X.Modules) ⟶
      SheafOfModules.unit X.ringCatSheaf => q.val.app (op a.val.U.1)
        (complementSectionParameter i g hig hS s hs a)) hig
  change Scheme.Modules.Hom.app g a.val.U.1
    (Scheme.Modules.Hom.app i a.val.U.1 (complementSectionParameter i g hig hS s hs a)) = 0 at hz
  change scalarRestriction a.property
      (Scheme.Modules.Hom.app g W (complementLift i g hig hS s hs)) =
    scalarRestriction a.property 1
  have hv : Scheme.Modules.Hom.app g a.val.U.1
      (E.presheaf.map (homOfLE a.property).op (complementLift i g hig hS s hs)) =
      (1 : Γ(X, a.val.U.1)) := by
    rw [complementLift_restrict, adjustedComplementLift, map_sub,
      a.val.quotient_lift, hz, sub_zero]
  exact hn.symm.trans (hv.trans (map_one (scalarRestriction a.property)).symm)

end Converse

variable (s : X ⟶ (quotientComplement i g hig hS).toScheme)
  (hs : s ≫ complementProjection i g hig hS = 𝟙 X)

/-- The actual global lift of one determined by the supplied global complementary section. -/
def globalComplementLift : Γ(E, ⊤) :=
  complementLift i g hig hS ((⊤ : X.Opens).ι ≫ s)
    (by rw [Category.assoc, hs, Category.comp_id])

/-- The original short exact complex splits through its constructed global quotient lift. -/
def globalComplementSplitting : (extensionComplex i g hig).Splitting := by
  let z := globalComplementLift i g hig hS s hs
  let q := (unitHomGlobalSectionsEquiv X E).symm z
  have hq : q ≫ g = 𝟙 _ := by
    apply (unitHomGlobalSectionsEquiv X (SheafOfModules.unit X.ringCatSheaf)).injective
    rw [unitHomGlobalSectionsEquiv_naturality]
    simp only [q, Equiv.apply_symm_apply, unitHomGlobalSectionsEquiv_apply]
    change Scheme.Modules.Hom.app g ⊤ z = (1 : Γ(X, ⊤))
    exact complementLift_quotient i g hig hS _ _
  exact ShortComplex.Splitting.ofExactOfSection _ hS.exact q hq hS.mono_f

/-- A complementary global section constructs a retraction of the original extension inclusion. -/
def retractionOfComplementSection : E ⟶ SheafOfModules.unit X.ringCatSheaf :=
  (globalComplementSplitting i g hig hS s hs).r

/-- The constructed retraction satisfies the equation for the original inclusion. -/
@[reassoc] theorem inclusion_retractionOfComplementSection :
    i ≫ retractionOfComplementSection i g hig hS s hs = 𝟙 _ :=
  (globalComplementSplitting i g hig hS s hs).f_r

end AlgebraicGeometry.Scheme.ProjectiveBundle.RankTwoExtension
