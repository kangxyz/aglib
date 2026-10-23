/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.Blowup.ProjectivePresentation.ChartCoordinates
public import Aglib.AlgebraicGeometry.Blowup.ProjectivePresentation.Restriction
public import Aglib.AlgebraicGeometry.Blowup.ProjectivePresentation.FrameCover

public import Aglib.AlgebraicGeometry.ProjectiveSpace.BaseChange.Cartesian
public import Aglib.AlgebraicGeometry.ProjectiveSpace.Segre.ClosedComposition
public import Aglib.AlgebraicGeometry.ProjectiveSpace.FromSections.LineSource.Pullback
public import Aglib.AlgebraicGeometry.ProjectiveSpace.FromSections.Coefficients

/-!
# Actual projective embeddings of scalar base changes of a blowup

A finite coherent presentation supplies the original coordinate morphism.
Its relative graph is closed on the actual compatible affine frames, by
comparison with the scalar Rees polynomial embedding. The original Segre
map then gives a finite projective embedding of the unchanged fibre product,
with its original structure triangle. Scalar changes are arbitrary.
-/

@[expose] public noncomputable section

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open CategoryTheory CategoryTheory.Limits

universe u

namespace AlgebraicGeometry.Scheme.Blowup.ProjectivePresentation

open AlgebraicGeometry.ProjectiveSpace.FromSections
open AlgebraicGeometry.Scheme.Modules AlgebraicGeometry.Scheme.Modules.Invertible

private theorem row_restriction_equation
    {P S T : Scheme.{u}} {t : T ⟶ P} {p : T ⟶ S}
    {D L : P.Modules} {N : S.Modules} {K : T.Modules}
    {eSource : (Modules.pullback t).obj D ≅ SheafOfModules.unit T.ringCatSheaf}
    {d : D ⟶ L} {eLine : (Modules.pullback t).obj L ≅ K}
    {s : SheafOfModules.unit S.ringCatSheaf ⟶ N}
    {Q : (Modules.pullback p).obj N ⟶ K}
    (h : Restriction.RowRestrictionEq t p D L N K eSource d eLine s Q)
    (d' : D ⟶ L) (s' : SheafOfModules.unit T.ringCatSheaf ⟶ K)
    (hd : d' = d) (hs : s' = pullbackSection p s ≫ Q) :
    eSource.inv ≫ (Modules.pullback t).map d' ≫ eLine.hom = s' := by
  rw [hd, hs]
  exact h

private theorem presentation_row_eq_original
    {X W : Scheme.{u}} {I : X.IdealSheafData} (B : BlowupDatum I) (f : W ⟶ X)
    {A ι : Type u} [CommRing A] (j : W ⟶ ProjectiveSpace A ι)
    (N : ℕ) {J : Type u} [Finite J]
    (π : (∐ fun _ : J => (Modules.pullback j).obj
      (ProjectiveSpace.twistingSheaf A ι (-(N : ℤ)))) ⟶ degreeOneModule (I := I) f)
    (r : J) :
    lineQuotientRow (sourceTwistLine B f j N) (pulledTautologicalLine B f)
        (commonTwistQuotient B f j N π) r =
      Restriction.originalRow B f ((Modules.pullback j).obj
        (ProjectiveSpace.twistingSheaf A ι (-(N : ℤ)))) π r := by
  rw [lineQuotientRow, commonTwistQuotient, PreservesCoproduct.inv_hom]
  rfl

private theorem coordinateMapOfPresentation_value
    {X W : Scheme.{u}} {I : X.IdealSheafData} (B : BlowupDatum I) (f : W ⟶ X)
    {A ι : Type u} [CommRing A] (j : W ⟶ ProjectiveSpace A ι)
    (N : ℕ) {J : Type u} [Finite J]
    (π : (∐ fun _ : J => (Modules.pullback j).obj
      (ProjectiveSpace.twistingSheaf A ι (-(N : ℤ)))) ⟶ degreeOneModule (I := I) f)
    [Epi π] :
    let : Epi (Sigma.desc (lineQuotientRow (sourceTwistLine B f j N)
      (pulledTautologicalLine B f) (commonTwistQuotient B f j N π))) :=
      lineQuotientRow_epi _ _ _
    coordinateMapOfPresentation B f j N π =
      LineSource.mapOfFamily (sourceTwistLine B f j N).val (pulledTautologicalLine B f).val
        (sourceTwistLine B f j N).property
        (pullback.snd B.map f ≫ j ≫ ProjectiveSpace.toSpec A ι)
        (pulledTautologicalLine B f).property
        (lineQuotientRow (sourceTwistLine B f j N) (pulledTautologicalLine B f)
          (commonTwistQuotient B f j N π)) := rfl

private theorem affine_square_base_triangle
    {A S : Type u} [CommRing A] [CommRing S] {W Y T : Scheme.{u}}
    (p : Y ⟶ W) (u : Spec (.of S) ⟶ W) (t : T ⟶ Y) (r : T ⟶ Spec (.of S))
    (a : W ⟶ Spec (.of A)) (β : A →+* S)
    (ht : t ≫ p = r ≫ u) (hβ : Spec.map (CommRingCat.ofHom β) = u ≫ a) :
    r ≫ Spec.map (CommRingCat.ofHom β) = t ≫ p ≫ a :=
  (congrArg (fun z => r ≫ z) hβ).trans
    ((Category.assoc r u a).symm.trans
      ((congrArg (fun z => z ≫ a) ht.symm).trans (Category.assoc t p a)))

private theorem original_row_map_restriction
    {A S ι : Type u} [CommRing A] [CommRing S] [Finite ι]
    {X T : Scheme.{u}} (g : T ⟶ X)
    (D J : X.Modules) (hD : IsLocallyRankOne X D) (hJ : IsLocallyRankOne X J)
    (d : ι → (D ⟶ J)) [Epi (Sigma.desc d)]
    (eD : (Modules.pullback g).obj D ≅ SheafOfModules.unit T.ringCatSheaf)
    (K : T.Modules) (hK : IsLocallyRankOne T K) (eJ : (Modules.pullback g).obj J ≅ K)
    (s : ι → (SheafOfModules.unit T.ringCatSheaf ⟶ K)) [hs_epi : Epi (Sigma.desc s)]
    (hs : ∀ i, eD.inv ≫ (Modules.pullback g).map (d i) ≫ eJ.hom = s i)
    (p : X ⟶ Spec (.of A)) (pS : T ⟶ Spec (.of S)) (β : A →+* S)
    (hp : pS ≫ Spec.map (CommRingCat.ofHom β) = g ≫ p) :
    g ≫ LineSource.mapOfFamily D J hD p hJ d =
      mapOfFiniteFamily pS K hK s ≫ ProjectiveSpace.map β ι := by
  let : Epi (Sigma.desc (fun i => eD.inv ≫ (Modules.pullback g).map (d i))) :=
    LineSource.pulledTrivializedFamily_epi g D eD J d
  calc
    _ = mapOfFiniteFamily (g ≫ p) ((Modules.pullback g).obj J)
        (pullback_locallyRankOne g J hJ)
        (fun i => eD.inv ≫ (Modules.pullback g).map (d i)) :=
      LineSource.mapOfFamily_pullback_eq_of_sourceIso g D hD eD J d p hJ
    _ = mapOfFiniteFamily (g ≫ p) K hK s :=
      mapOfFiniteFamily_iso (g ≫ p) _ K _ hK _ s eJ
        (fun i => (Category.assoc _ _ _).trans (hs i))
    _ = mapOfFiniteFamily (pS ≫ Spec.map (CommRingCat.ofHom β)) K hK s := by rw [hp]
    _ = _ := (mapOfFiniteFamily_coefficients β pS K hK s).symm

section RelativeGraph

variable {A ι : Type u} [CommRing A] {Y W : Scheme.{u}}
  (p : Y ⟶ W) (a : W ⟶ Spec (.of A)) (q : Y ⟶ ProjectiveSpace A ι)
  (hq : q ≫ ProjectiveSpace.toSpec A ι = p ≫ a)

private def relativeGraph : Y ⟶ pullback a (ProjectiveSpace.toSpec A ι) :=
  pullback.lift p q hq.symm

@[reassoc]
private theorem relativeGraph_fst :
    relativeGraph p a q hq ≫ pullback.fst a (ProjectiveSpace.toSpec A ι) = p :=
  pullback.lift_fst _ _ _

@[reassoc]
private theorem relativeGraph_snd :
    relativeGraph p a q hq ≫ pullback.snd a (ProjectiveSpace.toSpec A ι) = q :=
  pullback.lift_snd _ _ _

variable {S : Type u} [CommRing S] (u : Spec (.of S) ⟶ W)
  (β : A →+* S) (hβ : Spec.map (CommRingCat.ofHom β) = u ≫ a)

private def relativeTargetChart : ProjectiveSpace S ι ⟶
    pullback a (ProjectiveSpace.toSpec A ι) :=
  pullback.lift (ProjectiveSpace.toSpec S ι ≫ u) (ProjectiveSpace.map β ι) (by
    rw [Category.assoc, ← hβ, ProjectiveSpace.map_toSpec])

@[reassoc]
private theorem relativeTargetChart_fst :
    relativeTargetChart (ι := ι) a u β hβ ≫
      pullback.fst a (ProjectiveSpace.toSpec A ι) = ProjectiveSpace.toSpec S ι ≫ u :=
  pullback.lift_fst _ _ _

@[reassoc]
private theorem relativeTargetChart_snd :
    relativeTargetChart (ι := ι) a u β hβ ≫
      pullback.snd a (ProjectiveSpace.toSpec A ι) = ProjectiveSpace.map β ι :=
  pullback.lift_snd _ _ _

private theorem relativeTargetChart_isPullback :
    IsPullback (relativeTargetChart (ι := ι) a u β hβ) (ProjectiveSpace.toSpec S ι)
      (pullback.fst a (ProjectiveSpace.toSpec A ι)) u := by
  have H : IsPullback
      (relativeTargetChart (ι := ι) a u β hβ ≫
        pullback.snd a (ProjectiveSpace.toSpec A ι))
      (ProjectiveSpace.toSpec S ι) (ProjectiveSpace.toSpec A ι) (u ≫ a) := by
    rw [relativeTargetChart_snd, ← hβ]
    exact ProjectiveSpace.isPullback_map β ι
  exact H.of_right (relativeTargetChart_fst a u β hβ)
    (IsPullback.of_hasPullback a (ProjectiveSpace.toSpec A ι)).flip

private theorem relativeGraph_chart_isPullback
    {V : Scheme.{u}} (t : V ⟶ Y) (v : V ⟶ Spec (.of S))
    (k : V ⟶ ProjectiveSpace S ι) (H : IsPullback t v p u)
    (hk : k ≫ ProjectiveSpace.toSpec S ι = v)
    (hc : t ≫ q = k ≫ ProjectiveSpace.map β ι) :
    IsPullback t k (relativeGraph p a q hq) (relativeTargetChart (ι := ι) a u β hβ) := by
  have hw : t ≫ relativeGraph p a q hq = k ≫ relativeTargetChart (ι := ι) a u β hβ := by
    apply pullback.hom_ext
    · simp only [Category.assoc, relativeGraph_fst, relativeTargetChart_fst]
      rw [← Category.assoc, hk]
      exact H.w
    · simp only [Category.assoc, relativeGraph_snd, relativeTargetChart_snd]
      exact hc
  have H' : IsPullback t (k ≫ ProjectiveSpace.toSpec S ι)
      (relativeGraph p a q hq ≫ pullback.fst a (ProjectiveSpace.toSpec A ι)) u := by
    rw [hk, relativeGraph_fst]
    exact H
  exact H'.of_bot hw (relativeTargetChart_isPullback a u β hβ)

end RelativeGraph

section Gluing

variable {A ι : Type u} [CommRing A] {Y W : Scheme.{u}}
  (p : Y ⟶ W) (a : W ⟶ Spec (.of A)) (q : Y ⟶ ProjectiveSpace A ι)
  (hq : q ≫ ProjectiveSpace.toSpec A ι = p ≫ a)

private theorem relativeGraph_closed_of_actual_affine_charts
    (𝒰 : W.AffineOpenCover.{u, u})
    (β : ∀ i, A →+* 𝒰.X i)
    (hβ : ∀ i, Spec.map (CommRingCat.ofHom (β i)) = 𝒰.f i ≫ a)
    (V : 𝒰.I₀ → Scheme.{u}) (t : ∀ i, V i ⟶ Y)
    (v : ∀ i, V i ⟶ Spec (𝒰.X i))
    (k : ∀ i, V i ⟶ ProjectiveSpace (𝒰.X i) ι)
    (H : ∀ i, IsPullback (t i) (v i) p (𝒰.f i))
    (hk : ∀ i, k i ≫ ProjectiveSpace.toSpec (𝒰.X i) ι = v i)
    (hc : ∀ i, t i ≫ q = k i ≫ ProjectiveSpace.map (β i) ι)
    (hclosed : ∀ i, IsClosedImmersion (k i)) :
    IsClosedImmersion (relativeGraph p a q hq) := by
  let Z := pullback a (ProjectiveSpace.toSpec A ι)
  let z : Z ⟶ W := pullback.fst a (ProjectiveSpace.toSpec A ι)
  let 𝒱 := 𝒰.openCover.pullback₁ z
  apply IsZariskiLocalAtTarget.of_openCover (P := @IsClosedImmersion) 𝒱
  intro i
  let e := (relativeTargetChart_isPullback (ι := ι) a (𝒰.f i) (β i) (hβ i)).isoPullback
  have he : e.hom ≫ 𝒱.f i = relativeTargetChart (ι := ι) a (𝒰.f i) (β i) (hβ i) :=
    (relativeTargetChart_isPullback (ι := ι) a (𝒰.f i) (β i) (hβ i)).isoPullback_hom_fst
  have Hi := relativeGraph_chart_isPullback p a q hq (𝒰.f i) (β i) (hβ i)
    (t i) (v i) (k i) (H i) (hk i) (hc i)
  have H' : IsPullback (t i) (k i ≫ e.hom) (relativeGraph p a q hq) (𝒱.f i) := by
    refine Hi.of_iso (Iso.refl _) (Iso.refl _) e (Iso.refl _) ?_ ?_ ?_ ?_
    · simp only [Iso.refl_hom, Category.comp_id, Category.id_comp]
    · simp only [Iso.refl_hom, Category.id_comp]
    · simp only [Iso.refl_hom, Category.comp_id, Category.id_comp]
    · simpa only [Iso.refl_hom, Category.comp_id] using he.symm
  let : IsClosedImmersion (k i) := hclosed i
  change IsClosedImmersion (pullback.snd (relativeGraph p a q hq) (𝒱.f i))
  rw [← H'.isoPullback_inv_snd]
  infer_instance

end Gluing

end AlgebraicGeometry.Scheme.Blowup.ProjectivePresentation


namespace AlgebraicGeometry.Scheme.Blowup.ProjectivePresentation

open AlgebraicGeometry.ProjectiveSpace.FromSections
open AlgebraicGeometry.Scheme.Modules AlgebraicGeometry.Scheme.Modules.Invertible

variable {X W : Scheme.{u}} {I : X.IdealSheafData} (B : BlowupDatum I) (f : W ⟶ X)
  {A ι : Type u} [CommRing A] [Finite ι] (j : W ⟶ ProjectiveSpace A ι)

omit [Finite ι] in
private theorem coordinateMapOfPresentation_restriction
    (N : ℕ) {J : Type u} [Finite J]
    (π : (∐ fun _ : J => (Modules.pullback j).obj
      (ProjectiveSpace.twistingSheaf A ι (-(N : ℤ)))) ⟶ degreeOneModule (I := I) f)
    [Epi π] (V : X.affineOpens) {S : Type u} [CommRing S] [Algebra Γ(X, V.val) S]
    (u : Spec (.of S) ⟶ W)
    (hsq : Restriction.affineScalarMap V S ≫ V.property.fromSpec = u ≫ f)
    (eD : (Modules.pullback u).obj ((Modules.pullback j).obj
      (ProjectiveSpace.twistingSheaf A ι (-(N : ℤ)))) ≅
        SheafOfModules.unit (Spec (.of S)).ringCatSheaf)
    (β : A →+* S)
    (hβ : Spec.map (CommRingCat.ofHom β) = u ≫ j ≫ ProjectiveSpace.toSpec A ι) :
    Restriction.chartMap B V f u hsq ≫ coordinateMapOfPresentation B f j N π =
      OriginalRowRestriction.mapOfFramedPresentation (Restriction.restrictedDatum B V)
        ((Modules.pullback u).obj ((Modules.pullback j).obj
          (ProjectiveSpace.twistingSheaf A ι (-(N : ℤ))))) eD
        (Restriction.localPresentation V f u hsq ((Modules.pullback j).obj
          (ProjectiveSpace.twistingSheaf A ι (-(N : ℤ)))) π) ≫
        ProjectiveSpace.map β J := by
  let D := (Modules.pullback j).obj (ProjectiveSpace.twistingSheaf A ι (-(N : ℤ)))
  let BR := Restriction.restrictedDatum B V
  let pR := pullback.snd BR.map (Restriction.affineScalarMap V S)
  let t := Restriction.chartMap B V f u hsq
  let DU := (Modules.pullback u).obj D
  let πU := Restriction.localPresentation V f u hsq D π
  let k := OriginalRowRestriction.mapOfFramedPresentation BR DU eD πU
  let a : W ⟶ Spec (.of A) := j ≫ ProjectiveSpace.toSpec A ι
  let d := lineQuotientRow (sourceTwistLine B f j N) (pulledTautologicalLine B f)
    (commonTwistQuotient B f j N π)
  let : Epi (Sigma.desc d) := lineQuotientRow_epi _ _ _
  let s := OriginalRowRestriction.pulledFramedFamily BR DU eD πU
  let hs_epi : Epi (Sigma.desc s) :=
    OriginalRowRestriction.pulledFramedFamily_epi BR DU eD πU
  let : Epi (Sigma.desc s) := hs_epi
  let K := OriginalRowRestriction.affineLine (S := S) BR
  let hK : IsLocallyRankOne _ K :=
    (pulledTautologicalLine BR (Spec.algebraMap Γ(X, V.val) S)).property
  let eK : (Modules.pullback t).obj (pulledTautologicalLine B f).val ≅ K :=
    Restriction.pulledLineRestrictionIso B V f u hsq
  have hd (r : J) : d r = Restriction.originalRow B f D π r :=
    presentation_row_eq_original B f j N π r
  have hs' (r : J) : s r =
      pullbackSection (pullback.snd (Restriction.restrictedDatum B V).map
        (Restriction.affineScalarMap V S))
        (eD.inv ≫ Sigma.ι (fun _ : J => (Modules.pullback u).obj D) r ≫
          Restriction.localPresentation V f u hsq D π) ≫
            pulledTautologicalQuotient (Restriction.restrictedDatum B V)
              (Restriction.affineScalarMap V S) := rfl
  have he (r : J) := row_restriction_equation
    (Restriction.originalRow_restriction B V f u hsq D π eD r)
    (d r) (s r) (hd r) (hs' r)
  have hp := affine_square_base_triangle (pullback.snd B.map f) u t pR a β
    (Restriction.chartMap_snd B V f u hsq) hβ
  have hm := original_row_map_restriction (hs_epi := hs_epi) t
    (sourceTwistLine B f j N).val (pulledTautologicalLine B f).val
    (sourceTwistLine B f j N).property (pulledTautologicalLine B f).property d
    (Restriction.sourceFrame B V f u hsq D eD)
    K hK eK s he
    (pullback.snd B.map f ≫ a) pR β hp
  have hq := coordinateMapOfPresentation_value B f j N π
  have hk : k = @mapOfFiniteFamily S _ J
      (pullback BR.map (Restriction.affineScalarMap V S)) pR K hK inferInstance s hs_epi := rfl
  exact (congrArg (fun q => t ≫ q) hq).trans
    (hm.trans (congrArg (fun q => q ≫ ProjectiveSpace.map β J) hk.symm))

omit [Finite ι] in
private theorem coordinateMapOfPresentation_relativeGraph_closed
    (N : ℕ) {J : Type u} [Finite J]
    (π : (∐ fun _ : J => (Modules.pullback j).obj
      (ProjectiveSpace.twistingSheaf A ι (-(N : ℤ)))) ⟶ degreeOneModule (I := I) f)
    [Epi π] :
    IsClosedImmersion (relativeGraph (pullback.snd B.map f)
      (j ≫ ProjectiveSpace.toSpec A ι) (coordinateMapOfPresentation B f j N π)
      (coordinateMapOfPresentation_toSpec B f j N π)) := by
  let D := (Modules.pullback j).obj (ProjectiveSpace.twistingSheaf A ι (-(N : ℤ)))
  let hD : IsLocallyRankOne W D :=
    (pullbackLineBundle j (ProjectiveSpace.twistingLineBundle A ι (-(N : ℤ)))).property
  obtain ⟨𝒰, V, φ, e, hsq⟩ := exists_affine_frame_cover f D hD
  let (i : 𝒰.I₀) : Algebra Γ(X, (V i).val) (𝒰.X i) := (φ i).hom.toAlgebra
  have hs (i : 𝒰.I₀) :
      Restriction.affineScalarMap (V i) (𝒰.X i) ≫ (V i).property.fromSpec = 𝒰.f i ≫ f :=
    hsq i
  let BR (i : 𝒰.I₀) := Restriction.restrictedDatum B (V i)
  let pR (i : 𝒰.I₀) := pullback.snd (BR i).map
    (Spec.algebraMap Γ(X, (V i).val) (𝒰.X i))
  let t (i : 𝒰.I₀) := Restriction.chartMap B (V i) f (𝒰.f i) (hs i)
  let DU (i : 𝒰.I₀) := (Modules.pullback (𝒰.f i)).obj D
  let πU (i : 𝒰.I₀) := Restriction.localPresentation (V i) f (𝒰.f i) (hs i) D π
  let k (i : 𝒰.I₀) := OriginalRowRestriction.mapOfFramedPresentation (BR i) (DU i) (e i) (πU i)
  let a : W ⟶ Spec (.of A) := j ≫ ProjectiveSpace.toSpec A ι
  let β (i : 𝒰.I₀) : A →+* 𝒰.X i := (Spec.preimage (𝒰.f i ≫ a)).hom
  have hβ (i : 𝒰.I₀) : Spec.map (CommRingCat.ofHom (β i)) = 𝒰.f i ≫ a :=
    Spec.map_preimage _
  have hmap (i : 𝒰.I₀) : t i ≫ coordinateMapOfPresentation B f j N π =
      k i ≫ ProjectiveSpace.map (β i) J :=
    coordinateMapOfPresentation_restriction B f j N π (V i) (𝒰.f i) (hs i) (e i)
      (β i) (hβ i)
  apply relativeGraph_closed_of_actual_affine_charts (pullback.snd B.map f) a
    (coordinateMapOfPresentation B f j N π) (coordinateMapOfPresentation_toSpec B f j N π)
    𝒰 β hβ (fun i => pullback (BR i).map (Restriction.affineScalarMap (V i) (𝒰.X i)))
    t pR k
  · intro i
    exact Restriction.chartMap_isPullback B (V i) f (𝒰.f i) (hs i)
  · intro i
    exact OriginalRowRestriction.mapOfFramedPresentation_toSpec (BR i) (DU i) (e i) (πU i)
  · exact hmap
  · intro i
    exact OriginalRowRestriction.mapOfFramedPresentation_isClosedImmersion
      (BR i) (DU i) (e i) (πU i)

/-- An arbitrary scalar base change of the specified blowup has an actual finite projective
embedding over the same affine base whenever the unchanged new base is already embedded.
The construction uses the original coherent presentation, its closed relative coordinate graph,
and the original Segre embedding. -/
theorem exists_projective_embedding [IsLocallyNoetherian X] [IsClosedImmersion j] :
    ∃ (J : Type u) (_ : Finite J)
      (k : pullback B.map f ⟶ ProjectiveSpace A J),
      IsClosedImmersion k ∧
        k ≫ ProjectiveSpace.toSpec A J =
          pullback.snd B.map f ≫ j ≫ ProjectiveSpace.toSpec A ι := by
  obtain ⟨N, _, J, hJ, π, hπ⟩ := exists_baseTwistPresentation (I := I) f j 0
  let : Finite J := hJ
  let : Epi π := hπ
  let a : W ⟶ Spec (.of A) := j ≫ ProjectiveSpace.toSpec A ι
  let q := coordinateMapOfPresentation B f j N π
  let γ := relativeGraph (pullback.snd B.map f) a q
    (coordinateMapOfPresentation_toSpec B f j N π)
  let : IsClosedImmersion γ := coordinateMapOfPresentation_relativeGraph_closed B f j N π
  refine ⟨J × ι, inferInstance,
    ProjectiveSpace.Segre.closedCompositionMap A J ι a j rfl γ, inferInstance, ?_⟩
  rw [ProjectiveSpace.Segre.closedCompositionMap_toSpec]
  simpa only [Category.assoc] using congrArg (fun z => z ≫ a)
    (relativeGraph_fst (pullback.snd B.map f) a q
      (coordinateMapOfPresentation_toSpec B f j N π))

end AlgebraicGeometry.Scheme.Blowup.ProjectivePresentation
