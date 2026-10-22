/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.Blowup.ClosedImmersion
public import Aglib.AlgebraicGeometry.ProjectiveSpace.AffineImmersion
public import Aglib.AlgebraicGeometry.ProjectiveSpace.Flat
public import Aglib.AlgebraicGeometry.Limits.Range

/-!
# Closed comparison with the fibre product of a blowup

For a locally finite-type base map, the blowup of the inverse-image ideal maps
by a closed immersion into the actual fibre product. This is not a nonflat
base-change isomorphism. Affine maps factor through a closed immersion and a
flat projective chart; only open base changes are used in globalization.
-/

@[expose] public noncomputable section

open CategoryTheory Limits

universe u

namespace AlgebraicGeometry.Scheme.Blowup.BaseChange

/-- The canonical comparison with the actual fibre product, without flatness. -/
def toPullback {X Z : Scheme.{u}} (f : Z ⟶ X)
    {I : X.IdealSheafData} {J : Z.IdealSheafData} (hI : I.comap f = J)
    (B : BlowupDatum I) (C : BlowupDatum J) : C.Y ⟶ pullback f B.map :=
  pullback.lift C.map (map f hI B C) (map_triangle f hI B C).symm

@[reassoc (attr := simp)]
lemma toPullback_fst {X Z : Scheme.{u}} (f : Z ⟶ X)
    {I : X.IdealSheafData} {J : Z.IdealSheafData} (hI : I.comap f = J)
    (B : BlowupDatum I) (C : BlowupDatum J) :
    toPullback f hI B C ≫ pullback.fst f B.map = C.map := pullback.lift_fst _ _ _

@[reassoc (attr := simp)]
lemma toPullback_snd {X Z : Scheme.{u}} (f : Z ⟶ X)
    {I : X.IdealSheafData} {J : Z.IdealSheafData} (hI : I.comap f = J)
    (B : BlowupDatum I) (C : BlowupDatum J) :
    toPullback f hI B C ≫ pullback.snd f B.map = map f hI B C :=
  pullback.lift_snd _ _ _

/-- Closed-then-flat factorizations give the closed comparison, with the original
ideal and the original universal representatives. -/
theorem toPullback_isClosedImmersion_of_factorization
    {X Z P : Scheme.{u}} (f : Z ⟶ X) (i : Z ⟶ P) (p : P ⟶ X)
    [IsClosedImmersion i] [Flat p] (hf : i ≫ p = f)
    {I : X.IdealSheafData} {J : Z.IdealSheafData} (hI : I.comap f = J)
    (B : BlowupDatum I) (C : BlowupDatum J) :
    IsClosedImmersion (toPullback f hI B C) := by
  subst f
  let D := flatPullbackDatum B p
  have hJ : (I.comap p).comap i = J := by
    rw [← IdealSheafData.comap_comp, hI]
  let a := map i hJ D C
  let : IsClosedImmersion a := map_isClosedImmersion i hJ D C
  let H := isPullback_of_flat p inferInstance rfl B D
  let l : pullback (i ≫ p) B.map ⟶ D.Y :=
    H.lift (pullback.snd _ _) (pullback.fst _ _ ≫ i)
      (by simpa only [Category.assoc] using (pullback.condition (f := i ≫ p) (g := B.map)).symm)
  have hl₁ : l ≫ map p rfl B D = pullback.snd _ _ := H.lift_fst _ _ _
  have hl₂ : l ≫ D.map = pullback.fst _ _ ≫ i := H.lift_snd _ _ _
  have Hl : IsPullback l (pullback.fst (i ≫ p) B.map) D.map i := by
    have Ho : IsPullback (l ≫ map p rfl B D)
        (pullback.fst (i ≫ p) B.map) B.map (i ≫ p) := by
      rw [hl₁]
      exact (IsPullback.of_hasPullback (i ≫ p) B.map).flip
    exact Ho.of_right hl₂ H
  let : IsClosedImmersion l := MorphismProperty.of_isPullback Hl.flip inferInstance
  have he : toPullback (i ≫ p) hI B C ≫ l = a := by
    apply map_unique i hJ D C
    rw [Category.assoc, hl₂, toPullback_fst_assoc]
  let : IsClosedImmersion (toPullback (i ≫ p) hI B C ≫ l) := by
    rw [he]
    infer_instance
  exact IsClosedImmersion.of_comp_isClosedImmersion _ l

/-- The comparison for a finite-type map between affine schemes. -/
theorem toPullback_isClosedImmersion_of_isAffine
    {X Z : Scheme.{u}} [IsAffine X] [IsAffine Z]
    (f : Z ⟶ X) [LocallyOfFiniteType f]
    {I : X.IdealSheafData} {J : Z.IdealSheafData} (hI : I.comap f = J)
    (B : BlowupDatum I) (C : BlowupDatum J) :
    IsClosedImmersion (toPullback f hI B C) := by
  obtain ⟨ι, hι, i, hi, he⟩ :=
    ProjectiveSpace.exists_projectiveChart_closedImmersion_of_finiteType f.appTop.hom
      (HasRingHomProperty.appTop @LocallyOfFiniteType f inferInstance)
  let := hι
  let : IsClosedImmersion i := hi
  let j := Z.isoSpec.hom ≫ i
  let p := (ProjectiveSpace.coordinateOpen Γ(X, ⊤) (Option ι) none).ι ≫
    ProjectiveSpace.toSpec Γ(X, ⊤) (Option ι) ≫ X.isoSpec.inv
  have hjp : j ≫ p = f := by
    dsimp only [j, p]
    calc
      _ = Z.isoSpec.hom ≫ ((i ≫
          (ProjectiveSpace.coordinateOpen Γ(X, ⊤) (Option ι) none).ι) ≫
          ProjectiveSpace.toSpec Γ(X, ⊤) (Option ι)) ≫ X.isoSpec.inv := by
        simp only [Category.assoc]
      _ = Z.isoSpec.hom ≫ Spec.map f.appTop ≫ X.isoSpec.inv := by rw [he]; rfl
      _ = f := by rw [Scheme.isoSpec_hom_naturality_assoc]; simp
  exact toPullback_isClosedImmersion_of_factorization f j p hjp hI B C

/-- Open restrictions of both original schemes give actual Cartesian restrictions
of the comparison and its fibre-product target. -/
theorem exists_open_restriction
    {X Z X₀ Z₀ : Scheme.{u}} (f : Z ⟶ X) (f₀ : Z₀ ⟶ X₀)
    (u : Z₀ ⟶ Z) (v : X₀ ⟶ X) [IsOpenImmersion u] [IsOpenImmersion v]
    (hf : f₀ ≫ v = u ≫ f)
    {I : X.IdealSheafData} {J : Z.IdealSheafData} (hI : I.comap f = J)
    (B : BlowupDatum I) (C : BlowupDatum J) :
    let B₀ := flatPullbackDatum B v
    let C₀ := flatPullbackDatum C u
    ∃ (h₀ : (I.comap v).comap f₀ = J.comap u)
      (l : pullback f₀ B₀.map ⟶ pullback f B.map),
      IsPullback l (pullback.fst f₀ B₀.map) (pullback.fst f B.map) u ∧
      IsPullback (toPullback f₀ h₀ B₀ C₀) (pullback.fst C.map u) l
        (toPullback f hI B C) := by
  dsimp only
  let B₀ := flatPullbackDatum B v
  let C₀ := flatPullbackDatum C u
  let b : B₀.Y ⟶ B.Y := pullback.fst B.map v
  let c : C₀.Y ⟶ C.Y := pullback.fst C.map u
  let : Flat c := show Flat (pullback.fst C.map u) from inferInstance
  have hb : b ≫ B.map = B₀.map ≫ v := pullback.condition
  have hc : c ≫ C.map = C₀.map ≫ u := pullback.condition
  have h₀ : (I.comap v).comap f₀ = J.comap u := by
    rw [← IdealSheafData.comap_comp, hf, IdealSheafData.comap_comp, hI]
  let l : pullback f₀ B₀.map ⟶ pullback f B.map :=
    pullback.lift (pullback.fst _ _ ≫ u) (pullback.snd _ _ ≫ b) (by
      rw [Category.assoc, ← hf, ← Category.assoc, pullback.condition,
        Category.assoc, ← hb, Category.assoc])
  have hl₁ : l ≫ pullback.fst f B.map = pullback.fst _ _ ≫ u :=
    pullback.lift_fst _ _ _
  have hl₂ : l ≫ pullback.snd f B.map = pullback.snd _ _ ≫ b :=
    pullback.lift_snd _ _ _
  have Hl : IsPullback l (pullback.fst f₀ B₀.map) (pullback.fst f B.map) u := by
    have H := (IsPullback.of_hasPullback f₀ B₀.map).paste_vert
      (IsPullback.of_hasPullback B.map v).flip
    have Ho : IsPullback (l ≫ pullback.snd f B.map)
        (pullback.fst f₀ B₀.map) B.map (u ≫ f) := by
      rw [hl₂, ← hf]
      exact H.flip
    exact Ho.of_right hl₁ (IsPullback.of_hasPullback f B.map).flip
  have he : toPullback f₀ h₀ B₀ C₀ ≫ l = c ≫ toPullback f hI B C := by
    apply pullback.hom_ext
    · simp only [Category.assoc, hl₁, toPullback_fst, toPullback_fst_assoc]
      exact pullback.condition.symm
    · simp only [Category.assoc, hl₂, toPullback_snd, toPullback_snd_assoc]
      apply B.hom_ext
        (cartierPullback_comp_of_flat I (C.map ≫ f) (cartier_composite f hI C) c)
      · rw [Category.assoc, hb, ← Category.assoc,
          map_triangle, Category.assoc, hf, ← Category.assoc C₀.map u, ← hc,
          Category.assoc]
      · rw [Category.assoc, map_triangle]
  have Ho : IsPullback
      (toPullback f₀ h₀ B₀ C₀ ≫ pullback.fst f₀ B₀.map) c u
      (toPullback f hI B C ≫ pullback.fst f B.map) := by
    simp only [toPullback_fst]
    exact (IsPullback.of_hasPullback C.map u).flip
  exact ⟨h₀, l, Hl, Ho.of_right he Hl.flip⟩

/-- A locally finite-type base map gives a closed comparison from the actual
blowup of the inverse-image centre to the actual fibre product. No nonflat
base-change isomorphism or Noetherian hypothesis is asserted. -/
theorem toPullback_isClosedImmersion
    {X Z : Scheme.{u}} (f : Z ⟶ X) [LocallyOfFiniteType f]
    {I : X.IdealSheafData} {J : Z.IdealSheafData} (hI : I.comap f = J)
    (B : BlowupDatum I) (C : BlowupDatum J) :
    IsClosedImmersion (toPullback f hI B C) := by
  let k := toPullback f hI B C
  apply IsZariskiLocalAtTarget.of_forall_exists_morphismRestrict (P := @IsClosedImmersion)
  intro y
  obtain ⟨V, hV, hyV, _⟩ := exists_isAffineOpen_mem_and_subset
    (x := f (pullback.fst f B.map y)) (U := ⊤) (by trivial)
  obtain ⟨W, hW, hyW, hWV⟩ := exists_isAffineOpen_mem_and_subset
    (x := pullback.fst f B.map y) (U := f ⁻¹ᵁ V) hyV
  let u := hW.fromSpec
  let v := hV.fromSpec
  let f₀ := Spec.map (f.appLE V W hWV)
  have hf : f₀ ≫ v = u ≫ f := hV.SpecMap_appLE_fromSpec f hW hWV
  let : LocallyOfFiniteType f₀ :=
    (HasRingHomProperty.Spec_iff (P := @LocallyOfFiniteType)).mpr
      (f.finiteType_appLE hV hW hWV)
  let B₀ := flatPullbackDatum B v
  let C₀ := flatPullbackDatum C u
  obtain ⟨h₀, l, Hl, Hk⟩ := exists_open_restriction f f₀ u v hf hI B C
  let : IsOpenImmersion l := MorphismProperty.of_isPullback Hl.flip inferInstance
  let : IsClosedImmersion (toPullback f₀ h₀ B₀ C₀) :=
    toPullback_isClosedImmersion_of_isAffine f₀ h₀ B₀ C₀
  have hlocal : IsClosedImmersion (pullback.snd k l) := by
    rw [← Hk.flip.isoPullback_inv_snd]
    infer_instance
  refine ⟨l.opensRange, ?_, ?_⟩
  · change y ∈ Set.range l
    rw [Scheme.Pullback.Fibre.pullback_range_fst Hl]
    change pullback.fst f B.map y ∈ Set.range hW.fromSpec
    rw [hW.range_fromSpec]
    exact hyW
  · exact (MorphismProperty.arrow_mk_iso_iff (P := @IsClosedImmersion)
      (morphismRestrictOpensRange k l)).mpr hlocal

end AlgebraicGeometry.Scheme.Blowup.BaseChange
