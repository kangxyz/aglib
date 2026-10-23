/-
Copyright (c) 2026 kangxyz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.EtaleCohomology.Continuity.StageSupport.FiniteFamilies
public import Aglib.AlgebraicGeometry.Sites.EtaleAffineBasis.AffineSchemeCoverModels
public import Aglib.AlgebraicGeometry.Sites.EtaleAffineBasis.FiniteRefinement

/-!
# Supported affine refinements over an affine stage model

The affine charts in this file have specified actual stage models. A finite
original affine étale cover of such a chart descends along its actual affine
scheme tail. Pasting its cartesian model with the chart's cartesian comparison
constructs models over the original stage schemes, with no all-qcqs-descent
assumption.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite

universe u v

namespace AlgebraicGeometry.Scheme.EtaleCohomology.Continuity.StageSupport

variable {I : Type u} [Category.{u} I] [IsFiltered I]
  {X : I ⥤ Scheme.{u}ᵒᵖ} {c : Cocone X}
  [∀ i, CompactSpace (X.obj i).unop] [∀ i, QuasiSeparatedSpace (X.obj i).unop]
  [∀ {i j} (a : i ⟶ j), IsAffineHom (X.map a).unop]
  (hc : IsColimit c)

include hc

/-- Every member of an actual finite affine étale cover of an affine modeled
object has a genuine qcqs étale model at an original stage. -/
theorem affine_cover_supported {i : I} {W : c.pt.unop.Etale}
    (M : Model X c i W) [IsAffine M.obj.left]
    {J : Type v} [Finite J] (U : J → Over W)
    [∀ j, IsAffine (U j).left.left]
    (hcover : Sieve.ofArrows (fun j => (U j).left) (fun j => (U j).hom) ∈
      c.pt.unop.smallEtaleTopology W) :
    ∀ j, stageDescendedQcqsObjects X c (U j).left := by
  classical
  let D₀ : Iᵒᵖ ⥤ Scheme.{u} := X.leftOp
  let C₀ : Cone D₀ := coneLeftOpOfCocone c
  let hC₀ : IsLimit C₀ := isLimitConeLeftOpOfCocone X hc
  let {j k : Iᵒᵖ} (a : j ⟶ k) : IsAffineHom (D₀.map a) :=
    inferInstanceAs (IsAffineHom (X.map a.unop).unop)
  let N : Scheme.FinitePresentationDescent.Model (C₀.π.app (op i)) W.hom :=
    M.finitePresentationModel
  let : IsAffine N.X := inferInstanceAs (IsAffine M.obj.left)
  let : Etale N.f := inferInstanceAs (Etale M.obj.hom)
  let D := Scheme.baseChangeDiagram D₀ (op i) N.f
  let e : W.left ≅ (Scheme.baseChangeCone D₀ C₀ (op i) N.f).pt := N.rawIso
  let C : Cone D := (Scheme.baseChangeCone D₀ C₀ (op i) N.f).extend e.hom
  let eC : Scheme.baseChangeCone D₀ C₀ (op i) N.f ≅ C :=
    Cone.extendIso (Scheme.baseChangeCone D₀ C₀ (op i) N.f) e.symm
  let hC : IsLimit C :=
    (Scheme.isLimitBaseChangeCone D₀ C₀ hC₀ (op i) N.f).ofIsoLimit eC
  have (k : Over (op i)) : IsAffine (D.obj k) := by
    change IsAffine (pullback (D₀.map k.hom) N.f)
    exact isAffine_of_isAffineHom (pullback.snd (D₀.map k.hom) N.f)
  let Y (j : J) : Over C.pt := Over.mk (U j).hom.left
  have (j : J) : IsAffine (Y j).left :=
    inferInstanceAs (IsAffine (U j).left.left)
  have (j : J) : Etale (Y j).hom := inferInstanceAs (Etale (U j).hom.left)
  have hsur : ∀ x : C.pt, ∃ j, ∃ y : (Y j).left, (Y j).hom y = x := by
    intro x
    have h := (Scheme.ofArrows_mem_smallEtaleTopology_iff (fun j => (U j).hom)).mp hcover
    have hx := Set.mem_univ x
    rw [← h] at hx
    change ∃ j, ∃ y : (U j).left.left, (U j).hom.left y = x
    simpa only [Set.mem_iUnion, Set.mem_range] using hx
  obtain ⟨k, _, Z, hZ, he, hm, _⟩ :=
    EtaleAffineBasis.exists_affineScheme_cover_model_above D C hC (Over.mk (𝟙 (op i))) Y hsur
  have (j : J) : IsAffine (Z j).left := hZ j
  have (j : J) : Etale (Z j).hom := he j
  let f : D.obj k ⟶ (X.obj k.left.unop).unop := pullback.fst (D₀.map k.hom) N.f
  have : Etale f := inferInstanceAs (Etale (pullback.fst (D₀.map k.hom) N.f))
  have H : IsPullback (C.π.app k) W.hom f (c.ι.app k.left.unop).unop := by
    apply (Scheme.isPullback_baseChangeCone D₀ C₀ (op i) N.f k).of_iso'
      e (Iso.refl _) (Iso.refl _) (Iso.refl _)
    · change C.π.app k = C.π.app k ≫ 𝟙 _
      exact (Category.comp_id _).symm
    · exact N.rawIso_hom_fst.trans (Category.comp_id W.hom).symm
    · change 𝟙 _ ≫ f = f ≫ 𝟙 _
      simp only [Category.id_comp, Category.comp_id]
    · change 𝟙 _ ≫ (c.ι.app k.left.unop).unop =
        (c.ι.app k.left.unop).unop ≫ 𝟙 _
      simp only [Category.id_comp, Category.comp_id]
  intro j
  let g : (Z j).left ⟶ D.obj k := (Z j).hom
  let : Etale g := he j
  let : QuasiCompact g := quasiCompact_of_compactSpace g
  let : QuasiSeparated g := QuasiSeparated.of_quasiSeparatedSpace g
  let A : Scheme.FinitePresentationDescent.Model (C.π.app k) (U j).hom.left :=
    Scheme.FinitePresentationDescent.Model.ofOverIso g (Classical.choice (hm j))
  have hA : IsPullback (P := (U j).left.left) (X := (Z j).left)
      (Y := W.left) (Z := D.obj k) A.p (U j).hom.left g (C.π.app k) := A.square
  have hH : IsPullback (P := W.left) (X := D.obj k) (Y := c.pt.unop)
      (Z := (X.obj k.left.unop).unop) (C.π.app k) W.hom f
      (c.ι.app k.left.unop).unop := H
  have hB : IsPullback (P := (U j).left.left) (X := (Z j).left)
      (Y := c.pt.unop) (Z := (X.obj k.left.unop).unop) A.p
      ((U j).hom.left ≫ W.hom) (g ≫ f) (c.ι.app k.left.unop).unop :=
    hA.paste_vert hH
  have hw : (U j).hom.left ≫ W.hom = (U j).left.hom :=
    MorphismProperty.Over.w (U j).hom
  rw [hw] at hB
  let B : Scheme.FinitePresentationDescent.Model
      (c.ι.app k.left.unop).unop (U j).left.hom :=
    { X := (Z j).left
      f := g ≫ f
      locallyOfFinitePresentation := inferInstance
      quasiCompact := inferInstance
      quasiSeparated := inferInstance
      p := A.p
      square := hB }
  have : Etale B.f := inferInstanceAs (Etale (g ≫ f))
  exact ⟨k.left.unop, ⟨ofFinitePresentation B⟩⟩

/-- An arbitrary original covering sieve on an affine modeled object contains
a finite supported affine covering family. All membership statements concern
the original sieve, not a replacement topology. -/
theorem exists_affine_supported_family {i : I} {W : c.pt.unop.Etale}
    (M : Model X c i W) [IsAffine M.obj.left]
    (R : Sieve W) (hR : R ∈ c.pt.unop.smallEtaleTopology W) :
    ∃ (J : Type u) (_ : Finite J) (U : J → Over W),
      (∀ j, stageDescendedQcqsObjects X c (U j).left) ∧
      Sieve.ofArrows (fun j => (U j).left) (fun j => (U j).hom) ∈
        c.pt.unop.smallEtaleTopology W ∧
      ∀ j, R (U j).hom := by
  let : CompactSpace W.left := (M.qcqs hc).1
  obtain ⟨J, hJ, V, f, hV, hf, hcov⟩ :=
    EtaleAffineBasis.exists_finite_affine_family W R hR
  let : Finite J := hJ
  let U : J → Over W := fun j => Over.mk (f j)
  have (j : J) : IsAffine (U j).left.left := hV j
  exact ⟨J, hJ, U, affine_cover_supported hc M U hcov, hcov, hf⟩

end AlgebraicGeometry.Scheme.EtaleCohomology.Continuity.StageSupport
