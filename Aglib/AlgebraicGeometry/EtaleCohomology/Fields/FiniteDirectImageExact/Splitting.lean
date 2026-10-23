/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.EtaleCohomology.Fields.FiniteEtaleTransfer.Gluing
public import Aglib.AlgebraicGeometry.EtaleCohomology.H1.EtaleRestriction
public import Aglib.AlgebraicGeometry.Sites.EtaleCoproductSections

/-! # Literal component maps on a finite-etale splitting chart -/

@[expose] public noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true

open CategoryTheory CategoryTheory.Limits Opposite
open AlgebraicGeometry.Scheme.FiniteEtale

universe u

namespace AlgebraicGeometry.Scheme.EtaleCohomology.Fields.FiniteDirectImage

variable {X : Scheme.{u}} (Y : Scheme.FiniteEtale X)
  {V : X.Etale} {A : FintypeCat.{u}}
  (e : (trivialCoverFunctor V.left).obj A ≅ (baseChange V.hom).obj Y)

/-- The original component map from the splitting chart into the finite cover. -/
abbrev splitComponent (a : A) : V.left ⟶ Y.obj.left := (chartSiteSection Y e a).left

@[reassoc] theorem splitComponent_w (a : A) :
    splitComponent Y e a ≫ Y.obj.hom = V.hom :=
  MorphismProperty.Over.w (chartSiteSection Y e a)

instance splitComponent_etale (a : A) : Etale (splitComponent Y e a) := by
  infer_instance

/-- An original test over the splitting chart, viewed through its component. -/
abbrev componentTest (U : V.left.Etale) (a : A) : Y.obj.left.Etale :=
  (siteEtalePostcompose (splitComponent Y e a)).obj U

/-- The exact test at which the original direct image is evaluated. -/
abbrev pullbackTest (U : V.left.Etale) : Y.obj.left.Etale :=
  (siteBaseChange Y.obj.hom).obj ((siteEtalePostcompose V.hom).obj U)

/-- Actual inclusion of a split component into that original pullback test. -/
def componentTestInclusion (U : V.left.Etale) (a : A) :
    componentTest Y e U a ⟶ pullbackTest Y U :=
  MorphismProperty.Over.homMk
    (pullback.lift (𝟙 U.left) (U.hom ≫ splitComponent Y e a) (by
      change 𝟙 U.left ≫ (U.hom ≫ V.hom) = (U.hom ≫ splitComponent Y e a) ≫ Y.obj.hom
      rw [Category.id_comp, Category.assoc, splitComponent_w]))
    (pullback.lift_snd _ _ _)

@[reassoc] theorem componentTestInclusion_fst (U : V.left.Etale) (a : A) :
    (componentTestInclusion Y e U a).left ≫
      pullback.fst (U.hom ≫ V.hom) Y.obj.hom = 𝟙 U.left := by
  exact pullback.lift_fst _ _ _

@[reassoc] theorem componentTestInclusion_snd (U : V.left.Etale) (a : A) :
    (componentTestInclusion Y e U a).left ≫
      pullback.snd (U.hom ≫ V.hom) Y.obj.hom = U.hom ≫ splitComponent Y e a := by
  exact pullback.lift_snd _ _ _

private theorem projection_naturality
    {S T B Z : Scheme.{u}} (p : Z ⟶ B) (s : S ⟶ B) (t : T ⟶ B)
    (g : S ⟶ T) (lS : S ⟶ pullback s p) (lT : T ⟶ pullback t p)
    (m : pullback s p ⟶ pullback t p) (cS : S ⟶ Z) (cT : T ⟶ Z)
    (hS₁ : lS ≫ pullback.fst s p = 𝟙 S)
    (hS₂ : lS ≫ pullback.snd s p = cS)
    (hT₁ : lT ≫ pullback.fst t p = 𝟙 T)
    (hT₂ : lT ≫ pullback.snd t p = cT)
    (hm₁ : m ≫ pullback.fst t p = pullback.fst s p ≫ g)
    (hm₂ : m ≫ pullback.snd t p = pullback.snd s p)
    (hc : g ≫ cT = cS) : g ≫ lT = lS ≫ m := by
  apply pullback.hom_ext
  · calc
      (g ≫ lT) ≫ pullback.fst t p = g := by rw [Category.assoc, hT₁, Category.comp_id]
      _ = (lS ≫ pullback.fst s p) ≫ g := by rw [hS₁, Category.id_comp]
      _ = (lS ≫ m) ≫ pullback.fst t p :=
        (Category.assoc lS (pullback.fst s p) g).trans
          ((Category.assoc lS m (pullback.fst t p)).trans
            (congrArg (fun h => lS ≫ h) hm₁)).symm
  · calc
      (g ≫ lT) ≫ pullback.snd t p = cS := by rw [Category.assoc, hT₂, hc]
      _ = (lS ≫ m) ≫ pullback.snd t p := by rw [Category.assoc, hm₂, hS₂]

@[reassoc] theorem componentTestInclusion_naturality
    {U W : V.left.Etale} (g : U ⟶ W) (a : A) :
    (siteEtalePostcompose (splitComponent Y e a)).map g ≫ componentTestInclusion Y e W a =
      componentTestInclusion Y e U a ≫
        (siteBaseChange Y.obj.hom).map ((siteEtalePostcompose V.hom).map g) := by
  apply MorphismProperty.Over.Hom.ext
  rw [MorphismProperty.Comma.comp_left, MorphismProperty.Comma.comp_left]
  let t := (siteBaseChange Y.obj.hom).map ((siteEtalePostcompose V.hom).map g)
  have ht₁ : t.left ≫ pullback.fst (W.hom ≫ V.hom) Y.obj.hom =
      pullback.fst (U.hom ≫ V.hom) Y.obj.hom ≫ g.left := by
    exact pullback.lift_fst _ _ _
  have ht₂ : t.left ≫ pullback.snd (W.hom ≫ V.hom) Y.obj.hom =
      pullback.snd (U.hom ≫ V.hom) Y.obj.hom := by
    exact pullback.lift_snd _ _ _
  change g.left ≫ (componentTestInclusion Y e W a).left =
    (componentTestInclusion Y e U a).left ≫ t.left
  exact projection_naturality Y.obj.hom (U.hom ≫ V.hom) (W.hom ≫ V.hom)
    g.left (componentTestInclusion Y e U a).left (componentTestInclusion Y e W a).left
    t.left (U.hom ≫ splitComponent Y e a) (W.hom ≫ splitComponent Y e a)
    (componentTestInclusion_fst Y e U a) (componentTestInclusion_snd Y e U a)
    (componentTestInclusion_fst Y e W a) (componentTestInclusion_snd Y e W a)
    ht₁ ht₂ ((Category.assoc _ _ _).symm.trans
      (congrArg (fun h => h ≫ splitComponent Y e a) (MorphismProperty.Over.w g)))

/-- The component inclusions are the literal underlying coproduct isomorphism. -/
theorem componentTestInclusion_isIso (U : V.left.Etale) :
    IsIso (Sigma.desc (fun a => (componentTestInclusion Y e U a).left)) := by
  let W : X.Etale := (siteEtalePostcompose V.hom).obj U
  let g : W ⟶ V := MorphismProperty.Over.homMk U.hom rfl
  let eU := restrictChartSplitting Y g e
  let d : (∐ fun _ : A => U.left) ≅ pullback W.hom Y.obj.hom :=
    (trivialCoverSigmaIso U.left A).symm ≪≫
      (forgetToScheme U.left).mapIso eU ≪≫ pullbackSymmetry Y.obj.hom W.hom
  have hd : Sigma.desc (fun a => (componentTestInclusion Y e U a).left) = d.hom := by
    apply Sigma.hom_ext
    intro a
    rw [Sigma.ι_comp_desc]
    have hι : Sigma.ι (fun _ : A => U.left) a ≫ (trivialCoverSigmaIso U.left A).inv =
        (trivialCoverι U.left A a).hom.left := by
      apply (cancel_mono (trivialCoverSigmaIso U.left A).hom).mp
      simp only [Category.assoc, Iso.inv_hom_id, Category.comp_id, trivialCoverSigmaIso_ι]
    have hd₁ : (Sigma.ι (fun _ : A => U.left) a ≫ d.hom) ≫
        pullback.fst W.hom Y.obj.hom = 𝟙 U.left := by
      change (Sigma.ι (fun _ : A => U.left) a ≫
        ((trivialCoverSigmaIso U.left A).inv ≫ eU.hom.hom.left ≫
          (pullbackSymmetry Y.obj.hom W.hom).hom)) ≫
            pullback.fst W.hom Y.obj.hom = _
      simp only [Category.assoc, pullbackSymmetry_hom_comp_fst]
      rw [← Category.assoc, hι]
      exact (congrArg (fun h => (trivialCoverι U.left A a).hom.left ≫ h)
        (Over.w eU.hom.hom)).trans (trivialCoverι_struct U.left A a)
    have hd₂ : (Sigma.ι (fun _ : A => U.left) a ≫ d.hom) ≫
        pullback.snd W.hom Y.obj.hom = U.hom ≫ splitComponent Y e a := by
      change (Sigma.ι (fun _ : A => U.left) a ≫
        ((trivialCoverSigmaIso U.left A).inv ≫ eU.hom.hom.left ≫
          (pullbackSymmetry Y.obj.hom W.hom).hom)) ≫
            pullback.snd W.hom Y.obj.hom = _
      simp only [Category.assoc, pullbackSymmetry_hom_comp_snd]
      rw [← Category.assoc, hι]
      exact congrArg (fun h => h.left) (chartSiteSection_restrict Y g e a)
    exact pullback.hom_ext
      ((componentTestInclusion_fst Y e U a).trans hd₁.symm)
      ((componentTestInclusion_snd Y e U a).trans hd₂.symm)
  rw [hd]
  infer_instance

end AlgebraicGeometry.Scheme.EtaleCohomology.Fields.FiniteDirectImage
