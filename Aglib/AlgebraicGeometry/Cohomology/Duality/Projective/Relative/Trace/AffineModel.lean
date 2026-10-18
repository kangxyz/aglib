/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.Cohomology.Duality.Projective.Relative.Trace.AffineModel.Identity
public import Aglib.AlgebraicGeometry.ProjectiveSpace.BaseChange.Affine

/-!
# Original affine polynomial-model higher-image comparisons

The actual affine Cartesian model and original higher-image restriction paste
with the native identity-restriction comparisons. The typed component retains
exactly the original natural-isomorphism arrow. The open-square equation uses
only the original restriction-pasting laws and has no trace, coefficient
flatness, coherence, Noetherianity or coordinate-order premise.
-/

@[expose] public section
noncomputable section
set_option autoImplicit false
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option Elab.async false
open CategoryTheory CategoryTheory.Limits CategoryTheory.Abelian HomologicalComplex
open AlgebraicGeometry AlgebraicGeometry.ProjectiveSpace AlgebraicGeometry.Scheme.Modules
open AlgebraicGeometry.Scheme.Modules.Differentials
universe u
attribute [local instance] AlgebraicGeometry.Scheme.Modules.standardHasDerivedCategory

namespace AlgebraicGeometry.Scheme.Cohomology.RelativeProjectiveTrace

variable (R : Type u) [CommRing R] (ι : Type u)
  {A B : Type u} [CommRing A] [CommRing B] {X W : Scheme.{u}}
  (a : X ⟶ ProjectiveSpace R ι) (p : X ⟶ Spec (.of A))
  (f : Spec (.of A) ⟶ Spec (.of R)) (h : IsPullback a p (toSpec R ι) f)

/-- The original inverse affine-model square over the identity base morphism. -/
theorem affineModelSquare :
    IsPullback (affinePullbackIso ι a p f h).inv (toSpec A ι) p (𝟙 (Spec (.of A))) :=
  IsPullback.of_horiz_isIso ⟨by simpa only [Category.comp_id] using
    (affinePullbackIso_inv_snd ι a p f h)⟩

/-- The original affine polynomial-model comparison, with both identity restrictions. -/
def affineModelHigherIso (n : ℕ) :
    relativeHigherFunctor p n ≅ relativeHigherFunctor (toSpec A ι) n :=
  Functor.isoWhiskerLeft (relativeHigherFunctor p n) restrictFunctorId.symm ≪≫
    relativeHigherRestrictionIso p (affinePullbackIso ι a p f h).inv (toSpec A ι)
      (𝟙 (Spec (.of A))) (affineModelSquare (A := A) (X := X) R ι a p f h) n ≪≫
    Functor.isoWhiskerRight restrictFunctorId
      (relativeHigherFunctor (toSpec A ι) n)
private theorem affineModelHigherIso_original (n : ℕ) :
    affineModelHigherIso R ι a p f h n =
      Functor.isoWhiskerLeft (relativeHigherFunctor p n) restrictFunctorId.symm ≪≫
        relativeHigherRestrictionIso p (affinePullbackIso ι a p f h).inv (toSpec A ι)
          (𝟙 (Spec (.of A))) (IsPullback.of_horiz_isIso
            ⟨by simpa only [Category.comp_id] using
              (affinePullbackIso_inv_snd ι a p f h)⟩) n ≪≫
        Functor.isoWhiskerRight restrictFunctorId (relativeHigherFunctor (toSpec A ι) n) := by
  rfl

/-- The same comparison as an explicitly typed composite of its original three arrows. -/
def affineModelHigherHom (n : ℕ) (N : (Spec (.of A)).Modules) :
    (relativeHigherFunctor p n).obj N ⟶
      (relativeHigherFunctor (toSpec A ι) n).obj N := by
  let E : X ≅ ProjectiveSpace A ι := affinePullbackIso ι a p f h
  let HE : IsPullback E.inv (toSpec A ι) p (𝟙 (Spec (.of A))) :=
    affineModelSquare (A := A) (X := X) R ι a p f h
  let F₀ : (Spec (.of A)).Modules ⥤ (Spec (.of A)).Modules := relativeHigherFunctor p n
  let F₁ : (Spec (.of A)).Modules ⥤ (Spec (.of A)).Modules :=
    relativeHigherFunctor (toSpec A ι) n
  let N₀ : (Spec (.of A)).Modules := F₀.obj N
  let N₁ : (Spec (.of A)).Modules := N₀.restrict (𝟙 (Spec (.of A)))
  let N₂ : (Spec (.of A)).Modules := F₁.obj (N.restrict (𝟙 (Spec (.of A))))
  let N₃ : (Spec (.of A)).Modules := F₁.obj N
  let d₀ : N₀ ⟶ N₁ := (restrictFunctorId (X := Spec (.of A))).inv.app N₀
  let d₁ : N₁ ⟶ N₂ :=
    relativeHigherRestrictionHom p E.inv (toSpec A ι) (𝟙 (Spec (.of A))) HE n N
  let d₂ : N₂ ⟶ N₃ := F₁.map
    (X := N.restrict (𝟙 (Spec (.of A)))) (Y := N)
    ((restrictFunctorId (X := Spec (.of A))).hom.app N)
  exact @CategoryStruct.comp (Spec (.of A)).Modules inferInstance N₀ N₁ N₃ d₀
    (@CategoryStruct.comp (Spec (.of A)).Modules inferInstance N₁ N₂ N₃ d₁ d₂)
/-- The typed arrow is exactly the original natural-isomorphism component. -/
theorem affineModelHigherHom_eq (n : ℕ) (N : (Spec (.of A)).Modules) :
    affineModelHigherHom R ι a p f h n N = (affineModelHigherIso R ι a p f h n).hom.app N := rfl

private theorem affineModelHigherIso_identity (n : ℕ) :
    let E : X ≅ ProjectiveSpace A ι := affinePullbackIso ι a p f h
    let HE : IsPullback E.inv (toSpec A ι) p (𝟙 (Spec (.of A))) :=
      affineModelSquare (A := A) (X := X) R ι a p f h
    affineModelHigherIso (A := A) (X := X) R ι a p f h n =
      identityHigherModelIso (Y := Spec (.of A)) p E.inv (toSpec A ι) HE n := by
  rfl

private theorem identityHigherModelIso_open_nat
    {X₀ X₁ V₀ V₁ Y₀ Y₁ : Scheme.{u}}
    (p₀ : X₀ ⟶ Y₀) (p₁ : X₁ ⟶ Y₁) (q₀ : V₀ ⟶ Y₀) (q₁ : V₁ ⟶ Y₁)
    (i : X₁ ⟶ X₀) (j : Y₁ ⟶ Y₀) (e₀ : V₀ ⟶ X₀) (e₁ : V₁ ⟶ X₁) (g : V₁ ⟶ V₀)
    [IsOpenImmersion i] [IsOpenImmersion j] [IsOpenImmersion e₀]
    [IsOpenImmersion e₁] [IsOpenImmersion g]
    (H : IsPullback i p₁ p₀ j) (H₀ : IsPullback e₀ q₀ p₀ (𝟙 Y₀))
    (H₁ : IsPullback e₁ q₁ p₁ (𝟙 Y₁)) (G : IsPullback g q₁ q₀ j)
    (w : e₁ ≫ i = g ≫ e₀) (n : ℕ) :
    relativeHigherRestrictionIso p₀ i p₁ j H n ≪≫
        Functor.isoWhiskerLeft (Modules.restrictFunctor j)
          (identityHigherModelIso p₁ e₁ q₁ H₁ n) =
      Functor.isoWhiskerRight (identityHigherModelIso p₀ e₀ q₀ H₀ n)
          (Modules.restrictFunctor j) ≪≫
        relativeHigherRestrictionIso q₀ g q₁ j G n := by
  apply Iso.ext
  apply NatTrans.ext
  funext N
  simpa only [Iso.trans_hom, NatTrans.comp_app,
    Functor.isoWhiskerLeft_hom, Functor.whiskerLeft_app,
    Functor.isoWhiskerRight_hom, Functor.whiskerRight_app] using
      identityHigherModelIso_open p₀ p₁ q₀ q₁ i j e₀ e₁ g H H₀ H₁ G w n N


/-- The original affine-model comparison commutes with open restriction before
evaluation at a coefficient. -/
theorem affineModelHigherIso_open_nat
    (i : W ⟶ X) (q : W ⟶ Spec (.of B)) (σ : A →+* B)
    [IsOpenImmersion i] [IsOpenImmersion (Spec.map (CommRingCat.ofHom σ))]
    (H : IsPullback i q p (Spec.map (CommRingCat.ofHom σ))) (n : ℕ) :
    letI : IsOpenImmersion (ProjectiveSpace.map σ ι) :=
      MorphismProperty.of_isPullback (ProjectiveSpace.isPullback_map σ ι).flip inferInstance
    let j : Spec (.of B) ⟶ Spec (.of A) := Spec.map (CommRingCat.ofHom σ)
    relativeHigherRestrictionIso p i q j H n ≪≫
        Functor.isoWhiskerLeft (Modules.restrictFunctor j)
          (affineModelHigherIso R ι (i ≫ a) q (j ≫ f) (H.paste_horiz h) n) =
      Functor.isoWhiskerRight (affineModelHigherIso R ι a p f h n)
          (Modules.restrictFunctor j) ≪≫
        relativeHigherRestrictionIso (toSpec A ι) (ProjectiveSpace.map σ ι) (toSpec B ι)
          j (ProjectiveSpace.isPullback_map σ ι) n := by
  let : IsOpenImmersion (ProjectiveSpace.map σ ι) :=
    MorphismProperty.of_isPullback (ProjectiveSpace.isPullback_map σ ι).flip inferInstance
  let j : Spec (.of B) ⟶ Spec (.of A) := Spec.map (CommRingCat.ofHom σ)
  let g : ProjectiveSpace B ι ⟶ ProjectiveSpace A ι := ProjectiveSpace.map σ ι
  let E : X ≅ ProjectiveSpace A ι := affinePullbackIso ι a p f h
  let E' : W ≅ ProjectiveSpace B ι :=
    affinePullbackIso ι (i ≫ a) q (j ≫ f) (H.paste_horiz h)
  have hw : E'.inv ≫ i = g ≫ E.inv := by
    apply h.hom_ext
    · change (affinePullbackIso ι (i ≫ a) q (j ≫ f) (H.paste_horiz h)).inv ≫ (i ≫ a) =
        g ≫ ((affinePullbackIso ι a p f h).inv ≫ a)
      rw [affinePullbackIso_inv_fst, affinePullbackIso_inv_fst]
      simp only [j, g, Spec.preimage_comp, Spec.preimage_map, CommRingCat.hom_comp,
        ProjectiveSpace.map_comp]
      rfl
    · change E'.inv ≫ (i ≫ p) = g ≫ (E.inv ≫ p)
      rw [H.w, ← Category.assoc E'.inv q j]
      change ((affinePullbackIso ι (i ≫ a) q (j ≫ f) (H.paste_horiz h)).inv ≫ q) ≫ j =
        g ≫ ((affinePullbackIso ι a p f h).inv ≫ p)
      rw [affinePullbackIso_inv_snd, affinePullbackIso_inv_snd]
      exact (ProjectiveSpace.map_toSpec σ ι).symm
  let HE : IsPullback E.inv (toSpec A ι) p (𝟙 (Spec (.of A))) :=
    affineModelSquare (A := A) (X := X) R ι a p f h
  let HE' : IsPullback E'.inv (toSpec B ι) q (𝟙 (Spec (.of B))) :=
    affineModelSquare (A := B) (X := W) R ι (i ≫ a) q (j ≫ f) (H.paste_horiz h)
  let κA : relativeHigherFunctor p n ≅ relativeHigherFunctor (toSpec A ι) n :=
    identityHigherModelIso (Y := Spec (.of A)) p E.inv (toSpec A ι) HE n
  let κB : relativeHigherFunctor q n ≅ relativeHigherFunctor (toSpec B ι) n :=
    identityHigherModelIso (Y := Spec (.of B)) q E'.inv (toSpec B ι) HE' n
  let P (KA : relativeHigherFunctor p n ≅ relativeHigherFunctor (toSpec A ι) n)
      (KB : relativeHigherFunctor q n ≅ relativeHigherFunctor (toSpec B ι) n) : Prop :=
    relativeHigherRestrictionIso p i q j H n ≪≫
        Functor.isoWhiskerLeft (Modules.restrictFunctor j) KB =
      Functor.isoWhiskerRight KA (Modules.restrictFunctor j) ≪≫
        relativeHigherRestrictionIso (toSpec A ι) g (toSpec B ι) j
          (ProjectiveSpace.isPullback_map σ ι) n
  have hA : affineModelHigherIso R ι a p f h n = κA := by
    have hh := affineModelHigherIso_identity (A := A) (X := X) R ι a p f h n
    dsimp only at hh
    simpa only [κA, E, HE] using hh
  have hB : affineModelHigherIso R ι (i ≫ a) q (j ≫ f) (H.paste_horiz h) n = κB := by
    have hh := affineModelHigherIso_identity (A := B) (X := W) R ι (i ≫ a) q
      (j ≫ f) (H.paste_horiz h) n
    dsimp only at hh
    simpa only [κB, E', HE'] using hh
  have hc : P κA κB := by
    exact identityHigherModelIso_open_nat
      (X₀ := X) (X₁ := W) (V₀ := ProjectiveSpace A ι) (V₁ := ProjectiveSpace B ι)
      (Y₀ := Spec (.of A)) (Y₁ := Spec (.of B))
      p q (toSpec A ι) (toSpec B ι) i j E.inv E'.inv g H HE HE'
      (ProjectiveSpace.isPullback_map σ ι) hw n
  have hOld : P (affineModelHigherIso R ι a p f h n)
      (affineModelHigherIso R ι (i ≫ a) q (j ≫ f) (H.paste_horiz h) n) := by
    apply (congrArg₂ P hA hB).mpr
    exact hc
  simpa only [P, j, g] using hOld

/-- The original affine model comparison commutes with every supplied Cartesian open square. -/
theorem affineModelHigherIso_open
    (i : W ⟶ X) (q : W ⟶ Spec (.of B)) (σ : A →+* B)
    [IsOpenImmersion i] [IsOpenImmersion (Spec.map (CommRingCat.ofHom σ))]
    (H : IsPullback i q p (Spec.map (CommRingCat.ofHom σ)))
    (n : ℕ) (N : (Spec (.of A)).Modules) :
    letI : IsOpenImmersion (ProjectiveSpace.map σ ι) :=
      MorphismProperty.of_isPullback (ProjectiveSpace.isPullback_map σ ι).flip inferInstance
    let baseOpen := Spec.map (CommRingCat.ofHom σ)
    let sourceModule : (Spec (.of B)).Modules :=
      ((relativeHigherFunctor p n).obj N).restrict baseOpen
    let leftMiddle : (Spec (.of B)).Modules :=
      (relativeHigherFunctor q n).obj (N.restrict baseOpen)
    let rightMiddle : (Spec (.of B)).Modules :=
      ((relativeHigherFunctor (toSpec A ι) n).obj N).restrict baseOpen
    let targetModule : (Spec (.of B)).Modules :=
      (relativeHigherFunctor (toSpec B ι) n).obj (N.restrict baseOpen)
    let restrictionArrow : sourceModule ⟶ leftMiddle :=
      relativeHigherRestrictionHom p i q baseOpen H n N
    let modelArrow : leftMiddle ⟶ targetModule :=
      affineModelHigherHom R ι (i ≫ a) q (baseOpen ≫ f)
        (H.paste_horiz h) n (N.restrict baseOpen)
    let baseModelArrow : sourceModule ⟶ rightMiddle :=
      (Modules.restrictFunctor baseOpen).map
        (X := (relativeHigherFunctor p n).obj N)
        (Y := (relativeHigherFunctor (toSpec A ι) n).obj N)
        (affineModelHigherHom R ι a p f h n N)
    let nativeRestrictionArrow : rightMiddle ⟶ targetModule :=
      relativeHigherRestrictionHom (toSpec A ι) (ProjectiveSpace.map σ ι) (toSpec B ι)
        baseOpen (ProjectiveSpace.isPullback_map σ ι) n N
    let leftArrow : sourceModule ⟶ targetModule :=
      @CategoryStruct.comp (Spec (.of B)).Modules inferInstance
        sourceModule leftMiddle targetModule restrictionArrow modelArrow
    let rightArrow : sourceModule ⟶ targetModule :=
      @CategoryStruct.comp (Spec (.of B)).Modules inferInstance
        sourceModule rightMiddle targetModule baseModelArrow nativeRestrictionArrow
    @Eq (sourceModule ⟶ targetModule) leftArrow rightArrow := by
  let : IsOpenImmersion (ProjectiveSpace.map σ ι) :=
    MorphismProperty.of_isPullback (ProjectiveSpace.isPullback_map σ ι).flip inferInstance
  let j : Spec (.of B) ⟶ Spec (.of A) := Spec.map (CommRingCat.ofHom σ)
  let sourceFunctor : (Spec (.of A)).Modules ⥤ (Spec (.of B)).Modules :=
    relativeHigherFunctor p n ⋙ Modules.restrictFunctor j
  let targetFunctor : (Spec (.of A)).Modules ⥤ (Spec (.of B)).Modules :=
    Modules.restrictFunctor j ⋙ relativeHigherFunctor (toSpec B ι) n
  have hNat := affineModelHigherIso_open_nat R ι a p f h i q σ H n
  have hEval := congrArg
    (fun η : sourceFunctor ≅ targetFunctor => η.hom.app N) hNat
  simpa only [affineModelHigherHom_eq, relativeHigherRestrictionHom,
    Iso.trans_hom, NatTrans.comp_app, Functor.isoWhiskerLeft_hom,
    Functor.whiskerLeft_app, Functor.isoWhiskerRight_hom,
    Functor.whiskerRight_app, sourceFunctor, targetFunctor, j, Functor.comp_obj] using hEval

end AlgebraicGeometry.Scheme.Cohomology.RelativeProjectiveTrace
