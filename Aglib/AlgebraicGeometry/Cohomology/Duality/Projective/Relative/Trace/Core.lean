/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module
public import Aglib.AlgebraicGeometry.Cohomology.Duality.Projective.Relative.AffineTrace
public import Aglib.AlgebraicGeometry.Cohomology.Duality.Projective.Relative.Trace.Restriction
public import Aglib.AlgebraicGeometry.Cohomology.Duality.Projective.Relative.Trace.Sections
public import Aglib.AlgebraicGeometry.Cohomology.Duality.Projective.Relative.Trace.Descent
public import Aglib.AlgebraicGeometry.Cohomology.Duality.Projective.Relative.Trace.CoefficientMap
public import Aglib.AlgebraicGeometry.Cohomology.Duality.Projective.Relative.Trace.AffineModel
public import Aglib.AlgebraicGeometry.Cohomology.Duality.Projective.Relative.Trace.Residue
public import Aglib.AlgebraicGeometry.Cohomology.Duality.Projective.Relative.Trace.Local
public import Aglib.AlgebraicGeometry.Cohomology.Duality.Projective.Relative.Trace.Gluing
public import Aglib.AlgebraicGeometry.Cohomology.Duality.Projective.Relative.Trace.Pullback
public import Aglib.AlgebraicGeometry.ProjectiveSpace.BaseChange.Affine
public import Aglib.AlgebraicGeometry.Modules.LocallyFree.Locality
public import Aglib.AlgebraicGeometry.Modules.QuasiCoherent.Tensor
public import Aglib.AlgebraicGeometry.Modules.QuasiCoherent.Pullback
public import Aglib.AlgebraicGeometry.Cohomology.Projective.Projection.Amplitude
public import Aglib.AlgebraicGeometry.Cohomology.DirectImage.Affine.Cohomology.Restriction
public import Aglib.AlgebraicGeometry.Cohomology.DirectImage.Affine.Cohomology.Naturality
public import Aglib.AlgebraicGeometry.Cohomology.DirectImage.Restriction.Composition
public import Aglib.AlgebraicGeometry.Modules.InternalHom.Gluing
public import Aglib.AlgebraicGeometry.Modules.BaseChange.Affine.Locality
public import Aglib.AlgebraicGeometry.Modules.IsomorphismFunctors
public import Mathlib.AlgebraicGeometry.Morphisms.Separated
public import Aglib.Algebra.Homology.DerivedCategory.TStructure.HomToSingle
/-!
# The original normalized relative projective trace
For a supplied Cartesian polynomial projective space over a separated scheme, the
original affine residue trace glues as an ordinary top higher-direct-image morphism.
The native upper bound and top-Hom equivalence lift that morphism to the actual
bounded-below derived direct image followed by its full-category inclusion.
All coefficient and open comparisons are the original ones. Quasicoherent coefficients
are arbitrary; no Noetherianity or coefficient flatness is assumed.
-/
@[expose] public section
noncomputable section
set_option autoImplicit false
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
-- Check the long native component conversions sequentially to bound peak memory.
set_option Elab.async false
open CategoryTheory CategoryTheory.Limits CategoryTheory.Abelian HomologicalComplex
open AlgebraicGeometry AlgebraicGeometry.ProjectiveSpace AlgebraicGeometry.Scheme.Modules
open AlgebraicGeometry.Scheme.Modules.Differentials
open AlgebraicGeometry.Scheme.Cohomology.RelativeProjectiveTrace
universe u
attribute [local instance] AlgebraicGeometry.Scheme.Modules.standardHasDerivedCategory
attribute [local instance] AlgebraicGeometry.Scheme.Cohomology.projectiveCoefficientTraceTarget
namespace AlgebraicGeometry.Scheme.Cohomology
variable (R : Type u) [CommRing R] (ι : Type u)
  {X Y : Scheme.{u}} (a : X ⟶ ProjectiveSpace R ι) (p : X ⟶ Y)
  (f : Y ⟶ Spec (.of R)) (h : IsPullback a p (ProjectiveSpace.toSpec R ι) f)
  (n : ℕ) (e : ι ≃ Fin (n + 1))
include h e in
private theorem differentialTop_affineRestriction_finiteLocallyFree
    {A : CommRingCat.{u}} {W : Scheme.{u}} (i : W ⟶ X) (q : W ⟶ Spec A)
    (j : Spec A ⟶ Y) [IsOpenImmersion i] [IsOpenImmersion j]
    (H : IsPullback i q p j) :
    IsFiniteLocallyFree W
      ((moduleExteriorPower X (relativeDifferentialSheaf p) n).restrict i) := by
  let : Fintype ι := Fintype.ofEquiv (Fin (n + 1)) e.symm
  let E := ProjectiveSpace.affinePullbackIso ι (i ≫ a) q (j ≫ f) (H.paste_horiz h)
  let : IsFiniteLocallyFree (ProjectiveSpace A ι)
      (moduleExteriorPower (ProjectiveSpace A ι)
        (relativeDifferentialSheaf (ProjectiveSpace.toSpec A ι)) n) :=
    finiteLocallyFree_of_iso (differentialResidueTwistingIso A ι n e).symm
  let g : (moduleExteriorPower (ProjectiveSpace A ι)
      (relativeDifferentialSheaf (ProjectiveSpace.toSpec A ι)) n).restrict E.hom ≅
      moduleExteriorPower W (relativeDifferentialSheaf q) n :=
    relativeTopDifferentialRestrictionIso (ProjectiveSpace.toSpec A ι) E.hom q (𝟙 (Spec A))
      (by simpa only [Category.comp_id] using
        ProjectiveSpace.affinePullbackIso_hom_toSpec ι (i ≫ a) q (j ≫ f) (H.paste_horiz h)) n
  let : IsFiniteLocallyFree W (moduleExteriorPower W (relativeDifferentialSheaf q) n) :=
    finiteLocallyFree_of_iso g
  exact finiteLocallyFree_of_iso (relativeTopDifferentialRestrictionIso p i q j H.w n).symm
include h e in
/-- The actual relative top differential sheaf is finite locally free on every base change. -/
theorem relativeProjectiveDifferentialTop_finiteLocallyFree :
    IsFiniteLocallyFree X (moduleExteriorPower X (relativeDifferentialSheaf p) n) := by
  let C := Y.affineOpenCover.openCover.pullback₁ p
  apply finiteLocallyFree_of_schemeOpenCover _ C
  intro k
  change IsFiniteLocallyFree (pullback p (Y.affineOpenCover.f k))
    ((moduleExteriorPower X (relativeDifferentialSheaf p) n).restrict
      (pullback.fst p (Y.affineOpenCover.f k)))
  exact differentialTop_affineRestriction_finiteLocallyFree R ι a p f h n e
    (pullback.fst p (Y.affineOpenCover.f k))
    (pullback.snd p (Y.affineOpenCover.f k)) (Y.affineOpenCover.f k)
    (IsPullback.of_hasPullback p (Y.affineOpenCover.f k))
include h e in
/-- Arbitrary quasicoherent coefficients give an actual quasicoherent differential coefficient. -/
theorem relativeProjectiveDifferentialCoefficients_isQuasicoherent
    (N : Y.Modules) [N.IsQuasicoherent] :
    ((relativeTopDifferentialCoefficientsFunctor p n).obj N).IsQuasicoherent := by
  let := relativeProjectiveDifferentialTop_finiteLocallyFree R ι a p f h n e
  exact isQuasicoherent_moduleTensorLeftFunctor
    (moduleExteriorPower X (relativeDifferentialSheaf p) n) ((Scheme.Modules.pullback p).obj N)
/-- The literal installed derived direct image followed by the full-category inclusion. -/
private abbrev relativeTopDifferentialCoefficientsDerived (N : Y.Modules) :
    DerivedCategory Y.Modules :=
  DerivedCategory.Plus.ι.obj
    ((Scheme.Modules.derivedPushforwardPlus p).obj
      ((DerivedCategory.Plus.singleFunctor X.Modules 0).obj
        ((relativeTopDifferentialCoefficientsFunctor p n).obj N)))
include h e in
/-- The actual differential-coefficient direct image has the original upper bound n. -/
theorem relativeProjectiveDifferentialCoefficientsDerived_isLE (N : Y.Modules) [N.IsQuasicoherent] :
    (DerivedCategory.Plus.ι.obj ((Scheme.Modules.derivedPushforwardPlus p).obj
      ((DerivedCategory.Plus.singleFunctor X.Modules 0).obj
        ((relativeTopDifferentialCoefficientsFunctor p n).obj N)))).IsLE (n : ℤ) := by
  let := relativeProjectiveDifferentialCoefficients_isQuasicoherent R ι a p f h n e N
  rw [DerivedCategory.Plus.isLE_ι_obj_iff]
  exact projectiveProjection_derivedSingle_zero_isLE R ι a p f h n e _
end AlgebraicGeometry.Scheme.Cohomology
namespace AlgebraicGeometry.Scheme.Cohomology
open AlgebraicGeometry.Scheme.Modules.Differentials
private def affineTraceModuleIso {A : CommRingCat.{u}} {M N : (Spec A).Modules}
    [M.IsQuasicoherent] [N.IsQuasicoherent]
    (E : moduleSpecΓFunctor.obj M ≅ moduleSpecΓFunctor.obj N) : M ≅ N :=
  (asIso M.fromTildeΓ).symm ≪≫ (tilde.functor A).mapIso E ≪≫ asIso N.fromTildeΓ
private theorem affineTraceModuleIso_sections {A : CommRingCat.{u}} {M N : (Spec A).Modules}
    [M.IsQuasicoherent] [N.IsQuasicoherent]
    (E : moduleSpecΓFunctor.obj M ≅ moduleSpecΓFunctor.obj N) :
    moduleSpecΓFunctor.map (affineTraceModuleIso E).hom = E.hom := by
  let η := (tilde.toTildeΓNatIso (R := A)).hom
  have hM : η.app (moduleSpecΓFunctor.obj M) ≫ moduleSpecΓFunctor.map M.fromTildeΓ = 𝟙 _ :=
    (tilde.adjunction (R := A)).right_triangle_components M
  have hN : η.app (moduleSpecΓFunctor.obj N) ≫ moduleSpecΓFunctor.map N.fromTildeΓ = 𝟙 _ :=
    (tilde.adjunction (R := A)).right_triangle_components N
  have hMi : moduleSpecΓFunctor.map (asIso M.fromTildeΓ).inv =
      η.app (moduleSpecΓFunctor.obj M) := by
    apply (cancel_mono (moduleSpecΓFunctor.map M.fromTildeΓ)).mp
    rw [← Functor.map_comp]
    simpa using hM.symm
  change moduleSpecΓFunctor.map
    ((asIso M.fromTildeΓ).inv ≫ tilde.map E.hom ≫ N.fromTildeΓ) = _
  have hn : E.hom ≫ η.app (moduleSpecΓFunctor.obj N) =
      η.app (moduleSpecΓFunctor.obj M) ≫ moduleSpecΓFunctor.map (tilde.map E.hom) :=
    η.naturality E.hom
  rw [Functor.map_comp, Functor.map_comp, hMi, ← Category.assoc, ← hn, Category.assoc, hN]
  exact Category.comp_id E.hom
/-- The actual top differential coefficient on polynomial projective space is quasicoherent. -/
theorem projectiveTopDifferentialCoefficients_isQuasicoherent (A : Type u) [CommRing A] (ι : Type u)
    (n : ℕ) (e : ι ≃ Fin (n + 1)) (N : (Spec (.of A)).Modules) [N.IsQuasicoherent] :
    ((relativeTopDifferentialCoefficientsFunctor (toSpec A ι) n).obj N).IsQuasicoherent := by
  let H : IsPullback (𝟙 (ProjectiveSpace A ι)) (toSpec A ι) (toSpec A ι)
      (𝟙 (Spec (.of A))) := IsPullback.of_horiz_isIso ⟨by simp⟩
  exact relativeProjectiveDifferentialCoefficients_isQuasicoherent A ι _ _ _ H n e N
private def standardAffineTraceIso (R : Type u) [CommRing R] (ι : Type u)
    (n : ℕ) (e : ι ≃ Fin (n + 1)) (N : (Spec (.of R)).Modules) [N.IsQuasicoherent] :
    (((Scheme.Modules.pushforward (toSpec R ι)).rightDerived n).obj
      ((relativeTopDifferentialCoefficientsFunctor (toSpec R ι) n).obj N)) ≅ N := by
  let : Fintype ι := Fintype.ofEquiv (Fin (n + 1)) e.symm
  let := projectiveTopDifferentialCoefficients_isQuasicoherent R ι n e N
  let : ((((Scheme.Modules.pushforward (toSpec R ι)).rightDerived n).obj
      ((relativeTopDifferentialCoefficientsFunctor (toSpec R ι) n).obj N))).IsQuasicoherent :=
    moduleHigherDirectImage_isQuasicoherent (toSpec R ι)
      ((relativeTopDifferentialCoefficientsFunctor (toSpec R ι) n).obj N) n
  exact affineTraceModuleIso
    ((moduleHigherDirectImageAffineSectionsLinearEquiv (toSpec R ι) _
      (injectiveResolution _) n).trans
        (projectiveAffineDifferentialTraceLinearEquiv R ι n e N)).toModuleIso
private def standardAffineTraceHom (R : Type u) [CommRing R] (ι : Type u)
    (n : ℕ) (e : ι ≃ Fin (n + 1)) (N : (Spec (.of R)).Modules) [N.IsQuasicoherent] :
    (((Scheme.Modules.pushforward (toSpec R ι)).rightDerived n).obj
      ((relativeTopDifferentialCoefficientsFunctor (toSpec R ι) n).obj N)) ⟶ N :=
  (show (((Scheme.Modules.pushforward (toSpec R ι)).rightDerived n).obj
      ((relativeTopDifferentialCoefficientsFunctor (toSpec R ι) n).obj N)) ≅ N from
    standardAffineTraceIso R ι n e N).hom
private theorem standardAffineTraceHom_eq (R : Type u) [CommRing R] (ι : Type u)
    (n : ℕ) (e : ι ≃ Fin (n + 1)) (N : (Spec (.of R)).Modules) [N.IsQuasicoherent] :
    standardAffineTraceHom R ι n e N = (standardAffineTraceIso R ι n e N).hom := rfl
set_option maxRecDepth 2000 in
-- The concrete affine-section linear equivalences require deeper native type conversion.
private theorem standardAffineTraceIso_sections (R : Type u) [CommRing R] (ι : Type u)
    (n : ℕ) (e : ι ≃ Fin (n + 1)) (N : (Spec (.of R)).Modules) [N.IsQuasicoherent] :
    letI : Fintype ι := Fintype.ofEquiv (Fin (n + 1)) e.symm
    letI := projectiveTopDifferentialCoefficients_isQuasicoherent R ι n e N
    affineTraceSectionsEquation (toSpec R ι)
      ((relativeTopDifferentialCoefficientsFunctor (toSpec R ι) n).obj N) N n
      (standardAffineTraceIso R ι n e N).hom
      (fun c => projectiveAffineDifferentialTraceLinearEquiv R ι n e N c) := by
  let : Fintype ι := Fintype.ofEquiv (Fin (n + 1)) e.symm
  let := projectiveTopDifferentialCoefficients_isQuasicoherent R ι n e N
  intro x
  let M := (relativeTopDifferentialCoefficientsFunctor (toSpec R ι) n).obj N
  let : (((Scheme.Modules.pushforward (toSpec R ι)).rightDerived n).obj M).IsQuasicoherent :=
    moduleHigherDirectImage_isQuasicoherent (toSpec R ι) M n
  let E := ((moduleHigherDirectImageAffineSectionsLinearEquiv (toSpec R ι) M
    (injectiveResolution M) n).trans
      (projectiveAffineDifferentialTraceLinearEquiv R ι n e N)).toModuleIso
  change moduleSpecΓFunctor.map (affineTraceModuleIso E).hom x = E.hom x
  exact ConcreteCategory.congr_hom (affineTraceModuleIso_sections E) x
private theorem standardAffineTraceHom_sections (R : Type u) [CommRing R] (ι : Type u)
    (n : ℕ) (e : ι ≃ Fin (n + 1)) (N : (Spec (.of R)).Modules) [N.IsQuasicoherent] :
    letI : Fintype ι := Fintype.ofEquiv (Fin (n + 1)) e.symm
    letI := projectiveTopDifferentialCoefficients_isQuasicoherent R ι n e N
    affineTraceSectionsEquation (toSpec R ι)
      ((relativeTopDifferentialCoefficientsFunctor (toSpec R ι) n).obj N) N n
      (standardAffineTraceHom R ι n e N)
      (fun c => projectiveAffineDifferentialTraceLinearEquiv R ι n e N c) := by
  let : Fintype ι := Fintype.ofEquiv (Fin (n + 1)) e.symm
  let := projectiveTopDifferentialCoefficients_isQuasicoherent R ι n e N
  exact (congrArg
    (fun k => affineTraceSectionsEquation (toSpec R ι)
      ((relativeTopDifferentialCoefficientsFunctor (toSpec R ι) n).obj N) N n k
      (fun c => projectiveAffineDifferentialTraceLinearEquiv R ι n e N c))
    (standardAffineTraceHom_eq R ι n e N)).mpr
      (standardAffineTraceIso_sections R ι n e N)
set_option maxRecDepth 2000 in
-- The concrete affine coefficient naturality transports exceed the default elaborator stack.
private theorem standardAffineTraceIso_naturality (R : Type u) [CommRing R] (ι : Type u)
    (n : ℕ) (e : ι ≃ Fin (n + 1))
    {N N' : (Spec (.of R)).Modules} [N.IsQuasicoherent] [N'.IsQuasicoherent] (s : N ⟶ N') :
    (relativeHigherFunctor (toSpec R ι) n).map s ≫
        (standardAffineTraceIso R ι n e N').hom =
      (standardAffineTraceIso R ι n e N).hom ≫ s := by
  let : Fintype ι := Fintype.ofEquiv (Fin (n + 1)) e.symm
  let := projectiveTopDifferentialCoefficients_isQuasicoherent R ι n e N
  let := projectiveTopDifferentialCoefficients_isQuasicoherent R ι n e N'
  let : ((relativeHigherFunctor (toSpec R ι) n).obj N).IsQuasicoherent :=
    moduleHigherDirectImage_isQuasicoherent (toSpec R ι)
      ((relativeTopDifferentialCoefficientsFunctor (toSpec R ι) n).obj N) n
  apply affineHom_ext
  ext x
  simp only [Functor.map_comp, ConcreteCategory.comp_apply]
  have h₁ := standardAffineTraceIso_sections R ι n e N'
    (moduleSpecΓFunctor.map ((relativeHigherFunctor (toSpec R ι) n).map s) x)
  have h₀ := standardAffineTraceIso_sections R ι n e N x
  change _ = _ at h₁ h₀
  erw [h₁, h₀]
  have hn := moduleHigherDirectImageAffineSectionsLinearEquiv_naturality (toSpec R ι)
    (injectiveResolution ((relativeTopDifferentialCoefficientsFunctor (toSpec R ι) n).obj N))
    (injectiveResolution ((relativeTopDifferentialCoefficientsFunctor (toSpec R ι) n).obj N'))
    (v := (relativeTopDifferentialCoefficientsFunctor (toSpec R ι) n).map s) n x
  change _ = _ at hn
  exact (congrArg (projectiveAffineDifferentialTraceLinearEquiv R ι n e N') hn).trans
    (projectiveAffineDifferentialTraceLinearEquiv_naturality R ι n e s _)
private theorem relativeHigherRestrictionHom_component
    {W X Z Y : Scheme.{u}} (p : X ⟶ Y) (i : W ⟶ X) (q : W ⟶ Z) (j : Z ⟶ Y)
    [IsOpenImmersion i] [IsOpenImmersion j] (H : IsPullback i q p j) (n : ℕ)
    (N : Y.Modules) :
    relativeHigherRestrictionHom p i q j H n N =
      (Scheme.Modules.higherDirectImageOpenRestrictionIso i q p j H n).hom.app
        ((relativeTopDifferentialCoefficientsFunctor p n).obj N) ≫
      ((Scheme.Modules.pushforward q).rightDerived n).map
        ((relativeTopDifferentialCoefficientsRestrictionIso p i q j H.w n).hom.app N) :=
  relativeHigherRestrictionIso_hom p i q j H n N
private theorem relativeHigherRestrictionHom_postcomp
    {W X Z Y : Scheme.{u}} (p : X ⟶ Y) (i : W ⟶ X) (q : W ⟶ Z) (j : Z ⟶ Y)
    [IsOpenImmersion i] [IsOpenImmersion j] (H : IsPullback i q p j) (n : ℕ)
    (N : Y.Modules) {P : Z.Modules}
    (t : (relativeHigherFunctor q n).obj ((Modules.restrictFunctor j).obj N) ⟶ P) :
    relativeHigherRestrictionHom p i q j H n N ≫ t =
      (Scheme.Modules.higherDirectImageOpenRestrictionIso i q p j H n).hom.app
        ((relativeTopDifferentialCoefficientsFunctor p n).obj N) ≫
      ((Scheme.Modules.pushforward q).rightDerived n).map
        ((relativeTopDifferentialCoefficientsRestrictionIso p i q j H.w n).hom.app N) ≫ t := by
  rw [relativeHigherRestrictionHom_component, Category.assoc]
private def rawTraceRestrictionSquare
    {W X Z Y : Scheme.{u}} (i : W ⟶ X) (q : W ⟶ Z) (p : X ⟶ Y) (j : Z ⟶ Y)
    [IsOpenImmersion i] [IsOpenImmersion j] (H : IsPullback i q p j)
    (M : X.Modules) (M' : W.Modules) (N : Y.Modules) (n : ℕ)
    (C : (Modules.restrictFunctor i).obj M ⟶ M')
    (tR : ((Scheme.Modules.pushforward p).rightDerived n).obj M ⟶ N)
    (tA : ((Scheme.Modules.pushforward q).rightDerived n).obj M' ⟶
      (Modules.restrictFunctor j).obj N) : Prop :=
  @Eq ((Modules.restrictFunctor j).obj
      (((Scheme.Modules.pushforward p).rightDerived n).obj M) ⟶
    (Modules.restrictFunctor j).obj N)
    ((Scheme.Modules.higherDirectImageOpenRestrictionIso i q p j H n).hom.app M ≫
      ((Scheme.Modules.pushforward q).rightDerived n).map
        (X := (Modules.restrictFunctor i).obj M) (Y := M') C ≫ tA)
    ((Modules.restrictFunctor j).map
      (X := ((Scheme.Modules.pushforward p).rightDerived n).obj M) (Y := N) tR)

private theorem relativeHigherRestrictionHom_of_raw_square
    {W X Z Y : Scheme.{u}} (p : X ⟶ Y) (i : W ⟶ X) (q : W ⟶ Z) (j : Z ⟶ Y)
    [IsOpenImmersion i] [IsOpenImmersion j] (H : IsPullback i q p j)
    (w : i ≫ p = q ≫ j) (n : ℕ)
    (N : Y.Modules)
    (tR : ((Scheme.Modules.pushforward p).rightDerived n).obj
      ((relativeTopDifferentialCoefficientsFunctor p n).obj N) ⟶ N)
    (tA : ((Scheme.Modules.pushforward q).rightDerived n).obj
      ((relativeTopDifferentialCoefficientsFunctor q n).obj
        ((Modules.restrictFunctor j).obj N)) ⟶ (Modules.restrictFunctor j).obj N)
    (h : rawTraceRestrictionSquare i q p j H
      ((relativeTopDifferentialCoefficientsFunctor p n).obj N)
      ((relativeTopDifferentialCoefficientsFunctor q n).obj
        ((Modules.restrictFunctor j).obj N)) N n
      (coefficientRawComponent (relativeTopDifferentialCoefficientsFunctor p n)
        (Modules.restrictFunctor j) (relativeTopDifferentialCoefficientsFunctor q n)
        (Modules.restrictFunctor i)
        (relativeTopDifferentialCoefficientsRestrictionIso p i q j w n).hom N)
      tR tA) :
    relativeHigherTraceSquare p i q j H n N tR tA := by
  let P (v : i ≫ p = q ≫ j) : Prop := rawTraceRestrictionSquare i q p j H
    ((relativeTopDifferentialCoefficientsFunctor p n).obj N)
    ((relativeTopDifferentialCoefficientsFunctor q n).obj
      ((Modules.restrictFunctor j).obj N)) N n
    (coefficientRawComponent (relativeTopDifferentialCoefficientsFunctor p n)
      (Modules.restrictFunctor j) (relativeTopDifferentialCoefficientsFunctor q n)
      (Modules.restrictFunctor i)
      (relativeTopDifferentialCoefficientsRestrictionIso p i q j v n).hom N)
    tR tA
  have h' : P H.w := (congrArg P (Subsingleton.elim w H.w)).mp h
  exact (relativeHigherRestrictionHom_postcomp p i q j H n N tA).trans h'

private theorem affineTraceRestriction_of_equations
    {R A : Type u} [CommRing R] [CommRing A] {X W : Scheme.{u}}
    (i : W ⟶ X) (q : W ⟶ Spec (.of A)) (p : X ⟶ Spec (.of R)) (σ : R →+* A)
    [QuasiCompact p] [QuasiSeparated p] [QuasiCompact q] [QuasiSeparated q]
    [IsOpenImmersion i] [IsOpenImmersion (Spec.map (CommRingCat.ofHom σ))]
    (H : IsPullback i q p (Spec.map (CommRingCat.ofHom σ)))
    (M : X.Modules) [M.IsQuasicoherent] (M' : W.Modules) [M'.IsQuasicoherent]
    (N : (Spec (.of R)).Modules) (n : ℕ)
    (C : (Modules.restrictFunctor i).obj M ⟶ M')
    (β : M ⟶ (Scheme.Modules.pushforward i).obj M')
    (hβ : β = (restrictAdjunction i).homEquiv M M' C)
    (tR : ((Scheme.Modules.pushforward p).rightDerived n).obj M ⟶ N)
    (tA : ((Scheme.Modules.pushforward q).rightDerived n).obj M' ⟶
      (Modules.restrictFunctor (Spec.map (CommRingCat.ofHom σ))).obj N)
    (τR : Sheaf.H.{u + 1} (moduleAddSheaf X M) n → moduleSpecΓFunctor.obj N)
    (τA : Sheaf.H.{u + 1} (moduleAddSheaf W M') n →
      moduleSpecΓFunctor.obj
        ((Modules.restrictFunctor (Spec.map (CommRingCat.ofHom σ))).obj N))
    (htR : affineTraceSectionsEquation p M N n tR τR)
    (htA : affineTraceSectionsEquation q M'
      ((Modules.restrictFunctor (Spec.map (CommRingCat.ofHom σ))).obj N) n tA τA)
    (hopen : ∀ c, τA (moduleCohomologyMapAlong i β n c) =
      affineUnitSections (Spec.map (CommRingCat.ofHom σ)) N (τR c)) :
    rawTraceRestrictionSquare i q p (Spec.map (CommRingCat.ofHom σ)) H
      M M' N n C tR tA :=
  affineTraceRestriction_of_sections i q p σ H M M' N n C β hβ tR tA τR τA htR htA hopen

private theorem affineTraceRestriction_of_coefficientEquation
    {R A : Type u} [CommRing R] [CommRing A] {X W : Scheme.{u}}
    (i : W ⟶ X) (q : W ⟶ Spec (.of A)) (p : X ⟶ Spec (.of R)) (σ : R →+* A)
    [QuasiCompact p] [QuasiSeparated p] [QuasiCompact q] [QuasiSeparated q]
    [IsOpenImmersion i] [IsOpenImmersion (Spec.map (CommRingCat.ofHom σ))]
    (H : IsPullback i q p (Spec.map (CommRingCat.ofHom σ)))
    (F : (Spec (.of R)).Modules ⥤ X.Modules)
    (G : (Spec (.of A)).Modules ⥤ W.Modules)
    (η : F ⋙ Modules.restrictFunctor i ⟶
      Modules.restrictFunctor (Spec.map (CommRingCat.ofHom σ)) ⋙ G)
    (N : (Spec (.of R)).Modules) (n : ℕ)
    [(F.obj N).IsQuasicoherent]
    [(G.obj ((Modules.restrictFunctor (Spec.map (CommRingCat.ofHom σ))).obj N)).IsQuasicoherent]
    (b : F.obj N ⟶ (Scheme.Modules.pushforward i).obj
      ((Modules.restrictFunctor (Spec.map (CommRingCat.ofHom σ)) ⋙ G).obj N))
    (hβ : coefficientAdjunctionEquation F
      (Modules.restrictFunctor (Spec.map (CommRingCat.ofHom σ))) G
      (Modules.restrictFunctor i) (Scheme.Modules.pushforward i) (restrictAdjunction i) η N b)
    (tR : ((Scheme.Modules.pushforward p).rightDerived n).obj (F.obj N) ⟶ N)
    (tA : ((Scheme.Modules.pushforward q).rightDerived n).obj
      (G.obj ((Modules.restrictFunctor (Spec.map (CommRingCat.ofHom σ))).obj N)) ⟶
        (Modules.restrictFunctor (Spec.map (CommRingCat.ofHom σ))).obj N)
    (τR : Sheaf.H.{u + 1} (moduleAddSheaf X (F.obj N)) n → moduleSpecΓFunctor.obj N)
    (τA : Sheaf.H.{u + 1} (moduleAddSheaf W
      (G.obj ((Modules.restrictFunctor (Spec.map (CommRingCat.ofHom σ))).obj N))) n →
        moduleSpecΓFunctor.obj
          ((Modules.restrictFunctor (Spec.map (CommRingCat.ofHom σ))).obj N))
    (htR : affineTraceSectionsEquation p (F.obj N) N n tR τR)
    (htA : affineTraceSectionsEquation q
      (G.obj ((Modules.restrictFunctor (Spec.map (CommRingCat.ofHom σ))).obj N))
      ((Modules.restrictFunctor (Spec.map (CommRingCat.ofHom σ))).obj N) n tA τA)
    (hopen : ∀ c, τA (moduleCohomologyMapAlong i b n c) =
      affineUnitSections (Spec.map (CommRingCat.ofHom σ)) N (τR c)) :
    rawTraceRestrictionSquare i q p (Spec.map (CommRingCat.ofHom σ)) H
      (F.obj N) (G.obj ((Modules.restrictFunctor (Spec.map (CommRingCat.ofHom σ))).obj N))
      N n (coefficientRawComponent F
        (Modules.restrictFunctor (Spec.map (CommRingCat.ofHom σ))) G
        (Modules.restrictFunctor i) η N) tR tA := by
  exact affineTraceRestriction_of_equations i q p σ H
    (F.obj N) (G.obj ((Modules.restrictFunctor (Spec.map (CommRingCat.ofHom σ))).obj N)) N n
    (coefficientRawComponent F (Modules.restrictFunctor (Spec.map (CommRingCat.ofHom σ)))
      G (Modules.restrictFunctor i) η N)
    (coefficientRawAdjunct F (Modules.restrictFunctor (Spec.map (CommRingCat.ofHom σ)))
      G (Scheme.Modules.pushforward i) N b)
    (coefficientAdjunctionEquation_raw F
      (Modules.restrictFunctor (Spec.map (CommRingCat.ofHom σ))) G
      (Modules.restrictFunctor i) (Scheme.Modules.pushforward i) (restrictAdjunction i) η N b hβ)
    tR tA τR τA htR htA hopen

set_option backward.isDefEq.respectTransparency true in
set_option backward.isDefEq.respectTransparency.types true in
private theorem standardAffineRawTraceSquare
    {R A : Type u} [CommRing R] [CommRing A] (σ : R →+* A) (ι : Type u)
    [IsOpenImmersion (Spec.map (CommRingCat.ofHom σ))]
    [gOpen : IsOpenImmersion (ProjectiveSpace.map σ ι)]
    (n : ℕ) (e : ι ≃ Fin (n + 1)) (N : (Spec (.of R)).Modules) [N.IsQuasicoherent] :
    rawTraceRestrictionSquare (ProjectiveSpace.map σ ι) (toSpec A ι) (toSpec R ι)
      (Spec.map (CommRingCat.ofHom σ)) (ProjectiveSpace.isPullback_map σ ι)
      ((relativeTopDifferentialCoefficientsFunctor (toSpec R ι) n).obj N)
      ((relativeTopDifferentialCoefficientsFunctor (toSpec A ι) n).obj
        ((Modules.restrictFunctor (Spec.map (CommRingCat.ofHom σ))).obj N)) N n
      (coefficientRawComponent
        (relativeTopDifferentialCoefficientsFunctor (toSpec R ι) n)
        (Modules.restrictFunctor (Spec.map (CommRingCat.ofHom σ)))
        (relativeTopDifferentialCoefficientsFunctor (toSpec A ι) n)
        (Modules.restrictFunctor (ProjectiveSpace.map σ ι))
        (relativeTopDifferentialCoefficientsRestrictionIso (toSpec R ι) (ProjectiveSpace.map σ ι)
          (toSpec A ι) (Spec.map (CommRingCat.ofHom σ)) (ProjectiveSpace.map_toSpec σ ι) n).hom N)
      (standardAffineTraceHom R ι n e N)
      (standardAffineTraceHom A ι n e
        ((Modules.restrictFunctor (Spec.map (CommRingCat.ofHom σ))).obj N)) := by
  let : Fintype ι := Fintype.ofEquiv (Fin (n + 1)) e.symm
  let g := ProjectiveSpace.map σ ι
  let j := Spec.map (CommRingCat.ofHom σ)
  let M := (relativeTopDifferentialCoefficientsFunctor (toSpec R ι) n).obj N
  let M' := (relativeTopDifferentialCoefficientsFunctor (toSpec A ι) n).obj
    ((Modules.restrictFunctor j).obj N)
  let hM : M.IsQuasicoherent :=
    projectiveTopDifferentialCoefficients_isQuasicoherent R ι n e N
  let hM' : M'.IsQuasicoherent :=
    projectiveTopDifferentialCoefficients_isQuasicoherent A ι n e
      ((Modules.restrictFunctor j).obj N)
  let η := (relativeTopDifferentialCoefficientsRestrictionIso (toSpec R ι) g (toSpec A ι) j
    (ProjectiveSpace.map_toSpec σ ι) n).hom
  let b : M ⟶ (Scheme.Modules.pushforward g).obj
      ((Modules.restrictFunctor j ⋙
        relativeTopDifferentialCoefficientsFunctor (toSpec A ι) n).obj N) :=
    projectiveAffineDifferentialCoefficientsOpenMap σ ι n N
  let tR := standardAffineTraceHom R ι n e N
  let tA := standardAffineTraceHom A ι n e ((Modules.restrictFunctor j).obj N)
  let τR : Sheaf.H.{u + 1} (moduleAddSheaf (ProjectiveSpace R ι) M) n →
      (moduleSpecΓFunctor (R := .of R)).obj N :=
    fun c => projectiveAffineDifferentialTraceLinearEquiv R ι n e N c
  let τA : Sheaf.H.{u + 1} (moduleAddSheaf (ProjectiveSpace A ι) M') n →
      (moduleSpecΓFunctor (R := .of A)).obj ((Modules.restrictFunctor j).obj N) :=
    fun c => projectiveAffineDifferentialTraceLinearEquiv A ι n e
      ((Modules.restrictFunctor j).obj N) c
  have hR := standardAffineTraceHom_sections R ι n e N
  have hA := standardAffineTraceHom_sections A ι n e
    ((Modules.restrictFunctor j).obj N)
  have hOpen := projectiveAffineDifferentialTraceLinearEquiv_open σ ι n e N
  have hOpen' (c : Sheaf.H.{u + 1}
      (moduleAddSheaf (ProjectiveSpace R ι) M) n) :
      τA (moduleCohomologyMapAlong g b n c) = affineUnitSections j N (τR c) :=
    (hOpen c).trans (affineUnitSections_eq j N (τR c)).symm
  have hβ := coefficientOpenMap_eq_homEquiv σ ι gOpen n N
  dsimp -proj only [coefficientOpenMapAdjunctEquation] at hβ
  have h := affineTraceRestriction_of_coefficientEquation (R := R) (A := A)
    (X := ProjectiveSpace R ι) (W := ProjectiveSpace A ι)
    g (toSpec A ι) (toSpec R ι) σ (ProjectiveSpace.isPullback_map σ ι)
    (relativeTopDifferentialCoefficientsFunctor (toSpec R ι) n)
    (relativeTopDifferentialCoefficientsFunctor (toSpec A ι) n) η N n b hβ
    tR tA τR τA hR hA hOpen'
  dsimp -proj only [η, tR, tA, g, j] at h
  exact h

set_option backward.isDefEq.respectTransparency true in
set_option backward.isDefEq.respectTransparency.types true in
private theorem standardAffineTraceIso_open
    {R A : Type u} [CommRing R] [CommRing A] (σ : R →+* A) (ι : Type u)
    [IsOpenImmersion (Spec.map (CommRingCat.ofHom σ))]
    [gOpen : IsOpenImmersion (ProjectiveSpace.map σ ι)]
    (n : ℕ) (e : ι ≃ Fin (n + 1)) (N : (Spec (.of R)).Modules) [N.IsQuasicoherent] :
    relativeHigherTraceSquare (toSpec R ι) (ProjectiveSpace.map σ ι) (toSpec A ι)
      (Spec.map (CommRingCat.ofHom σ)) (ProjectiveSpace.isPullback_map σ ι) n N
      (standardAffineTraceHom R ι n e N)
      (standardAffineTraceHom A ι n e
        ((Modules.restrictFunctor (Spec.map (CommRingCat.ofHom σ))).obj N)) := by
  exact relativeHigherRestrictionHom_of_raw_square (toSpec R ι) (ProjectiveSpace.map σ ι)
    (toSpec A ι) (Spec.map (CommRingCat.ofHom σ)) (ProjectiveSpace.isPullback_map σ ι)
    (ProjectiveSpace.map_toSpec σ ι) n N
    (standardAffineTraceHom R ι n e N)
    (standardAffineTraceHom A ι n e
      ((Modules.restrictFunctor (Spec.map (CommRingCat.ofHom σ))).obj N))
    (standardAffineRawTraceSquare σ ι n e N)
section AffineModels
variable (R : Type u) [CommRing R] (ι : Type u)
  {A B : Type u} [CommRing A] [CommRing B] {X W : Scheme.{u}}
  (a : X ⟶ ProjectiveSpace R ι) (p : X ⟶ Spec (.of A))
  (f : Spec (.of A) ⟶ Spec (.of R)) (h : IsPullback a p (toSpec R ι) f)
private def affineRelativeTraceIso
    (n : ℕ) (e : ι ≃ Fin (n + 1)) (N : (Spec (.of A)).Modules) [N.IsQuasicoherent] :
    (relativeHigherFunctor p n).obj N ≅ N :=
  compositeTraceIso (relativeHigherFunctor p n)
    (relativeTopDifferentialCoefficientsFunctor (toSpec A ι) n)
    ((Scheme.Modules.pushforward (toSpec A ι)).rightDerived n)
    (affineModelHigherIso R ι a p f h n) N (standardAffineTraceIso A ι n e N)
private def affineRelativeTraceHom
    (n : ℕ) (e : ι ≃ Fin (n + 1)) (N : (Spec (.of A)).Modules) [N.IsQuasicoherent] :
    (relativeHigherFunctor p n).obj N ⟶ N :=
  (show (relativeHigherFunctor p n).obj N ≅ N from
    affineRelativeTraceIso R ι a p f h n e N).hom
private theorem affineRelativeTraceIso_naturality
    (n : ℕ) (e : ι ≃ Fin (n + 1))
    {N N' : (Spec (.of A)).Modules} [N.IsQuasicoherent] [N'.IsQuasicoherent] (s : N ⟶ N') :
    (relativeHigherFunctor p n).map s ≫ (affineRelativeTraceIso R ι a p f h n e N').hom =
      (affineRelativeTraceIso R ι a p f h n e N).hom ≫ s := by
  dsimp only [affineRelativeTraceIso, compositeTraceIso, Iso.trans_hom, Iso.app_hom]
  rw [← Category.assoc, (affineModelHigherIso R ι a p f h n).hom.naturality s,
    Category.assoc, standardAffineTraceIso_naturality]
  exact (Category.assoc _ _ _).symm
private theorem affineRelativeTraceHom_eq
    (n : ℕ) (e : ι ≃ Fin (n + 1)) (N : (Spec (.of A)).Modules) [N.IsQuasicoherent] :
    affineRelativeTraceHom R ι a p f h n e N =
      (affineRelativeTraceIso R ι a p f h n e N).hom := rfl
private theorem affineRelativeTraceHom_naturality
    (n : ℕ) (e : ι ≃ Fin (n + 1))
    {N N' : (Spec (.of A)).Modules} [N.IsQuasicoherent] [N'.IsQuasicoherent] (s : N ⟶ N') :
    (relativeHigherFunctor p n).map s ≫ affineRelativeTraceHom R ι a p f h n e N' =
      affineRelativeTraceHom R ι a p f h n e N ≫ s := by
  simpa only [affineRelativeTraceHom_eq] using
    affineRelativeTraceIso_naturality R ι a p f h n e s
/-- Keep the original affine coefficient law as an opaque naturality equation. -/
private theorem affineRelativeTraceHom_naturality_equation
    (n : ℕ) (e : ι ≃ Fin (n + 1))
    {N N' : (Spec (.of A)).Modules} [N.IsQuasicoherent] [N'.IsQuasicoherent]
    (s : N ⟶ N') :
    traceLocalNaturalityEquation
      (relativeTopDifferentialCoefficientsFunctor p n)
      ((Scheme.Modules.pushforward p).rightDerived n) (𝟭 (Spec (.of A)).Modules) s
      (affineRelativeTraceHom R ι a p f h n e N)
      (affineRelativeTraceHom R ι a p f h n e N') := by
  have hn := affineRelativeTraceHom_naturality R ι a p f h n e s
  dsimp -proj only [traceLocalNaturalityEquation, Functor.id_obj, Functor.id_map]
  dsimp -proj only [relativeHigherFunctor, Functor.comp_map, Functor.comp_obj] at hn
  exact hn
private theorem affineRelativeTraceHom_sections
    (n : ℕ) (e : ι ≃ Fin (n + 1)) (N : (Spec (.of A)).Modules) [N.IsQuasicoherent] :
    letI : Fintype ι := Fintype.ofEquiv (Fin (n + 1)) e.symm
    letI := projectiveTopDifferentialCoefficients_isQuasicoherent A ι n e N
    traceModelSectionsEquation (toSpec A ι) (relativeHigherFunctor p n)
      (relativeTopDifferentialCoefficientsFunctor (toSpec A ι) n) n
      (affineModelHigherIso R ι a p f h n) N
      (fun c => projectiveAffineDifferentialTraceLinearEquiv A ι n e N c)
      (affineRelativeTraceHom R ι a p f h n e N) := by
  let : Fintype ι := Fintype.ofEquiv (Fin (n + 1)) e.symm
  let := projectiveTopDifferentialCoefficients_isQuasicoherent A ι n e N
  exact traceModelSections_of_standard (toSpec A ι) (relativeHigherFunctor p n)
    (relativeTopDifferentialCoefficientsFunctor (toSpec A ι) n) n
    (affineModelHigherIso R ι a p f h n) N (standardAffineTraceIso A ι n e N)
    (fun c => projectiveAffineDifferentialTraceLinearEquiv A ι n e N c)
    (standardAffineTraceIso_sections A ι n e N)
private theorem affineRelativeTraceIso_open
    (i : W ⟶ X) (q : W ⟶ Spec (.of B)) (j : Spec (.of B) ⟶ Spec (.of A))
    [IsOpenImmersion i] [IsOpenImmersion j] (H : IsPullback i q p j)
    (n : ℕ) (e : ι ≃ Fin (n + 1)) (N : (Spec (.of A)).Modules) [N.IsQuasicoherent] :
    compositeTraceOpenSquare (Modules.restrictFunctor j) (relativeHigherFunctor p n)
      (relativeTopDifferentialCoefficientsFunctor (toSpec A ι) n)
      ((Scheme.Modules.pushforward (toSpec A ι)).rightDerived n)
      (affineModelHigherIso R ι a p f h n) (relativeHigherFunctor q n)
      (relativeTopDifferentialCoefficientsFunctor (toSpec B ι) n)
      ((Scheme.Modules.pushforward (toSpec B ι)).rightDerived n)
      (affineModelHigherIso R ι (i ≫ a) q (j ≫ f) (H.paste_horiz h) n)
      N (standardAffineTraceIso A ι n e N) (standardAffineTraceIso B ι n e (N.restrict j))
      (relativeHigherRestrictionIso p i q j H n) := by
  have hj : ∃ σ : A →+* B, Spec.map (CommRingCat.ofHom σ) = j :=
    ⟨(Spec.preimage j).hom, Spec.map_preimage j⟩
  obtain ⟨σ, rfl⟩ := hj
  let : IsOpenImmersion (ProjectiveSpace.map σ ι) :=
    MorphismProperty.of_isPullback (ProjectiveSpace.isPullback_map σ ι).flip inferInstance
  have hm := affineModelHigherIso_open_nat R ι a p f h i q σ H n
  have ht := standardAffineTraceIso_open σ ι n e N
  have traceInput := relativeHigherTraceSquare_nat (toSpec A ι) (ProjectiveSpace.map σ ι)
    (toSpec B ι) (Spec.map (CommRingCat.ofHom σ)) (ProjectiveSpace.isPullback_map σ ι) n N
    (standardAffineTraceHom A ι n e N)
    (standardAffineTraceHom B ι n e (N.restrict (Spec.map (CommRingCat.ofHom σ)))) ht
  have hFinal := compositeTrace_open_of_natSquare
    (Modules.restrictFunctor (Spec.map (CommRingCat.ofHom σ)))
    (relativeHigherFunctor p n)
    (relativeTopDifferentialCoefficientsFunctor (toSpec A ι) n)
    ((Scheme.Modules.pushforward (toSpec A ι)).rightDerived n)
    (affineModelHigherIso R ι a p f h n)
    (relativeHigherFunctor q n)
    (relativeTopDifferentialCoefficientsFunctor (toSpec B ι) n)
    ((Scheme.Modules.pushforward (toSpec B ι)).rightDerived n)
    (affineModelHigherIso R ι (i ≫ a) q ((Spec.map (CommRingCat.ofHom σ)) ≫ f)
      (H.paste_horiz h) n)
    N (standardAffineTraceIso A ι n e N)
    (standardAffineTraceIso B ι n e (N.restrict (Spec.map (CommRingCat.ofHom σ))))
    (relativeHigherRestrictionIso p i q (Spec.map (CommRingCat.ofHom σ)) H n)
    (relativeHigherRestrictionIso (toSpec A ι) (ProjectiveSpace.map σ ι) (toSpec B ι)
      (Spec.map (CommRingCat.ofHom σ)) (ProjectiveSpace.isPullback_map σ ι) n)
    (standardAffineTraceHom A ι n e N)
    (standardAffineTraceHom B ι n e (N.restrict (Spec.map (CommRingCat.ofHom σ))))
    hm traceInput (standardAffineTraceHom_eq A ι n e N)
    (standardAffineTraceHom_eq B ι n e (N.restrict (Spec.map (CommRingCat.ofHom σ))))
  exact hFinal
/-- The same native affine open law for the genuine Hom wrapper. -/
private theorem affineRelativeTraceHom_open
    (i : W ⟶ X) (q : W ⟶ Spec (.of B)) (j : Spec (.of B) ⟶ Spec (.of A))
    [IsOpenImmersion i] [IsOpenImmersion j] (H : IsPullback i q p j)
    (n : ℕ) (e : ι ≃ Fin (n + 1)) (N : (Spec (.of A)).Modules) [N.IsQuasicoherent] :
    relativeHigherTraceSquare p i q j H n N
      (affineRelativeTraceHom R ι a p f h n e N)
      (affineRelativeTraceHom R ι (i ≫ a) q (j ≫ f) (H.paste_horiz h) n e
        ((Modules.restrictFunctor j).obj N)) := by
  have hOpen := affineRelativeTraceIso_open R ι a p f h i q j H n e N
  dsimp -proj only [compositeTraceOpenSquare] at hOpen
  dsimp -proj only [relativeHigherTraceSquare, relativeHigherRestrictionHom,
    affineRelativeTraceHom, affineRelativeTraceIso]
  exact hOpen

/-- The original identity-base comparison preserves the original affine trace. -/
private theorem affineRelativeTraceHom_identity
    (i : W ⟶ X) (q : W ⟶ Spec (.of A)) [IsOpenImmersion i]
    (H : IsPullback i q p (𝟙 (Spec (.of A))))
    (n : ℕ) (e : ι ≃ Fin (n + 1)) (N : (Spec (.of A)).Modules) [N.IsQuasicoherent] :
    (identityHigherModelIso p i q H n).hom.app N ≫
        affineRelativeTraceHom (A := A) R ι (i ≫ a) q ((𝟙 (Spec (.of A))) ≫ f)
          (H.paste_horiz h) n e N =
      affineRelativeTraceHom (A := A) R ι a p f h n e N := by
  have ho₀ := affineRelativeTraceHom_open (A := A) (B := A) R ι a p f h i q
    (𝟙 (Spec (.of A))) H n e N
  have ho := relativeHigherTraceSquare_nat p i q (𝟙 (Spec (.of A))) H n N
    (affineRelativeTraceHom (A := A) R ι a p f h n e N)
    (affineRelativeTraceHom (A := A) R ι (i ≫ a) q ((𝟙 (Spec (.of A))) ≫ f)
      (H.paste_horiz h) n e (N.restrict (𝟙 (Spec (.of A))))) ho₀
  dsimp -proj only [compositeTraceNatRestrictionSquare, Functor.comp_obj] at ho
  have hn := affineRelativeTraceHom_naturality (A := A) R ι (i ≫ a) q
    ((𝟙 (Spec (.of A))) ≫ f) (H.paste_horiz h) n e
    (N := N.restrict (𝟙 (Spec (.of A)))) (N' := N)
    ((restrictFunctorId (X := Spec (.of A))).hom.app N)
  exact identityHigherModelIso_trace p i q H n N
    (affineRelativeTraceHom (A := A) R ι a p f h n e N)
    (affineRelativeTraceHom (A := A) R ι (i ≫ a) q ((𝟙 (Spec (.of A))) ≫ f)
      (H.paste_horiz h) n e N)
    (affineRelativeTraceHom (A := A) R ι (i ≫ a) q ((𝟙 (Spec (.of A))) ≫ f)
      (H.paste_horiz h) n e (N.restrict (𝟙 (Spec (.of A))))) ho hn

/-- Keep the original affine identity law as an opaque restriction equation. -/
private theorem affineRelativeTraceHom_identity_equation
    (i : W ⟶ X) (q : W ⟶ Spec (.of A)) [IsOpenImmersion i]
    (H : IsPullback i q p (𝟙 (Spec (.of A))))
    (n : ℕ) (e : ι ≃ Fin (n + 1)) (N : (Spec (.of A)).Modules) [N.IsQuasicoherent] :
    compositeTraceRestrictionSquare (𝟭 (Spec (.of A)).Modules)
      (relativeTopDifferentialCoefficientsFunctor p n)
      ((Scheme.Modules.pushforward p).rightDerived n)
      (relativeTopDifferentialCoefficientsFunctor q n)
      ((Scheme.Modules.pushforward q).rightDerived n) N
      ((identityHigherModelIso p i q H n).hom.app N)
      (affineRelativeTraceHom (A := A) R ι a p f h n e N)
      (affineRelativeTraceHom (A := A) R ι (i ≫ a) q ((𝟙 (Spec (.of A))) ≫ f)
        (H.paste_horiz h) n e N) := by
  have hi := affineRelativeTraceHom_identity (A := A) R ι a p f h i q H n e N
  dsimp -proj only [compositeTraceRestrictionSquare, Functor.id_obj, Functor.id_map]
  dsimp -proj only [relativeHigherFunctor, Functor.comp_obj] at hi
  exact hi

end AffineModels
variable (R : Type u) [CommRing R] (ι : Type u)
  {X Y : Scheme.{u}} (a : X ⟶ ProjectiveSpace R ι) (p : X ⟶ Y)
  (f : Y ⟶ Spec (.of R)) (h : IsPullback a p (toSpec R ι) f)
set_option backward.isDefEq.respectTransparency true in
set_option backward.isDefEq.respectTransparency.types true in
private def relativeAffineHigherNatIso (n : ℕ) {A : CommRingCat.{u}}
    (j : Spec A ⟶ Y) [IsOpenImmersion j] :
    relativeHigherFunctor p n ⋙ Modules.restrictFunctor j ≅
      Modules.restrictFunctor j ⋙ relativeHigherFunctor (toSpec A ι) n :=
  affineHigherCompositeFactory (relativeHigherFunctor p n)
    (relativeHigherFunctor (pullback.snd p j) n) (relativeHigherFunctor (toSpec A ι) n)
    (Modules.restrictFunctor j)
    (relativeHigherRestrictionIso p (pullback.fst p j) (pullback.snd p j) j
      (IsPullback.of_hasPullback p j) n)
    (affineModelHigherIso (A := A) R ι (pullback.fst p j ≫ a) (pullback.snd p j) (j ≫ f)
      ((IsPullback.of_hasPullback p j).paste_horiz h) n)

private theorem relativeAffineHigherNatIso_original (n : ℕ) {A : CommRingCat.{u}}
    (j : Spec A ⟶ Y) [IsOpenImmersion j] :
    relativeAffineHigherNatIso R ι a p f h n j =
      relativeHigherRestrictionIso p (pullback.fst p j) (pullback.snd p j) j
        (IsPullback.of_hasPullback p j) n ≪≫
        Functor.isoWhiskerLeft (Modules.restrictFunctor j)
          (affineModelHigherIso R ι (pullback.fst p j ≫ a) (pullback.snd p j) (j ≫ f)
            ((IsPullback.of_hasPullback p j).paste_horiz h) n) := rfl

/-- Original restriction identifies each actual affine chart with its polynomial model. -/
@[no_expose]
def relativeProjectiveAffineHigherIso (n : ℕ) {A : CommRingCat.{u}}
    (j : Spec A ⟶ Y) [IsOpenImmersion j] (N : Y.Modules) :
    (((Scheme.Modules.pushforward p).rightDerived n).obj
      ((relativeTopDifferentialCoefficientsFunctor p n).obj N)).restrict j ≅
      ((Scheme.Modules.pushforward (toSpec A ι)).rightDerived n).obj
        ((relativeTopDifferentialCoefficientsFunctor (toSpec A ι) n).obj (N.restrict j)) :=
  (relativeAffineHigherNatIso R ι a p f h n j).app N

set_option backward.isDefEq.respectTransparency true in
set_option backward.isDefEq.respectTransparency.types true in
private def relativeProjectiveAffineHigherHom (n : ℕ) {A : CommRingCat.{u}}
    (j : Spec A ⟶ Y) [IsOpenImmersion j] (N : Y.Modules) :
    (((Scheme.Modules.pushforward p).rightDerived n).obj
      ((relativeTopDifferentialCoefficientsFunctor p n).obj N)).restrict j ⟶
      ((Scheme.Modules.pushforward (toSpec A ι)).rightDerived n).obj
        ((relativeTopDifferentialCoefficientsFunctor (toSpec A ι) n).obj (N.restrict j)) :=
  (show (((Scheme.Modules.pushforward p).rightDerived n).obj
      ((relativeTopDifferentialCoefficientsFunctor p n).obj N)).restrict j ≅
      ((Scheme.Modules.pushforward (toSpec A ι)).rightDerived n).obj
        ((relativeTopDifferentialCoefficientsFunctor (toSpec A ι) n).obj (N.restrict j)) from
    relativeProjectiveAffineHigherIso R ι a p f h n j N).hom

set_option backward.isDefEq.respectTransparency true in
set_option backward.isDefEq.respectTransparency.types true in
private theorem relativeProjectiveAffineHigherHom_eq (n : ℕ) {A : CommRingCat.{u}}
    (j : Spec A ⟶ Y) [IsOpenImmersion j] (N : Y.Modules) :
    relativeProjectiveAffineHigherHom R ι a p f h n j N =
      (relativeProjectiveAffineHigherIso R ι a p f h n j N).hom := rfl

set_option backward.isDefEq.respectTransparency true in
set_option backward.isDefEq.respectTransparency.types true in
private theorem relativeProjectiveAffineHigherIso_component (n : ℕ) {A : CommRingCat.{u}}
    (j : Spec A ⟶ Y) [IsOpenImmersion j] (N : Y.Modules) :
    (relativeProjectiveAffineHigherIso R ι a p f h n j N).hom =
      (relativeAffineHigherNatIso R ι a p f h n j).hom.app N := rfl
set_option backward.isDefEq.respectTransparency true in
set_option backward.isDefEq.respectTransparency.types true in
private def relativeAffineTraceLocal (n : ℕ) (e : ι ≃ Fin (n + 1))
    {A : CommRingCat.{u}} (j : Spec A ⟶ Y) [IsOpenImmersion j]
    (N : Y.Modules) [N.IsQuasicoherent] :
    (Modules.restrictFunctor j).obj
      (((Scheme.Modules.pushforward p).rightDerived n).obj
        ((relativeTopDifferentialCoefficientsFunctor p n).obj N)) ⟶
      (Modules.restrictFunctor j).obj N :=
  traceLocalHomFactory
    (relativeTopDifferentialCoefficientsFunctor p n)
    ((Scheme.Modules.pushforward p).rightDerived n) (Modules.restrictFunctor j)
    (relativeTopDifferentialCoefficientsFunctor (pullback.snd p j) n)
    ((Scheme.Modules.pushforward (pullback.snd p j)).rightDerived n)
    (relativeHigherRestrictionIso p (pullback.fst p j) (pullback.snd p j) j
      (IsPullback.of_hasPullback p j) n) N
    (affineRelativeTraceHom (A := (A : Type u)) R ι (pullback.fst p j ≫ a)
      (pullback.snd p j) (j ≫ f) ((IsPullback.of_hasPullback p j).paste_horiz h)
      n e ((Modules.restrictFunctor j).obj N))
set_option backward.isDefEq.respectTransparency true in
set_option backward.isDefEq.respectTransparency.types true in
private theorem relativeAffineTraceLocal_factored (n : ℕ) (e : ι ≃ Fin (n + 1))
    {A : CommRingCat.{u}} (j : Spec A ⟶ Y) [IsOpenImmersion j]
    (N : Y.Modules) [N.IsQuasicoherent] :
    traceLocalHomFactoryEquation
      (relativeTopDifferentialCoefficientsFunctor p n)
      ((Scheme.Modules.pushforward p).rightDerived n) (Modules.restrictFunctor j)
      (relativeTopDifferentialCoefficientsFunctor (pullback.snd p j) n)
      ((Scheme.Modules.pushforward (pullback.snd p j)).rightDerived n)
      (relativeHigherRestrictionIso p (pullback.fst p j) (pullback.snd p j) j
        (IsPullback.of_hasPullback p j) n) N
      (relativeAffineTraceLocal R ι a p f h n e j N)
      (affineRelativeTraceHom (A := (A : Type u)) R ι (pullback.fst p j ≫ a)
        (pullback.snd p j) (j ≫ f) ((IsPullback.of_hasPullback p j).paste_horiz h)
        n e ((Modules.restrictFunctor j).obj N)) := rfl
set_option backward.isDefEq.respectTransparency true in
set_option backward.isDefEq.respectTransparency.types true in
private theorem relativeAffineTraceLocal_sections (n : ℕ) (e : ι ≃ Fin (n + 1))
    {A : CommRingCat.{u}} (j : Spec A ⟶ Y) [IsOpenImmersion j]
    (N : Y.Modules) [N.IsQuasicoherent] :
    letI : Fintype ι := Fintype.ofEquiv (Fin (n + 1)) e.symm
    letI := projectiveTopDifferentialCoefficients_isQuasicoherent A ι n e (N.restrict j)
    traceLocalSectionsEquation (toSpec A ι)
      (relativeTopDifferentialCoefficientsFunctor p n)
      ((Scheme.Modules.pushforward p).rightDerived n) (Modules.restrictFunctor j)
      (relativeTopDifferentialCoefficientsFunctor (pullback.snd p j) n)
      ((Scheme.Modules.pushforward (pullback.snd p j)).rightDerived n)
      (relativeTopDifferentialCoefficientsFunctor (toSpec A ι) n)
      (relativeHigherRestrictionIso p (pullback.fst p j) (pullback.snd p j) j
        (IsPullback.of_hasPullback p j) n) n
      (affineModelHigherIso (A := (A : Type u)) R ι (pullback.fst p j ≫ a)
        (pullback.snd p j) (j ≫ f) ((IsPullback.of_hasPullback p j).paste_horiz h) n)
      N (fun c => projectiveAffineDifferentialTraceLinearEquiv A ι n e (N.restrict j) c)
      (relativeAffineTraceLocal R ι a p f h n e j N) := by
  let : Fintype ι := Fintype.ofEquiv (Fin (n + 1)) e.symm
  let := projectiveTopDifferentialCoefficients_isQuasicoherent A ι n e (N.restrict j)
  exact traceLocalSections_of_model (toSpec A ι)
    (relativeTopDifferentialCoefficientsFunctor p n)
    ((Scheme.Modules.pushforward p).rightDerived n) (Modules.restrictFunctor j)
    (relativeTopDifferentialCoefficientsFunctor (pullback.snd p j) n)
    ((Scheme.Modules.pushforward (pullback.snd p j)).rightDerived n)
    (relativeTopDifferentialCoefficientsFunctor (toSpec A ι) n)
    (relativeHigherRestrictionIso p (pullback.fst p j) (pullback.snd p j) j
      (IsPullback.of_hasPullback p j) n) n
    (affineModelHigherIso (A := (A : Type u)) R ι (pullback.fst p j ≫ a)
      (pullback.snd p j) (j ≫ f) ((IsPullback.of_hasPullback p j).paste_horiz h) n)
    N (affineRelativeTraceHom (A := (A : Type u)) R ι (pullback.fst p j ≫ a)
      (pullback.snd p j) (j ≫ f) ((IsPullback.of_hasPullback p j).paste_horiz h)
      n e ((Modules.restrictFunctor j).obj N))
    (fun c => projectiveAffineDifferentialTraceLinearEquiv A ι n e (N.restrict j) c)
    (affineRelativeTraceHom_sections (A := (A : Type u)) R ι (pullback.fst p j ≫ a)
      (pullback.snd p j) (j ≫ f) ((IsPullback.of_hasPullback p j).paste_horiz h)
      n e ((Modules.restrictFunctor j).obj N))

set_option backward.isDefEq.respectTransparency true in
set_option backward.isDefEq.respectTransparency.types true in
private theorem relativeAffineTraceLocal_naturality (n : ℕ) (e : ι ≃ Fin (n + 1))
    {A : CommRingCat.{u}} (j : Spec A ⟶ Y) [IsOpenImmersion j]
    {N N' : Y.Modules} [N.IsQuasicoherent] [N'.IsQuasicoherent] (s : N ⟶ N') :
    traceLocalNaturalityEquation (relativeTopDifferentialCoefficientsFunctor p n)
      ((Scheme.Modules.pushforward p).rightDerived n) (Modules.restrictFunctor j) s
      (relativeAffineTraceLocal R ι a p f h n e j N)
      (relativeAffineTraceLocal R ι a p f h n e j N') := by
  have hn := affineRelativeTraceHom_naturality (A := (A : Type u)) R ι
    (pullback.fst p j ≫ a) (pullback.snd p j) (j ≫ f)
    ((IsPullback.of_hasPullback p j).paste_horiz h) n e ((Modules.restrictFunctor j).map s)
  dsimp -proj only [relativeHigherFunctor, Functor.comp_map] at hn
  have h := traceLocalHomFactory_naturality
    (relativeTopDifferentialCoefficientsFunctor p n)
    ((Scheme.Modules.pushforward p).rightDerived n) (Modules.restrictFunctor j)
    (relativeTopDifferentialCoefficientsFunctor (pullback.snd p j) n)
    ((Scheme.Modules.pushforward (pullback.snd p j)).rightDerived n)
    (relativeHigherRestrictionIso p (pullback.fst p j) (pullback.snd p j) j
      (IsPullback.of_hasPullback p j) n) s
    (affineRelativeTraceHom (A := (A : Type u)) R ι (pullback.fst p j ≫ a)
      (pullback.snd p j) (j ≫ f) ((IsPullback.of_hasPullback p j).paste_horiz h)
      n e ((Modules.restrictFunctor j).obj N))
    (affineRelativeTraceHom (A := (A : Type u)) R ι (pullback.fst p j ≫ a)
      (pullback.snd p j) (j ≫ f) ((IsPullback.of_hasPullback p j).paste_horiz h)
      n e ((Modules.restrictFunctor j).obj N')) hn
  exact h
set_option backward.isDefEq.respectTransparency true in
set_option backward.isDefEq.respectTransparency.types true in
private theorem relativeAffineTraceLocal_refine (n : ℕ) (e : ι ≃ Fin (n + 1))
    {A B : CommRingCat.{u}} (j : Spec A ⟶ Y) (k : Spec B ⟶ Spec A)
    [IsOpenImmersion j] [IsOpenImmersion k] (N : Y.Modules) [N.IsQuasicoherent] :
    Scheme.Modules.InternalHom.restrictionHomMap j k
      (M := ((Scheme.Modules.pushforward p).rightDerived n).obj
        ((relativeTopDifferentialCoefficientsFunctor p n).obj N)) (N := N)
      (relativeAffineTraceLocal R ι a p f h n e j N) =
      relativeAffineTraceLocal R ι a p f h n e (k ≫ j) N := by
  let i₀ := pullback.fst p j
  let q₀ := pullback.snd p j
  let H₀ := IsPullback.of_hasPullback p j
  let i₁ := pullback.fst p (k ≫ j)
  let q₁ := pullback.snd p (k ≫ j)
  let H₁ := IsPullback.of_hasPullback p (k ≫ j)
  let b := H₀.lift i₁ (q₁ ≫ k) (H₁.w.trans (Category.assoc _ _ _).symm)
  have hb : b ≫ i₀ = i₁ := H₀.lift_fst _ _ _
  have HB : IsPullback b q₁ q₀ k := H₁.of_right' H₀
  let : IsOpenImmersion b := MorphismProperty.of_isPullback HB.flip inferInstance
  have hc := relativeHigherRestrictionIso_comp p q₀ q₁ i₀ j b k H₀ HB
    (HB.paste_horiz H₀) n N
  have hoRaw := affineRelativeTraceHom_open (A := (A : Type u)) (B := (B : Type u))
    R ι (i₀ ≫ a) q₀ (j ≫ f) (H₀.paste_horiz h) b q₁ k HB n e
    ((Modules.restrictFunctor j).obj N)
  have transport {S T : Type _} (Q : S → T → Prop)
      (P : ∀ s t, Q s t → Prop) {s s' : S} {t t' : T}
      (hs : s = s') (ht : t = t') (q : Q s t) (q' : Q s' t')
      (hq : P s t q) : P s' t' q' := by
    cases hs
    cases ht
    exact (congrArg (P s t) (Subsingleton.elim q q')).mp hq
  let P (c : pullback p (k ≫ j) ⟶ ProjectiveSpace R ι)
      (g : Spec (@CommRingCat.of (B : Type u) (CommRingCat.commRing B)) ⟶
        Spec (.of R))
      (H : IsPullback c q₁ (toSpec R ι) g) : Prop :=
    compositeTraceNatRestrictionSquare (Modules.restrictFunctor k)
      (relativeTopDifferentialCoefficientsFunctor q₀ n)
      ((Scheme.Modules.pushforward q₀).rightDerived n)
      (relativeTopDifferentialCoefficientsFunctor q₁ n)
      ((Scheme.Modules.pushforward q₁).rightDerived n)
      ((Modules.restrictFunctor j).obj N)
      (relativeHigherRestrictionIso q₀ b q₁ k HB n)
      (affineRelativeTraceHom (A := (A : Type u)) R ι (i₀ ≫ a) q₀ (j ≫ f)
        (H₀.paste_horiz h) n e ((Modules.restrictFunctor j).obj N))
      (affineRelativeTraceHom (A := (B : Type u)) R ι c q₁ g H n e
        ((Modules.restrictFunctor k).obj ((Modules.restrictFunctor j).obj N)))
  have ho₀ : P (b ≫ (i₀ ≫ a)) (k ≫ (j ≫ f))
      (HB.paste_horiz (H₀.paste_horiz h)) :=
    relativeHigherTraceSquare_nat q₀ b q₁ k HB n
      ((Modules.restrictFunctor j).obj N)
      (affineRelativeTraceHom (A := (A : Type u)) R ι (i₀ ≫ a) q₀ (j ≫ f)
        (H₀.paste_horiz h) n e ((Modules.restrictFunctor j).obj N))
      (affineRelativeTraceHom (A := (B : Type u)) R ι (b ≫ (i₀ ≫ a)) q₁
        (k ≫ (j ≫ f)) (HB.paste_horiz (H₀.paste_horiz h)) n e
        ((Modules.restrictFunctor k).obj ((Modules.restrictFunctor j).obj N))) hoRaw
  have hpath : b ≫ (i₀ ≫ a) = i₁ ≫ a := by
    simp only [← Category.assoc, hb]
  have ho : P (i₁ ≫ a) ((k ≫ j) ≫ f) (H₁.paste_horiz h) :=
    transport (fun c g => IsPullback c q₁ (toSpec R ι) g) P
      hpath (Category.assoc k j f).symm
      (HB.paste_horiz (H₀.paste_horiz h)) (H₁.paste_horiz h) ho₀
  let : ((Modules.restrictFunctor j ⋙ Modules.restrictFunctor k).obj
      N).IsQuasicoherent := inferInstanceAs ((N.restrict j).restrict k).IsQuasicoherent
  have hn : traceLocalNaturalityEquation
      (relativeTopDifferentialCoefficientsFunctor q₁ n)
      ((Scheme.Modules.pushforward q₁).rightDerived n) (𝟭 (Spec B).Modules)
      (N := (Modules.restrictFunctor k).obj ((Modules.restrictFunctor j).obj N))
      (N' := (Modules.restrictFunctor (k ≫ j)).obj N)
      ((restrictFunctorComp k j).inv.app N)
      (affineRelativeTraceHom (A := (B : Type u)) R ι (i₁ ≫ a) q₁
        ((k ≫ j) ≫ f) (H₁.paste_horiz h) n e
        ((Modules.restrictFunctor k).obj ((Modules.restrictFunctor j).obj N)))
      (affineRelativeTraceHom (A := (B : Type u)) R ι (i₁ ≫ a) q₁
        ((k ≫ j) ≫ f) (H₁.paste_horiz h) n e
        ((Modules.restrictFunctor (k ≫ j)).obj N)) :=
    affineRelativeTraceHom_naturality_equation (A := (B : Type u)) R ι (i₁ ≫ a) q₁
      ((k ≫ j) ≫ f) (H₁.paste_horiz h) n e
      (N := (Modules.restrictFunctor k).obj ((Modules.restrictFunctor j).obj N))
      (N' := (Modules.restrictFunctor (k ≫ j)).obj N)
      ((restrictFunctorComp k j).inv.app N)
  simp only [hb] at hc
  dsimp -proj only [P, compositeTraceNatRestrictionSquare] at ho
  dsimp -proj only [relativeHigherFunctor, Functor.comp_map] at hc
  dsimp -proj only [traceLocalNaturalityEquation, Functor.id_obj, Functor.id_map,
    Functor.comp_obj] at hn
  dsimp -proj only [Scheme.Modules.InternalHom.restrictionHomMap]
  have paste := traceLocalHomFactory_refine
    (relativeTopDifferentialCoefficientsFunctor p n)
    ((Scheme.Modules.pushforward p).rightDerived n)
    (Modules.restrictFunctor j) (Modules.restrictFunctor k)
    (Modules.restrictFunctor (k ≫ j)) (restrictFunctorComp k j)
    (relativeTopDifferentialCoefficientsFunctor q₀ n)
    ((Scheme.Modules.pushforward q₀).rightDerived n)
    (relativeTopDifferentialCoefficientsFunctor q₁ n)
    ((Scheme.Modules.pushforward q₁).rightDerived n)
    (relativeHigherRestrictionIso p i₀ q₀ j H₀ n)
    (relativeHigherRestrictionIso q₀ b q₁ k HB n)
    (relativeHigherRestrictionIso p i₁ q₁ (k ≫ j) H₁ n) N
    (affineRelativeTraceHom (A := (A : Type u)) R ι (i₀ ≫ a) q₀ (j ≫ f)
      (H₀.paste_horiz h) n e ((Modules.restrictFunctor j).obj N))
    (affineRelativeTraceHom (A := (B : Type u)) R ι (i₁ ≫ a) q₁ ((k ≫ j) ≫ f)
      (H₁.paste_horiz h) n e ((Modules.restrictFunctor (k ≫ j)).obj N))
    (affineRelativeTraceHom (A := (B : Type u)) R ι (i₁ ≫ a) q₁ ((k ≫ j) ≫ f)
      (H₁.paste_horiz h) n e ((Modules.restrictFunctor k).obj
        ((Modules.restrictFunctor j).obj N)))
  have pasteComp := paste hc
  dsimp -proj only [Functor.comp_obj] at pasteComp ho
  have pasteOpen := pasteComp ho
  have hFinal := pasteOpen hn
  have hOpaque := traceLocalHomFactory_refine_eq
    (relativeTopDifferentialCoefficientsFunctor p n)
    ((Scheme.Modules.pushforward p).rightDerived n)
    (Modules.restrictFunctor j) (Modules.restrictFunctor k)
    (Modules.restrictFunctor (k ≫ j)) (restrictFunctorComp k j)
    (relativeTopDifferentialCoefficientsFunctor q₀ n)
    ((Scheme.Modules.pushforward q₀).rightDerived n)
    (relativeTopDifferentialCoefficientsFunctor q₁ n)
    ((Scheme.Modules.pushforward q₁).rightDerived n)
    (relativeHigherRestrictionIso p i₀ q₀ j H₀ n)
    (relativeHigherRestrictionIso p i₁ q₁ (k ≫ j) H₁ n) N
    (affineRelativeTraceHom (A := (A : Type u)) R ι (i₀ ≫ a) q₀ (j ≫ f)
      (H₀.paste_horiz h) n e ((Modules.restrictFunctor j).obj N))
    (affineRelativeTraceHom (A := (B : Type u)) R ι (i₁ ≫ a) q₁ ((k ≫ j) ≫ f)
      (H₁.paste_horiz h) n e ((Modules.restrictFunctor (k ≫ j)).obj N))
    (relativeAffineTraceLocal R ι a p f h n e j N)
    (relativeAffineTraceLocal R ι a p f h n e (k ≫ j) N)
    (relativeAffineTraceLocal_factored R ι a p f h n e j N)
    (relativeAffineTraceLocal_factored R ι a p f h n e (k ≫ j) N)
    hFinal
  dsimp -proj only [Functor.comp_obj] at hOpaque
  dsimp -proj only [Modules.restrict, Functor.comp_obj]
  exact hOpaque
private theorem relativeAffineTraceLocal_congr (n : ℕ) (e : ι ≃ Fin (n + 1))
    {A : CommRingCat.{u}} {j k : Spec A ⟶ Y} [IsOpenImmersion j] [IsOpenImmersion k]
    (w : j = k) (N : Y.Modules) [N.IsQuasicoherent] :
    relativeAffineTraceLocal R ι a p f h n e j N ≫
        (restrictFunctorCongr w).hom.app N =
      (restrictFunctorCongr w).hom.app ((relativeHigherFunctor p n).obj N) ≫
        relativeAffineTraceLocal R ι a p f h n e k N := by
  subst k
  have hc (M : Y.Modules) :
      (restrictFunctorCongr (rfl : j = j)).hom.app M = 𝟙 _ := by
    ext U x
    change M.presheaf.map (𝟙 _) x = x
    rw [M.presheaf.map_id]; rfl
  simp only [hc, Category.id_comp, Category.comp_id]
set_option backward.isDefEq.respectTransparency true in
set_option backward.isDefEq.respectTransparency.types true in
private theorem relativeAffineTraceLocal_square
    (n : ℕ) (e : ι ≃ Fin (n + 1)) {A : CommRingCat.{u}} {W : Scheme.{u}}
    (i : W ⟶ X) (q : W ⟶ Spec A) (j : Spec A ⟶ Y)
    [IsOpenImmersion i] [IsOpenImmersion j] (H : IsPullback i q p j)
    (N : Y.Modules) [N.IsQuasicoherent] :
    traceLocalHomFactoryEquation
      (relativeTopDifferentialCoefficientsFunctor p n)
      ((Scheme.Modules.pushforward p).rightDerived n) (Modules.restrictFunctor j)
      (relativeTopDifferentialCoefficientsFunctor q n)
      ((Scheme.Modules.pushforward q).rightDerived n)
      (relativeHigherRestrictionIso p i q j H n) N
      (relativeAffineTraceLocal R ι a p f h n e j N)
      (affineRelativeTraceHom (A := (A : Type u)) R ι (i ≫ a) q (j ≫ f)
        (H.paste_horiz h) n e (N.restrict j)) := by
  let E := H.isoPullback
  let i' := pullback.fst p j
  let q' := pullback.snd p j
  let H' := IsPullback.of_hasPullback p j
  let HE : IsPullback E.inv q' q (𝟙 (Spec A)) :=
    IsPullback.of_horiz_isIso
      ⟨H.isoPullback_inv_snd.trans (Category.comp_id q').symm⟩
  let M := (Modules.restrictFunctor j).obj N
  have transport {S T : Type _} (Q : S → T → Prop)
      (P : ∀ s t, Q s t → Prop) {s s' : S} {t t' : T}
      (hs : s = s') (ht : t = t') (q : Q s t) (q' : Q s' t')
      (hq : P s t q) : P s' t' q' := by
    cases hs
    cases ht
    exact (congrArg (P s t) (Subsingleton.elim q q')).mp hq
  let P (c : pullback p j ⟶ ProjectiveSpace R ι)
      (g : Spec (@CommRingCat.of (A : Type u) (CommRingCat.commRing A)) ⟶
        Spec (.of R)) (Hc : IsPullback c q' (toSpec R ι) g) : Prop :=
    compositeTraceRestrictionSquare (𝟭 (Spec A).Modules)
      (relativeTopDifferentialCoefficientsFunctor q n)
      ((Scheme.Modules.pushforward q).rightDerived n)
      (relativeTopDifferentialCoefficientsFunctor q' n)
      ((Scheme.Modules.pushforward q').rightDerived n) M
      ((identityHigherModelIso q E.inv q' HE n).hom.app M)
      (affineRelativeTraceHom (A := (A : Type u)) R ι (i ≫ a) q (j ≫ f)
        (H.paste_horiz h) n e M)
      (affineRelativeTraceHom (A := (A : Type u)) R ι c q' g Hc n e M)
  have ht₀ : P (E.inv ≫ (i ≫ a))
      ((𝟙 (Spec (@CommRingCat.of (A : Type u) (CommRingCat.commRing A)))) ≫ (j ≫ f))
      (HE.paste_horiz (H.paste_horiz h)) :=
    affineRelativeTraceHom_identity_equation (A := (A : Type u)) R ι (i ≫ a) q
      (j ≫ f) (H.paste_horiz h) E.inv q' HE n e M
  have hpath : E.inv ≫ (i ≫ a) = i' ≫ a := by
    rw [← Category.assoc, H.isoPullback_inv_fst]
  have ht : P (i' ≫ a) (j ≫ f) (H'.paste_horiz h) :=
    transport (fun c g => IsPullback c q' (toSpec R ι) g) P
      hpath (Category.id_comp (j ≫ f))
      (HE.paste_horiz (H.paste_horiz h)) (H'.paste_horiz h) ht₀
  dsimp -proj only [P, compositeTraceRestrictionSquare, Functor.id_obj,
    Functor.id_map, relativeHigherFunctor, Functor.comp_obj] at ht
  have hs := traceCanonicalLocalEquation p i q j H n N
    (relativeAffineTraceLocal R ι a p f h n e j N)
    (affineRelativeTraceHom (A := (A : Type u)) R ι (i' ≫ a) q' (j ≫ f)
      (H'.paste_horiz h) n e M)
    (affineRelativeTraceHom (A := (A : Type u)) R ι (i ≫ a) q (j ≫ f)
      (H.paste_horiz h) n e M)
    (relativeAffineTraceLocal_factored R ι a p f h n e j N) ht
  dsimp -proj only [Modules.restrict]
  exact hs

set_option backward.isDefEq.respectTransparency true in
set_option backward.isDefEq.respectTransparency.types true in
private theorem relativeProjectiveHigherTrace_exists [Y.IsSeparated]
    (n : ℕ) (e : ι ≃ Fin (n + 1)) (N : Y.Modules) [N.IsQuasicoherent] :
    ∃! t : (relativeHigherFunctor p n).obj N ⟶ N,
      ∀ c : AffineTraceChart Y,
        (Modules.restrictFunctor (affineTraceChartMap c)).map t =
          relativeAffineTraceLocal R ι a p f h n e (affineTraceChartMap c) N := by
  apply affineTrace_existsUnique ((relativeHigherFunctor p n).obj N) N
    (fun {A} j _ => relativeAffineTraceLocal R ι a p f h n e j N)
  · intro A B j k _ _
    exact relativeAffineTraceLocal_refine R ι a p f h n e j k N
  · intro A j k _ _ w
    exact relativeAffineTraceLocal_congr R ι a p f h n e w N
/-- The actual top higher-direct-image trace, glued from the original normalized affine traces. -/
@[no_expose]
def relativeProjectiveHigherTrace [Y.IsSeparated] (n : ℕ) (e : ι ≃ Fin (n + 1))
    (N : Y.Modules) [N.IsQuasicoherent] :
    ((Scheme.Modules.pushforward p).rightDerived n).obj
      ((relativeTopDifferentialCoefficientsFunctor p n).obj N) ⟶ N :=
  (relativeProjectiveHigherTrace_exists R ι a p f h n e N).choose
private theorem relativeProjectiveHigherTrace_restrict [Y.IsSeparated]
    (n : ℕ) (e : ι ≃ Fin (n + 1)) {A : CommRingCat.{u}}
    (j : Spec A ⟶ Y) [IsOpenImmersion j] (N : Y.Modules) [N.IsQuasicoherent] :
    (Modules.restrictFunctor j).map (relativeProjectiveHigherTrace R ι a p f h n e N) =
      relativeAffineTraceLocal R ι a p f h n e j N :=
  (relativeProjectiveHigherTrace_exists R ι a p f h n e N).choose_spec.1
    ⟨A, j, inferInstance⟩
/-- The actual higher-image trace preserves every original quasicoherent coefficient map. -/
@[reassoc]
theorem relativeProjectiveHigherTrace_naturality [Y.IsSeparated]
    (n : ℕ) (e : ι ≃ Fin (n + 1)) {N N' : Y.Modules}
    [N.IsQuasicoherent] [N'.IsQuasicoherent] (s : N ⟶ N') :
    ((Scheme.Modules.pushforward p).rightDerived n).map
        ((relativeTopDifferentialCoefficientsFunctor p n).map s) ≫
      relativeProjectiveHigherTrace R ι a p f h n e N' =
        relativeProjectiveHigherTrace R ι a p f h n e N ≫ s := by
  apply affineTraceCharts_hom_ext
  intro c
  simp only [Functor.map_comp, relativeProjectiveHigherTrace_restrict]
  exact relativeAffineTraceLocal_naturality R ι a p f h n e (affineTraceChartMap c) s
set_option backward.isDefEq.respectTransparency true in
set_option backward.isDefEq.respectTransparency.types true in
set_option maxRecDepth 2000 in
-- The native affine model and section objects exceeded recursion depth 1000.
set_option maxHeartbeats 400000 in
-- The original affine model and section component comparison exceeds 200000 heartbeats.
/-- Original affine sections of the global Hn trace have the original polynomial residue trace. -/
theorem relativeProjectiveHigherTrace_affine [Y.IsSeparated]
    (n : ℕ) (e : ι ≃ Fin (n + 1)) {A : CommRingCat.{u}}
    (j : Spec A ⟶ Y) [IsOpenImmersion j] (N : Y.Modules) [N.IsQuasicoherent]
    (x : moduleSpecΓFunctor.obj ((((Scheme.Modules.pushforward p).rightDerived n).obj
      ((relativeTopDifferentialCoefficientsFunctor p n).obj N)).restrict j)) :
    letI : Fintype ι := Fintype.ofEquiv (Fin (n + 1)) e.symm
    letI := projectiveTopDifferentialCoefficients_isQuasicoherent A ι n e (N.restrict j)
    moduleSpecΓFunctor.map ((Modules.restrictFunctor j).map
      (relativeProjectiveHigherTrace R ι a p f h n e N)) x =
    projectiveAffineDifferentialTraceLinearEquiv A ι n e (N.restrict j)
      (moduleHigherDirectImageAffineSectionsLinearEquiv (toSpec A ι) _ (injectiveResolution _) n
        (moduleSpecΓFunctor.map (relativeProjectiveAffineHigherIso R ι a p f h n j N).hom x)) := by
  cases A with
  | of A =>
    let : Fintype ι := Fintype.ofEquiv (Fin (n + 1)) e.symm
    let := projectiveTopDifferentialCoefficients_isQuasicoherent A ι n e (N.restrict j)
    rw [relativeProjectiveHigherTrace_restrict]
    have hx := relativeAffineTraceLocal_sections R ι a p f h n e j N
    dsimp -proj only [traceLocalSectionsEquation] at hx
    have hx' := hx x
    exact hx'
/-- The original normalized trace on the actual derived differential-coefficient image. -/
@[no_expose]
def relativeProjectiveTrace [Y.IsSeparated] (n : ℕ) (e : ι ≃ Fin (n + 1))
    (N : Y.Modules) [N.IsQuasicoherent] :
    DerivedCategory.Plus.ι.obj ((Scheme.Modules.derivedPushforwardPlus p).obj
      ((DerivedCategory.Plus.singleFunctor X.Modules 0).obj
        ((relativeTopDifferentialCoefficientsFunctor p n).obj N))) ⟶
      (DerivedCategory.singleFunctor Y.Modules (n : ℤ)).obj N := by
  let := relativeProjectiveDifferentialCoefficientsDerived_isLE R ι a p f h n e N
  exact (DerivedCategory.homToSingleAddEquiv
    (relativeTopDifferentialCoefficientsDerived p n N) (n : ℤ) N).symm
      (((Scheme.Modules.pushforward p).rightDerivedSingleHomologyIso n).inv.app
        ((relativeTopDifferentialCoefficientsFunctor p n).obj N) ≫
          relativeProjectiveHigherTrace R ι a p f h n e N)
/-- Original top homology of the derived trace is precisely the glued normalized Hn arrow. -/
@[reassoc]
theorem relativeProjectiveTrace_homology [Y.IsSeparated]
    (n : ℕ) (e : ι ≃ Fin (n + 1)) (N : Y.Modules) [N.IsQuasicoherent] :
    (DerivedCategory.homologyFunctor Y.Modules (n : ℤ)).map
        (relativeProjectiveTrace R ι a p f h n e N) ≫
      (DerivedCategory.singleFunctorCompHomologyFunctorIso Y.Modules (n : ℤ)).hom.app N =
    ((Scheme.Modules.pushforward p).rightDerivedSingleHomologyIso n).inv.app
      ((relativeTopDifferentialCoefficientsFunctor p n).obj N) ≫
        relativeProjectiveHigherTrace R ι a p f h n e N := by
  let := relativeProjectiveDifferentialCoefficientsDerived_isLE R ι a p f h n e N
  exact (DerivedCategory.homToSingleAddEquiv
    (relativeTopDifferentialCoefficientsDerived p n N) (n : ℤ) N).apply_symm_apply _
/-- The derived trace carries the original coefficient map through the original direct image. -/
@[reassoc]
theorem relativeProjectiveTrace_naturality [Y.IsSeparated]
    (n : ℕ) (e : ι ≃ Fin (n + 1)) {N N' : Y.Modules}
    [N.IsQuasicoherent] [N'.IsQuasicoherent] (s : N ⟶ N') :
    DerivedCategory.Plus.ι.map ((Scheme.Modules.derivedPushforwardPlus p).map
      ((DerivedCategory.Plus.singleFunctor X.Modules 0).map
        ((relativeTopDifferentialCoefficientsFunctor p n).map s))) ≫
      relativeProjectiveTrace R ι a p f h n e N' =
    relativeProjectiveTrace R ι a p f h n e N ≫
      (DerivedCategory.singleFunctor Y.Modules (n : ℤ)).map s := by
  let := relativeProjectiveDifferentialCoefficientsDerived_isLE R ι a p f h n e N
  let := relativeProjectiveDifferentialCoefficientsDerived_isLE R ι a p f h n e N'
  apply (DerivedCategory.homToSingleAddEquiv
    (relativeTopDifferentialCoefficientsDerived p n N) (n : ℤ) N').injective
  rw [DerivedCategory.homToSingleAddEquiv_naturality_left,
    DerivedCategory.homToSingleAddEquiv_naturality_right]
  simp only [DerivedCategory.homToSingleAddEquiv_apply, relativeProjectiveTrace_homology]
  change _ ≫ (_ ≫ _) = (_ ≫ _) ≫ s
  have hn := ((Scheme.Modules.pushforward p).rightDerivedSingleHomologyIso n).inv.naturality
    ((relativeTopDifferentialCoefficientsFunctor p n).map s)
  change (DerivedCategory.homologyFunctor Y.Modules (n : ℤ)).map
      (DerivedCategory.Plus.ι.map ((Scheme.Modules.derivedPushforwardPlus p).map
        ((DerivedCategory.Plus.singleFunctor X.Modules 0).map
          ((relativeTopDifferentialCoefficientsFunctor p n).map s)))) ≫
      ((Scheme.Modules.pushforward p).rightDerivedSingleHomologyIso n).inv.app _ =
    ((Scheme.Modules.pushforward p).rightDerivedSingleHomologyIso n).inv.app _ ≫
      ((Scheme.Modules.pushforward p).rightDerived n).map
        ((relativeTopDifferentialCoefficientsFunctor p n).map s) at hn
  rw [← Category.assoc, hn, Category.assoc, relativeProjectiveHigherTrace_naturality]
  exact (Category.assoc _ _ _).symm
set_option backward.isDefEq.respectTransparency true in
set_option backward.isDefEq.respectTransparency.types true in
set_option maxHeartbeats 400000 in
-- The original chart transport and open composition exceeded 200000 heartbeats.
/-- The global Hn trace commutes with the original comparisons on every Cartesian open square. -/
theorem relativeProjectiveHigherTrace_open [Y.IsSeparated]
    (n : ℕ) (e : ι ≃ Fin (n + 1)) {W Z : Scheme.{u}}
    (i : W ⟶ X) (q : W ⟶ Z) (j : Z ⟶ Y)
    [IsOpenImmersion i] [IsOpenImmersion j] (H : IsPullback i q p j)
    (N : Y.Modules) [N.IsQuasicoherent] :
    letI : Z.IsSeparated := ⟨by rw [← terminal.comp_from j]; infer_instance⟩
    (Scheme.Modules.higherDirectImageOpenRestrictionIso i q p j H n).hom.app
        ((relativeTopDifferentialCoefficientsFunctor p n).obj N) ≫
      ((Scheme.Modules.pushforward q).rightDerived n).map
        ((relativeTopDifferentialCoefficientsRestrictionIso p i q j H.w n).hom.app N) ≫
      relativeProjectiveHigherTrace R ι (i ≫ a) q (j ≫ f) (H.paste_horiz h) n e
        (N.restrict j) =
    (Modules.restrictFunctor j).map (relativeProjectiveHigherTrace R ι a p f h n e N) := by
  let : Z.IsSeparated := ⟨by rw [← terminal.comp_from j]; infer_instance⟩
  rw [← Category.assoc, ← relativeHigherRestrictionIso_hom]
  apply affineTraceCharts_hom_ext
  rintro ⟨A, k, hk⟩
  rcases A with ⟨A⟩
  let : IsOpenImmersion k := hk
  let b := pullback.fst q k
  let r := pullback.snd q k
  let HB := IsPullback.of_hasPullback q k
  let HC := HB.paste_horiz H
  have hzL := relativeAffineTraceLocal_square R ι a p f h n e (b ≫ i) r (k ≫ j) HC N
  have transport {S T : Type _} (Q : S → T → Prop)
      (P : ∀ s t, Q s t → Prop) {s s' : S} {t t' : T}
      (hs : s = s') (ht : t = t') (q : Q s t) (q' : Q s' t')
      (hq : P s t q) : P s' t' q' := by
    cases hs
    cases ht
    exact (congrArg (P s t) (Subsingleton.elim q q')).mp hq
  let P (d : pullback q k ⟶ ProjectiveSpace R ι)
      (g : Spec (.of A) ⟶
        Spec (.of R)) (Hd : IsPullback d r (toSpec R ι) g) : Prop :=
    traceLocalHomFactoryEquation
      (relativeTopDifferentialCoefficientsFunctor q n)
      ((Scheme.Modules.pushforward q).rightDerived n) (Modules.restrictFunctor k)
      (relativeTopDifferentialCoefficientsFunctor r n)
      ((Scheme.Modules.pushforward r).rightDerived n)
      (relativeHigherRestrictionIso q b r k HB n) ((Modules.restrictFunctor j).obj N)
      (relativeAffineTraceLocal R ι (i ≫ a) q (j ≫ f) (H.paste_horiz h) n e k
        ((Modules.restrictFunctor j).obj N))
      (affineRelativeTraceHom (A := A) R ι d r g Hd n e
        ((Modules.restrictFunctor k).obj ((Modules.restrictFunctor j).obj N)))
  have hzK₀ : P (b ≫ (i ≫ a)) (k ≫ (j ≫ f)) (HB.paste_horiz (H.paste_horiz h)) :=
    relativeAffineTraceLocal_factored R ι (i ≫ a) q (j ≫ f) (H.paste_horiz h) n e k
      ((Modules.restrictFunctor j).obj N)
  have hzK : P ((b ≫ i) ≫ a) ((k ≫ j) ≫ f) (HC.paste_horiz h) :=
    transport (fun d g => IsPullback d r (toSpec R ι) g) P
      (Category.assoc b i a).symm (Category.assoc k j f).symm
      (HB.paste_horiz (H.paste_horiz h)) (HC.paste_horiz h) hzK₀
  let : ((Modules.restrictFunctor j ⋙ Modules.restrictFunctor k).obj
      N).IsQuasicoherent := inferInstanceAs ((N.restrict j).restrict k).IsQuasicoherent
  have hn := affineRelativeTraceHom_naturality_equation (A := A) R ι
    ((b ≫ i) ≫ a) r ((k ≫ j) ≫ f) (HC.paste_horiz h) n e
    (N := (Modules.restrictFunctor (k ≫ j)).obj N)
    (N' := (Modules.restrictFunctor k).obj ((Modules.restrictFunctor j).obj N))
    ((restrictFunctorComp k j).hom.app N)
  dsimp -proj only [P, Modules.restrict] at hzK
  dsimp -proj only [Modules.restrict] at hzL
  dsimp -proj only [traceLocalNaturalityEquation, Functor.id_obj, Functor.id_map,
    Functor.comp_obj] at hn
  have hs := traceOpenLocalEquation p i q j H b r k HB n N
    (relativeProjectiveHigherTrace R ι a p f h n e N)
    (relativeAffineTraceLocal R ι a p f h n e (k ≫ j) N)
    (relativeAffineTraceLocal R ι (i ≫ a) q (j ≫ f) (H.paste_horiz h) n e k
      ((Modules.restrictFunctor j).obj N))
    (affineRelativeTraceHom (A := A) R ι ((b ≫ i) ≫ a) r
      ((k ≫ j) ≫ f) (HC.paste_horiz h) n e ((Modules.restrictFunctor (k ≫ j)).obj N))
    (affineRelativeTraceHom (A := A) R ι ((b ≫ i) ≫ a) r
      ((k ≫ j) ≫ f) (HC.paste_horiz h) n e
      ((Modules.restrictFunctor k).obj ((Modules.restrictFunctor j).obj N))) hn
    (relativeProjectiveHigherTrace_restrict R ι a p f h n e (k ≫ j) N) hzL hzK
  simp only [Functor.map_comp, relativeProjectiveHigherTrace_restrict]
  exact hs
/-- The affine normalization of the original full-derived trace uses its actual Hn map. -/
theorem relativeProjectiveTrace_affine [Y.IsSeparated]
    (n : ℕ) (e : ι ≃ Fin (n + 1)) {A : CommRingCat.{u}}
    (j : Spec A ⟶ Y) [IsOpenImmersion j] (N : Y.Modules) [N.IsQuasicoherent]
    (x : moduleSpecΓFunctor.obj ((((Scheme.Modules.pushforward p).rightDerived n).obj
      ((relativeTopDifferentialCoefficientsFunctor p n).obj N)).restrict j)) :
    letI : Fintype ι := Fintype.ofEquiv (Fin (n + 1)) e.symm
    letI := projectiveTopDifferentialCoefficients_isQuasicoherent A ι n e (N.restrict j)
    moduleSpecΓFunctor.map ((Modules.restrictFunctor j).map
      (((Scheme.Modules.pushforward p).rightDerivedSingleHomologyIso n).hom.app
          ((relativeTopDifferentialCoefficientsFunctor p n).obj N) ≫
        (DerivedCategory.homologyFunctor Y.Modules (n : ℤ)).map
          (relativeProjectiveTrace R ι a p f h n e N) ≫
        (DerivedCategory.singleFunctorCompHomologyFunctorIso Y.Modules (n : ℤ)).hom.app N)) x =
      projectiveAffineDifferentialTraceLinearEquiv A ι n e (N.restrict j)
        (moduleHigherDirectImageAffineSectionsLinearEquiv (toSpec A ι) _ (injectiveResolution _) n
          (moduleSpecΓFunctor.map
            (relativeProjectiveAffineHigherIso R ι a p f h n j N).hom x)) := by
  let : Fintype ι := Fintype.ofEquiv (Fin (n + 1)) e.symm
  let := projectiveTopDifferentialCoefficients_isQuasicoherent A ι n e (N.restrict j)
  rw [relativeProjectiveTrace_homology]
  simp only [Iso.hom_inv_id_app_assoc]
  exact relativeProjectiveHigherTrace_affine R ι a p f h n e j N x
end AlgebraicGeometry.Scheme.Cohomology
