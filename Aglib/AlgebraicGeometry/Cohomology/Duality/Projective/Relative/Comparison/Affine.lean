/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.Cohomology.Duality.Projective.Relative.Comparison
public import Aglib.AlgebraicGeometry.Cohomology.Duality.Projective.Relative.Comparison.AffineModel
public import Aglib.AlgebraicGeometry.Cohomology.DirectImage.QuasiCoherent
public import Aglib.AlgebraicGeometry.Cohomology.Duality.Projective.Relative.Comparison.AffineRaw
public import Aglib.AlgebraicGeometry.Modules.QuasiCoherent.Affine.Isomorphisms

/-!
# The actual normalized trace on an affine base

The native affine normalization proves that the original top higher-image
trace is invertible. This uses the original affine section comparisons and
quasicoherent descent, without a flatness or Noetherianity hypothesis.
-/

@[expose] public section
noncomputable section
set_option autoImplicit false
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open CategoryTheory CategoryTheory.Limits CategoryTheory.Abelian
open AlgebraicGeometry AlgebraicGeometry.ProjectiveSpace AlgebraicGeometry.Scheme.Modules
open AlgebraicGeometry.Scheme.Modules.QuasiCoherent

universe u
attribute [local instance] AlgebraicGeometry.Scheme.Modules.standardHasDerivedCategory
attribute [local instance] AlgebraicGeometry.Scheme.Cohomology.projectiveCoefficientTraceTarget

namespace AlgebraicGeometry.Scheme.Cohomology

variable (R : Type u) [CommRing R] (ι : Type u)
  {A : CommRingCat.{u}} {X : Scheme.{u}}
  (a : X ⟶ ProjectiveSpace R ι) (p : X ⟶ Spec A)
  (f : Spec A ⟶ Spec (.of R)) (h : IsPullback a p (toSpec R ι) f)

set_option backward.isDefEq.respectTransparency true in
set_option backward.isDefEq.respectTransparency.types true in
set_option maxRecDepth 2000 in
-- Instantiating the original affine section formula exceeds recursion depth 1000.
/-- On an affine base, the actual normalized top higher-image trace is an isomorphism. -/
theorem relativeProjectiveHigherTrace_isIso_affine
    (n : ℕ) (e : ι ≃ Fin (n + 1)) (N : (Spec A).Modules) [N.IsQuasicoherent] :
    IsIso (relativeProjectiveHigherTrace R ι a p f h n e N) := by
  let : Fintype ι := Fintype.ofEquiv (Fin (n + 1)) e.symm
  let : IsProper p := MorphismProperty.of_isPullback h inferInstance
  let := relativeProjectiveDifferentialCoefficients_isQuasicoherent R ι a p f h n e N
  let V := ((Scheme.Modules.pushforward p).rightDerived n).obj
    ((relativeTopDifferentialCoefficientsFunctor p n).obj N)
  let : V.IsQuasicoherent := moduleHigherDirectImage_isQuasicoherent p _ n
  let t := relativeProjectiveHigherTrace R ι a p f h n e N
  let J := Scheme.Modules.restrictFunctor (𝟙 (Spec A))
  let W := (relativeTopDifferentialCoefficientsFunctor (toSpec A ι) n).obj
    (N.restrict (𝟙 (Spec A)))
  let : W.IsQuasicoherent :=
    projectiveTopDifferentialCoefficients_isQuasicoherent A ι n e (N.restrict (𝟙 (Spec A)))
  let E₁ := relativeProjectiveAffineHigherIso R ι a p f h n (𝟙 (Spec A)) N
  let E₂ := moduleHigherDirectImageAffineSectionsLinearEquiv (toSpec A ι) W
    (injectiveResolution W) n
  let E₃ := projectiveAffineDifferentialTraceLinearEquiv A ι n e (N.restrict (𝟙 (Spec A)))
  have ht : (fun x => moduleSpecΓFunctor.map (J.map t) x) =
      fun x => E₃ (E₂ (moduleSpecΓFunctor.map E₁.hom x)) := by
    funext x
    exact relativeProjectiveHigherTrace_affine R ι a p f h n e (𝟙 (Spec A)) N x
  let : IsIso (moduleSpecΓFunctor.map (J.map t)) := by
    rw [ConcreteCategory.isIso_iff_bijective]
    change Function.Bijective (fun x => moduleSpecΓFunctor.map (J.map t) x)
    rw [ht]
    exact E₃.bijective.comp (E₂.bijective.comp
      (ConcreteCategory.bijective_of_isIso (moduleSpecΓFunctor.map E₁.hom)))
  let : IsIso (J.map t) :=
    Scheme.Modules.QuasiCoherent.affine_isIso_of_globalSections A (J.map t)
  exact (NatIso.isIso_map_iff Scheme.Modules.restrictFunctorId t).mp inferInstance

end AlgebraicGeometry.Scheme.Cohomology



namespace AlgebraicGeometry.Scheme.Cohomology

private theorem isIso_of_singleSource_homology
    {C : Type*} [Category* C] [Abelian C] [HasDerivedCategory C]
    (n : ℤ) {K : DerivedCategory C} {V W : C}
    (E : K ≅ (DerivedCategory.singleFunctor C n).obj V)
    (t : K ⟶ (DerivedCategory.singleFunctor C n).obj W)
    [IsIso ((DerivedCategory.homologyFunctor C n).map t)] : IsIso t := by
  let S := DerivedCategory.singleFunctor C n
  let H := DerivedCategory.homologyFunctor C n
  let r := E.inv ≫ t
  obtain ⟨s, hs⟩ := S.map_surjective r
  let : IsIso (H.map (S.map s)) := by
    rw [hs]
    change IsIso (H.map (E.inv ≫ t))
    rw [Functor.map_comp]
    infer_instance
  let : IsIso s := by
    apply (NatIso.isIso_map_iff (DerivedCategory.singleFunctorCompHomologyFunctorIso C n) s).mp
    change IsIso (H.map (S.map s))
    infer_instance
  let : IsIso (E.inv ≫ t) := by
    change IsIso r
    rw [← hs]
    infer_instance
  exact IsIso.of_isIso_comp_left E.inv t

/-- For a standard affine polynomial projection carrying any supplied Cartesian
coordinate presentation, the original normalized relative trace is invertible.
The original affine model supplies its full concentration. -/
theorem relativeProjectiveTrace_isIso_standardAffine
    (R : Type u) [CommRing R] (ι : Type u) {A : CommRingCat.{u}}
    (a : ProjectiveSpace A ι ⟶ ProjectiveSpace R ι) (f : Spec A ⟶ Spec (.of R))
    (h : IsPullback a (toSpec A ι) (toSpec R ι) f)
    (n : ℕ) (e : ι ≃ Fin (n + 1)) (N : (Spec A).Modules) [N.IsQuasicoherent] :
    IsIso (relativeProjectiveTrace R ι a (toSpec A ι) f h n e N) := by
  let t := relativeProjectiveTrace R ι a (toSpec A ι) f h n e N
  let H := DerivedCategory.homologyFunctor (Spec (.of A)).Modules (n : ℤ)
  let E := DerivedCategory.Plus.ι.mapIso
    (projectiveDifferentialCoefficientsAffineSingleIso A ι n e N)
  let : IsIso (relativeProjectiveHigherTrace R ι a (toSpec A ι) f h n e N) :=
    relativeProjectiveHigherTrace_isIso_affine R ι a (toSpec A ι) f h n e N
  have ht := relativeProjectiveTrace_homology R ι a (toSpec A ι) f h n e N
  let : IsIso (H.map t) := by
    have hc : IsIso (H.map t ≫
        (DerivedCategory.singleFunctorCompHomologyFunctorIso
          (Spec (.of A)).Modules (n : ℤ)).hom.app N) := by
      rw [ht]
      infer_instance
    let := hc
    exact IsIso.of_isIso_comp_right _
      ((DerivedCategory.singleFunctorCompHomologyFunctorIso
        (Spec (.of A)).Modules (n : ℤ)).hom.app N)
  exact isIso_of_singleSource_homology (n : ℤ) E t

/-- The literal normalized Serre map is bijective over a standard affine polynomial
projection, with any supplied Cartesian coordinate presentation and every Ext degree. -/
theorem relativeProjectiveSerreMap_bijective_standardAffine
    (R : Type u) [CommRing R] (ι : Type u) {A : CommRingCat.{u}} [IsNoetherianRing A]
    (a : ProjectiveSpace A ι ⟶ ProjectiveSpace R ι) (f : Spec A ⟶ Spec (.of R))
    (h : IsPullback a (toSpec A ι) (toSpec R ι) f)
    (n : ℕ) (e : ι ≃ Fin (n + 1)) (N : (Spec A).Modules) [N.IsQuasicoherent]
    (M : (ProjectiveSpace A ι).Modules)
    (hM : affineLocallyFiniteType (ProjectiveSpace A ι) M) (q : ℕ) :
    Function.Bijective (relativeProjectiveSerreMap R ι a (toSpec A ι) f h n e N M q) := by
  let F := Scheme.Modules.derivedPushforwardPlus (toSpec A ι) ⋙ DerivedCategory.Plus.ι
  let t := relativeProjectiveTrace R ι a (toSpec A ι) f h n e N
  let : IsIso t := relativeProjectiveTrace_isIso_standardAffine R ι a f h n e N
  let B := Iso.homCongr
    (Iso.refl (F.obj ((DerivedCategory.Plus.singleFunctor (ProjectiveSpace A ι).Modules 0).obj M)))
    ((shiftFunctor (DerivedCategory (Spec A).Modules) (q : ℤ)).mapIso (asIso t))
  have heq : (relativeProjectiveSerreMap R ι a (toSpec A ι) f h n e N M q : _ → _) =
      B ∘ (fun x : Ext.{u + 1} M
        ((relativeTopDifferentialCoefficientsFunctor (toSpec A ι) n).obj N) q =>
          x.homPlus.map F) := by
    funext x
    rw [relativeProjectiveSerreMap_apply]
    change _ = 𝟙 _ ≫ _ ≫ _
    rw [Category.id_comp]
    rfl
  rw [heq]
  exact B.bijective.comp
    (projectiveDerivedPushforwardDifferentialExt_bijective A ι n e N M hM q)

end AlgebraicGeometry.Scheme.Cohomology
