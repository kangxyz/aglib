/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.Cohomology.Injective.RestrictionSections
public import Mathlib.Algebra.Homology.HomologySequence
/-! # Higher cohomology on a two-affine cover with affine intersection

For two actual affine open immersions covering a scheme, together with an
actual affine open immersion whose image is their intersection, the original
injective-resolution global section complex of any quasicoherent module sheaf
is exact in every degree at least two. Consequently the original additive
global-section right-derived functors vanish in those degrees.

No noetherianity or separatedness assumption is imposed; the displayed affine
intersection is the exact geometric hypothesis used. Degree one is not claimed.
-/
@[expose] public section

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry HomologicalComplex
universe u
namespace AlgebraicGeometry.Scheme.Modules
open TwoOpen
variable {X : Scheme.{u}}

lemma pairSections_exactAt (U V : X.Opens) (I : CochainComplex X.Modules ℕ) (n : ℕ)
    (hU : (((sectionsFunctor X U).mapHomologicalComplex _).obj I).ExactAt n)
    (hV : (((sectionsFunctor X V).mapHomologicalComplex _).obj I).ExactAt n) :
    (((pairFunctor X U V).mapHomologicalComplex _).obj I).ExactAt n := by
  rw [exactAt_iff, ShortComplex.ab_exact_iff]
  rintro ⟨a, b⟩ hab
  obtain ⟨c, hc⟩ := (ShortComplex.ab_exact_iff _).mp hU a (congrArg Prod.fst hab)
  obtain ⟨d, hd⟩ := (ShortComplex.ab_exact_iff _).mp hV b (congrArg Prod.snd hab)
  exact ⟨(c, d), Prod.ext hc hd⟩

/-- The original injective resolution is globally acyclic above degree one on
a two-affine cover whose actual intersection is affine. -/
theorem twoAffine_injectiveResolution_exact_add_two
    {R S T : CommRingCat.{u}} (j : Spec R ⟶ X) (k : Spec S ⟶ X) (l : Spec T ⟶ X)
    [IsOpenImmersion j] [IsOpenImmersion k] [IsOpenImmersion l]
    (hcover : j.opensRange ⊔ k.opensRange = ⊤)
    (hoverlap : l.opensRange = j.opensRange ⊓ k.opensRange)
    (M : X.Modules) [M.IsQuasicoherent] (I : InjectiveResolution M) (n : ℕ) :
    (((sectionsFunctor X ⊤).mapHomologicalComplex _).obj I.cocomplex).ExactAt (n + 2) := by
  let S := cochainSequence j.opensRange k.opensRange I.cocomplex
  have hS : S.ShortExact :=
    injectiveResolution_cochainSequence_shortExact _ _ hcover M I
  have hW : S.X₃.ExactAt (n + 1) := by
    change (((sectionsFunctor X (j.opensRange ⊓ k.opensRange)).mapHomologicalComplex _).obj
      I.cocomplex).ExactAt (n + 1)
    rw [← hoverlap]
    exact affineOpen_injectiveResolution_exact_succ l M I n
  have hUV : S.X₂.ExactAt (n + 2) :=
    pairSections_exactAt _ _ _ _
      (affineOpen_injectiveResolution_exact_succ j M I (n + 1))
      (affineOpen_injectiveResolution_exact_succ k M I (n + 1))
  rw [exactAt_iff_isZero_homology]
  exact (hS.homology_exact₁ (n + 1) (n + 2) rfl).isZero_of_both_isZero
    hW.isZero_homology hUV.isZero_homology

/-- Actual right-derived additive global sections vanish in degrees at least
two on a two-affine cover with affine intersection. -/
theorem twoAffine_isZero_rightDerived_add_two
    {R S T : CommRingCat.{u}} (j : Spec R ⟶ X) (k : Spec S ⟶ X) (l : Spec T ⟶ X)
    [IsOpenImmersion j] [IsOpenImmersion k] [IsOpenImmersion l]
    (hcover : j.opensRange ⊔ k.opensRange = ⊤)
    (hoverlap : l.opensRange = j.opensRange ⊓ k.opensRange)
    (M : X.Modules) [M.IsQuasicoherent] (n : ℕ) :
    IsZero (((sectionsFunctor X ⊤).rightDerived (n + 2)).obj M) := by
  let I := injectiveResolution M
  have h := twoAffine_injectiveResolution_exact_add_two j k l hcover hoverlap M I n
  exact h.isZero_homology.of_iso (I.isoRightDerivedObj (sectionsFunctor X ⊤) (n + 2))

end AlgebraicGeometry.Scheme.Modules
