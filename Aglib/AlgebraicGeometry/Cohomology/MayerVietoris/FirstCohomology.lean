/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module
public import Aglib.AlgebraicGeometry.Cohomology.Injective.DegreeZero
public import Aglib.AlgebraicGeometry.Cohomology.MayerVietoris.AffineComparison
/-! # First cohomology and the original two-open restriction cokernel

The degree-zero comparison of an actual injective resolution identifies the
first connecting homomorphism with a map out of original overlap sections.
For two affine opens covering a scheme and quasicoherent coefficients, this
connecting map exhibits actual first right-derived global sections as the
cokernel of the literal signed two-open section difference. Affineness of the
intersection is not needed for this degree-one statement.
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry HomologicalComplex
universe u
namespace AlgebraicGeometry.Scheme.Modules
open TwoOpen
variable {X : Scheme.{u}} (M : X.Modules) (I : InjectiveResolution M)
    (U V : X.Opens) (hUV : U ⊔ V = ⊤)

/-- The actual first connecting map from original overlap sections, computed
through the original resolution augmentation and the cochain exact sequence. -/
def firstConnecting : Γ(M, U ⊓ V) ⟶ ((sectionsFunctor X ⊤).rightDerived 1).obj M :=
  (sectionsHomologyZeroIso M I (U ⊓ V)).hom ≫
    (injectiveResolution_cochainSequence_shortExact U V hUV M I).δ 0 1 rfl ≫
    (I.isoRightDerivedObj (sectionsFunctor X ⊤) 1).inv

lemma difference_firstConnecting :
    (sectionSequence M U V).g ≫ firstConnecting M I U V hUV = 0 := by
  unfold firstConnecting
  rw [← Category.assoc, difference_homologyZero_naturality, Category.assoc,
    ← Category.assoc (homologyMap _ 0), ShortComplex.ShortExact.comp_δ, zero_comp, comp_zero]

/-- Original chart-pair sections, overlap sections, and actual first cohomology. -/
def firstCohomologySequence : ShortComplex AddCommGrpCat.{u} :=
  ShortComplex.mk (sectionSequence M U V).g (firstConnecting M I U V hUV)
    (difference_firstConnecting M I U V hUV)

/-- This sequence is exact for every module sheaf, without quasicoherence or
local acyclicity assumptions. -/
lemma firstCohomologySequence_exact : (firstCohomologySequence M I U V hUV).Exact := by
  let hS := injectiveResolution_cochainSequence_shortExact U V hUV M I
  let T := ShortComplex.mk _ _ (hS.comp_δ 0 1 rfl)
  have e : firstCohomologySequence M I U V hUV ≅ T :=
    ShortComplex.isoMk (pairHomologyZeroIso M I U V)
      (sectionsHomologyZeroIso M I (U ⊓ V)) (I.isoRightDerivedObj (sectionsFunctor X ⊤) 1)
      (difference_homologyZero_naturality M I U V).symm
      (by simp [firstCohomologySequence, firstConnecting, T])
  exact ShortComplex.exact_of_iso e.symm (hS.homology_exact₃ 0 1 rfl)

omit U V hUV in
lemma firstConnecting_epi_of_affine_cover {R S : CommRingCat.{u}}
    (j : Spec R ⟶ X) (k : Spec S ⟶ X) [IsOpenImmersion j] [IsOpenImmersion k]
    (hcover : j.opensRange ⊔ k.opensRange = ⊤) [M.IsQuasicoherent] :
    Epi (firstConnecting M I j.opensRange k.opensRange hcover) := by
  let hS := injectiveResolution_cochainSequence_shortExact _ _ hcover M I
  have hB : (cochainSequence j.opensRange k.opensRange I.cocomplex).X₂.ExactAt 1 :=
    pairSections_exactAt _ _ _ _
      (affineOpen_injectiveResolution_exact_succ j M I 0)
      (affineOpen_injectiveResolution_exact_succ k M I 0)
  have : Epi (hS.δ 0 1 rfl) :=
    (hS.homology_exact₁ 0 1 rfl).epi_f_iff.mpr (hB.isZero_homology.eq_of_tgt _ _)
  unfold firstConnecting
  infer_instance

/-- For an actual two-affine cover, first right-derived global sections are
the cokernel of the original signed restriction map. The overlap may be nonaffine. -/
def twoAffineRightDerivedOneIsoCokernel {R S : CommRingCat.{u}}
    (j : Spec R ⟶ X) (k : Spec S ⟶ X) [IsOpenImmersion j] [IsOpenImmersion k]
    (hcover : j.opensRange ⊔ k.opensRange = ⊤) [M.IsQuasicoherent] :
    ((sectionsFunctor X ⊤).rightDerived 1).obj M ≅
      cokernel (sectionSequence M j.opensRange k.opensRange).g := by
  let : Epi (firstCohomologySequence M I j.opensRange k.opensRange hcover).g :=
    firstConnecting_epi_of_affine_cover M I j k hcover
  exact (firstCohomologySequence_exact M I _ _ hcover).gIsCokernel.coconePointUniqueUpToIso
    (colimit.isColimit _)

/-- The comparison identifies the cokernel quotient with the constructed
connecting map on original overlap sections. -/
lemma firstConnecting_twoAffineRightDerivedOneIsoCokernel_hom
    {R S : CommRingCat.{u}} (j : Spec R ⟶ X) (k : Spec S ⟶ X)
    [IsOpenImmersion j] [IsOpenImmersion k]
    (hcover : j.opensRange ⊔ k.opensRange = ⊤) [M.IsQuasicoherent] :
    firstConnecting M I j.opensRange k.opensRange hcover ≫
      (twoAffineRightDerivedOneIsoCokernel M I j k hcover).hom =
      cokernel.π (sectionSequence M j.opensRange k.opensRange).g := by
  let : Epi (firstCohomologySequence M I j.opensRange k.opensRange hcover).g :=
    firstConnecting_epi_of_affine_cover M I j k hcover
  exact (firstCohomologySequence_exact M I _ _ hcover).gIsCokernel.comp_coconePointUniqueUpToIso_hom
     (colimit.isColimit _) WalkingParallelPair.one

omit I U V hUV in
/-- Surjectivity of the actual section difference kills first derived global
sections on a two-affine cover. -/
theorem twoAffine_isZero_rightDerived_one_of_difference_surjective
    {R S : CommRingCat.{u}} (j : Spec R ⟶ X) (k : Spec S ⟶ X)
    [IsOpenImmersion j] [IsOpenImmersion k]
    (hcover : j.opensRange ⊔ k.opensRange = ⊤) [M.IsQuasicoherent]
    (hs : Function.Surjective (difference M j.opensRange k.opensRange)) :
    IsZero (((sectionsFunctor X ⊤).rightDerived 1).obj M) := by
  let : Epi (sectionSequence M j.opensRange k.opensRange).g :=
    (AddCommGrpCat.epi_iff_surjective _).mpr hs
  exact (isZero_cokernel_of_epi (sectionSequence M j.opensRange k.opensRange).g).of_iso
    (twoAffineRightDerivedOneIsoCokernel M (injectiveResolution M) j k hcover)

end AlgebraicGeometry.Scheme.Modules
