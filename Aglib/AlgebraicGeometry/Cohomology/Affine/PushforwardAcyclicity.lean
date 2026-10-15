/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.Cohomology.Injective.RestrictionSections
public import Aglib.Topology.Sheaves.BasisExactness
public import Mathlib.AlgebraicGeometry.Morphisms.Affine
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.Limits
/-! # Quasicoherent acyclicity for affine direct image

Actual ambient injective resolutions are exact after direct image in positive
degrees. The proof uses sections on inverse images of affine opens and the
original affine cohomology theorem, without finite or flat hypotheses.
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry TopologicalSpace
universe u
namespace AlgebraicGeometry.Scheme.Modules
open TwoOpen

/-- Sections of an actual injective resolution are exact in positive degree on any affine open. -/
theorem isAffineOpen_injectiveResolution_exact_succ {Z : Scheme.{u}}
    (U : Z.Opens) (hU : IsAffineOpen U) (M : Z.Modules) [M.IsQuasicoherent]
    (I : InjectiveResolution M) (n : ℕ) :
    (((sectionsFunctor Z U).mapHomologicalComplex _).obj I.cocomplex).ExactAt (n + 1) := by
  simpa only [hU.opensRange_fromSpec] using
    affineOpen_injectiveResolution_exact_succ hU.fromSpec M I n

/-- Direct image of the original injective resolution is exact in every positive degree. -/
theorem affinePushforward_injectiveResolution_exact_succ {Z X : Scheme.{u}}
    (f : Z ⟶ X) [IsAffineHom f] (M : Z.Modules) [M.IsQuasicoherent]
    (I : InjectiveResolution M) (n : ℕ) :
    (((Scheme.Modules.pushforward f).mapHomologicalComplex _).obj I.cocomplex).ExactAt
      (n + 1) := by
  let K := ((Scheme.Modules.pushforward f).mapHomologicalComplex _).obj I.cocomplex
  let F := SheafOfModules.toSheaf X.ringCatSheaf
  let : F.Faithful := inferInstanceAs
    (SheafOfModules.toSheaf X.ringCatSheaf).Faithful
  let : F.Additive := ⟨by intros; rfl⟩
  let : PreservesFiniteColimits F := ⟨fun _ ↦ inferInstance⟩
  let : PreservesFiniteLimits F := inferInstanceAs
    (PreservesFiniteLimits (SheafOfModules.toSheaf X.ringCatSheaf))
  have h : ((F.mapHomologicalComplex _).obj K).ExactAt (n + 1) := by
    apply TopCat.Sheaf.exactAt_of_sections_on_basis _ _ X.isBasis_affineOpens
    intro U hU
    change (((sectionsFunctor Z (f ⁻¹ᵁ U)).mapHomologicalComplex _).obj I.cocomplex).ExactAt
      (n + 1)
    exact isAffineOpen_injectiveResolution_exact_succ _ (hU.preimage f) M I n
  exact (ShortComplex.exact_map_iff_of_faithful (K.sc (n + 1)) F).mp h

/-- All higher original right-derived direct images of quasicoherent sheaves vanish for an
  affine morphism. -/
theorem isZero_rightDerived_pushforward_succ {Z X : Scheme.{u}}
    (f : Z ⟶ X) [IsAffineHom f] (M : Z.Modules) [M.IsQuasicoherent] (n : ℕ) :
    IsZero (((Scheme.Modules.pushforward f).rightDerived (n + 1)).obj M) := by
  let I := injectiveResolution M
  have h := affinePushforward_injectiveResolution_exact_succ f M I n
  exact ((HomologicalComplex.exactAt_iff_isZero_homology _ _).mp h).of_iso
    (I.isoRightDerivedObj (Scheme.Modules.pushforward f) (n + 1))

end AlgebraicGeometry.Scheme.Modules
