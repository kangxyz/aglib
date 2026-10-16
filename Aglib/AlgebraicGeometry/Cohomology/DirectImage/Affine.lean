/-
Copyright (c) 2026 algebraic-geometry contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.Cohomology.DirectImage.Affine.Resolution
public import Aglib.CategoryTheory.Abelian.RightDerived.Cochain

/-!
# Actual higher direct images over an affine target

The original right-derived pushforward is computed by the supplied native
module injective resolution. The actual tilde–global-sections counit is a
quasi-isomorphism, so its original homology comparison identifies every
higher direct image with tilde of the actual affine section-complex homology.
In particular, these actual higher direct images are quasicoherent for a
qcqs morphism and a quasicoherent coefficient.
-/

@[expose] public section

noncomputable section

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open CategoryTheory CategoryTheory.Limits CategoryTheory.Abelian HomologicalComplex
open AlgebraicGeometry TopologicalSpace Opposite

namespace AlgebraicGeometry.Scheme.Cohomology

universe u

variable {R : Type u} [CommRing R] {X : Scheme.{u}}
  (f : X ⟶ Spec (CommRingCat.of R)) [QuasiCompact f] [QuasiSeparated f]
  (M : X.Modules) [M.IsQuasicoherent]

/-- The actual higher direct image is tilde of homology of the original affine sections
of the actual pushed-forward injective resolution. -/
def moduleHigherDirectImageAffineIso (I : InjectiveResolution M) (n : ℕ) :
    ((Scheme.Modules.pushforward f).rightDerived n).obj M ≅
      tilde (((moduleSpecΓFunctor.mapHomologicalComplex (.up ℤ)).obj
        (((Scheme.Modules.pushforward f).mapHomologicalComplex (.up ℤ)).obj
          I.cochainComplex)).homology (n : ℤ)) := by
  let K := ((Scheme.Modules.pushforward f).mapHomologicalComplex (.up ℤ)).obj I.cochainComplex
  let : QuasiIso (Scheme.Modules.Complex.tildeGlobalSectionsCounit
      (CommRingCat.of R) (.up ℤ) K) := moduleResolutionPushforwardTildeCounit_quasiIso f M I
  exact I.isoRightDerivedObjCochain (Scheme.Modules.pushforward f) n ≪≫
    (Scheme.Modules.Complex.tildeGlobalSectionsHomologyIso
      (CommRingCat.of R) (.up ℤ) K (n : ℤ)).symm

/-- The comparison retains the native right-derived comparison and the original counit
homology map, with the native exact-tilde homology isomorphism. -/
@[reassoc]
theorem moduleHigherDirectImageAffineIso_hom_comp (I : InjectiveResolution M) (n : ℕ) :
    let K := ((Scheme.Modules.pushforward f).mapHomologicalComplex (.up ℤ)).obj I.cochainComplex
    letI : QuasiIso (Scheme.Modules.Complex.tildeGlobalSectionsCounit
      (CommRingCat.of R) (.up ℤ) K) := moduleResolutionPushforwardTildeCounit_quasiIso f M I
    (moduleHigherDirectImageAffineIso f M I n).hom ≫
        (Scheme.Modules.Complex.tildeGlobalSectionsHomologyIso
          (CommRingCat.of R) (.up ℤ) K (n : ℤ)).hom =
      (I.isoRightDerivedObjCochain (Scheme.Modules.pushforward f) n).hom := by
  let K := ((Scheme.Modules.pushforward f).mapHomologicalComplex (.up ℤ)).obj I.cochainComplex
  let : QuasiIso (Scheme.Modules.Complex.tildeGlobalSectionsCounit
      (CommRingCat.of R) (.up ℤ) K) := moduleResolutionPushforwardTildeCounit_quasiIso f M I
  change (I.isoRightDerivedObjCochain (Scheme.Modules.pushforward f) n).hom ≫
      (Scheme.Modules.Complex.tildeGlobalSectionsHomologyIso
        (CommRingCat.of R) (.up ℤ) K (n : ℤ)).inv ≫
      (Scheme.Modules.Complex.tildeGlobalSectionsHomologyIso
        (CommRingCat.of R) (.up ℤ) K (n : ℤ)).hom = _
  simp only [Iso.inv_hom_id, Category.comp_id]

/-- Every actual higher direct image of a quasicoherent module under a qcqs morphism to a
spectrum is quasicoherent, without Noetherianity or a finite generation hypothesis. -/
theorem moduleHigherDirectImageAffine_isQuasicoherent (n : ℕ) :
    (((Scheme.Modules.pushforward f).rightDerived n).obj M).IsQuasicoherent :=
  (SheafOfModules.isQuasicoherent (Spec (CommRingCat.of R)).ringCatSheaf).prop_of_iso
    (moduleHigherDirectImageAffineIso f M (injectiveResolution M) n).symm inferInstance

end AlgebraicGeometry.Scheme.Cohomology
