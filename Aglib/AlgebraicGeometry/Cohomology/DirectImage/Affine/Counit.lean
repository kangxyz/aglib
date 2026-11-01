/-
Copyright (c) 2026 algebraic-geometry contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.Cohomology.DirectImage.ResolutionSections.Pushforward.Spec
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
  (f : X ⟶ Spec (CommRingCat.of R))
  (M : X.Modules)

/-- The actual higher image from the original resolution counit. -/
def moduleHigherDirectImageAffineIso_of_counit_quasiIso
    (I : InjectiveResolution M)
    (hI : QuasiIso (Scheme.Modules.Complex.tildeGlobalSectionsCounit
      (CommRingCat.of R) (.up ℤ)
      (((Scheme.Modules.pushforward f).mapHomologicalComplex (.up ℤ)).obj I.cochainComplex)))
    (n : ℕ) :
    ((Scheme.Modules.pushforward f).rightDerived n).obj M ≅
      tilde (((moduleSpecΓFunctor.mapHomologicalComplex (.up ℤ)).obj
        (((Scheme.Modules.pushforward f).mapHomologicalComplex (.up ℤ)).obj
          I.cochainComplex)).homology (n : ℤ)) := by
  let K := ((Scheme.Modules.pushforward f).mapHomologicalComplex (.up ℤ)).obj I.cochainComplex
  let : QuasiIso (Scheme.Modules.Complex.tildeGlobalSectionsCounit
      (CommRingCat.of R) (.up ℤ) K) := hI
  exact I.isoRightDerivedObjCochain (Scheme.Modules.pushforward f) n ≪≫
    (Scheme.Modules.Complex.tildeGlobalSectionsHomologyIso
      (CommRingCat.of R) (.up ℤ) K (n : ℤ)).symm

/-- The comparison keeps the original resolution and counit homology maps. -/
@[reassoc]
theorem moduleHigherDirectImageAffineIso_of_counit_quasiIso_hom_comp
    (I : InjectiveResolution M)
    (hI : QuasiIso (Scheme.Modules.Complex.tildeGlobalSectionsCounit
      (CommRingCat.of R) (.up ℤ)
      (((Scheme.Modules.pushforward f).mapHomologicalComplex (.up ℤ)).obj I.cochainComplex)))
    (n : ℕ) :
    let K := ((Scheme.Modules.pushforward f).mapHomologicalComplex (.up ℤ)).obj I.cochainComplex
    letI : QuasiIso (Scheme.Modules.Complex.tildeGlobalSectionsCounit
      (CommRingCat.of R) (.up ℤ) K) := hI
    (moduleHigherDirectImageAffineIso_of_counit_quasiIso f M I hI n).hom ≫
        (Scheme.Modules.Complex.tildeGlobalSectionsHomologyIso
          (CommRingCat.of R) (.up ℤ) K (n : ℤ)).hom =
      (I.isoRightDerivedObjCochain (Scheme.Modules.pushforward f) n).hom := by
  let K := ((Scheme.Modules.pushforward f).mapHomologicalComplex (.up ℤ)).obj I.cochainComplex
  let : QuasiIso (Scheme.Modules.Complex.tildeGlobalSectionsCounit
      (CommRingCat.of R) (.up ℤ) K) := hI
  change (I.isoRightDerivedObjCochain (Scheme.Modules.pushforward f) n).hom ≫
      (Scheme.Modules.Complex.tildeGlobalSectionsHomologyIso
        (CommRingCat.of R) (.up ℤ) K (n : ℤ)).inv ≫
      (Scheme.Modules.Complex.tildeGlobalSectionsHomologyIso
        (CommRingCat.of R) (.up ℤ) K (n : ℤ)).hom = _
  simp only [Iso.inv_hom_id, Category.comp_id]

end AlgebraicGeometry.Scheme.Cohomology
