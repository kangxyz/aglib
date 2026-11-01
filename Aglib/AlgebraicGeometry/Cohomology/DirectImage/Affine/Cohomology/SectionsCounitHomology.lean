/-
Copyright (c) 2026 algebraic-geometry contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.Cohomology.DirectImage.Affine.SectionsCounit
public import Aglib.Algebra.Homology.ShortComplex.Adjunction.Counit

/-! # Original affine sections/homology factors from the actual counit -/

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
  (f : X ⟶ Spec (CommRingCat.of R)) (M : X.Modules)

/-- The unchanged first two affine cohomology factors, from actual higher-image sections
to homology of the original section complex of the supplied resolution. -/
def moduleHigherDirectImageAffineSectionsHomologyMap_of_counit_quasiIso (I : InjectiveResolution M)
    (hI : QuasiIso (Scheme.Modules.Complex.tildeGlobalSectionsCounit
      (CommRingCat.of R) (.up ℤ)
      (((Scheme.Modules.pushforward f).mapHomologicalComplex (.up ℤ)).obj I.cochainComplex)))
    (n : ℕ) :
    moduleSpecΓFunctor.obj (((Scheme.Modules.pushforward f).rightDerived n).obj M) ⟶
      ((moduleSpecΓFunctor.mapHomologicalComplex (.up ℤ)).obj
        (((Scheme.Modules.pushforward f).mapHomologicalComplex (.up ℤ)).obj
          I.cochainComplex)).homology (n : ℤ) :=
  moduleSpecΓFunctor.map (moduleHigherDirectImageAffineIso_of_counit_quasiIso f M I hI n).hom ≫
    (tilde.toTildeΓNatIso (R := CommRingCat.of R)).inv.app
      (((moduleSpecΓFunctor.mapHomologicalComplex (.up ℤ)).obj
        (((Scheme.Modules.pushforward f).mapHomologicalComplex (.up ℤ)).obj
          I.cochainComplex)).homology (n : ℤ))

/-- The original affine section/homology factor is invertible. -/
theorem moduleHigherDirectImageAffineSectionsHomologyMap_isIso_of_counit_quasiIso
    (I : InjectiveResolution M)
    (hI : QuasiIso (Scheme.Modules.Complex.tildeGlobalSectionsCounit
      (CommRingCat.of R) (.up ℤ)
      (((Scheme.Modules.pushforward f).mapHomologicalComplex (.up ℤ)).obj I.cochainComplex)))
    (n : ℕ) :
    IsIso (moduleHigherDirectImageAffineSectionsHomologyMap_of_counit_quasiIso f M I hI n) := by
  dsimp only [moduleHigherDirectImageAffineSectionsHomologyMap_of_counit_quasiIso]
  infer_instance

/-- The unchanged affine factor retains the native homology counit mate and the original
integer-resolution comparison. Global sections need not preserve homology. -/
theorem moduleHigherDirectImageAffineSectionsHomologyMap_counit_of_counit_quasiIso
    (I : InjectiveResolution M)
    (hI : QuasiIso (Scheme.Modules.Complex.tildeGlobalSectionsCounit
      (CommRingCat.of R) (.up ℤ)
      (((Scheme.Modules.pushforward f).mapHomologicalComplex (.up ℤ)).obj I.cochainComplex)))
    (n : ℕ) :
    let K := ((Scheme.Modules.pushforward f).mapHomologicalComplex (.up ℤ)).obj I.cochainComplex
    let : (tilde.functor (CommRingCat.of R)).Additive := by
      let : PreservesFiniteLimits (tilde.functor (CommRingCat.of R)) :=
        Scheme.Modules.tilde_preservesFiniteLimits (CommRingCat.of R)
      exact CategoryTheory.Functor.additive_of_preserves_binary_products _
    let : (tilde.functor (CommRingCat.of R)).PreservesHomology :=
      Scheme.Modules.tilde_preservesHomology (CommRingCat.of R)
    let : (moduleSpecΓFunctor (R := CommRingCat.of R)).Additive :=
      Scheme.Modules.moduleSpecΓFunctor_additive (CommRingCat.of R)
    moduleHigherDirectImageAffineSectionsHomologyMap_of_counit_quasiIso f M I hI n ≫
        (tilde.adjunction (R := CommRingCat.of R)).homologyCounitMate (K.sc (n : ℤ)) =
      moduleSpecΓFunctor.map
        (I.isoRightDerivedObjCochain (Scheme.Modules.pushforward f) n).hom := by
  let : PreservesFiniteLimits (tilde.functor (CommRingCat.of R)) :=
    Scheme.Modules.tilde_preservesFiniteLimits (CommRingCat.of R)
  let : (tilde.functor (CommRingCat.of R)).Additive :=
    CategoryTheory.Functor.additive_of_preserves_binary_products _
  let : (tilde.functor (CommRingCat.of R)).PreservesHomology :=
    Scheme.Modules.tilde_preservesHomology (CommRingCat.of R)
  let : (moduleSpecΓFunctor (R := CommRingCat.of R)).Additive :=
    Scheme.Modules.moduleSpecΓFunctor_additive (CommRingCat.of R)
  let K := ((Scheme.Modules.pushforward f).mapHomologicalComplex (.up ℤ)).obj I.cochainComplex
  let C := (moduleSpecΓFunctor.mapHomologicalComplex (.up ℤ)).obj K
  let : QuasiIso (Scheme.Modules.Complex.tildeGlobalSectionsCounit
      (CommRingCat.of R) (.up ℤ) K) := hI
  change moduleSpecΓFunctor.map (moduleHigherDirectImageAffineIso_of_counit_quasiIso
    f M I hI n).hom ≫
      (tilde.toTildeΓNatIso (R := CommRingCat.of R)).inv.app (C.homology (n : ℤ)) ≫
      (tilde.toTildeΓNatIso (R := CommRingCat.of R)).hom.app (C.homology (n : ℤ)) ≫
      moduleSpecΓFunctor.map
        (Scheme.Modules.Complex.tildeGlobalSectionsHomologyIso
          (CommRingCat.of R) (.up ℤ) K (n : ℤ)).hom = _
  simp only [Iso.inv_hom_id_app_assoc]
  rw [← Functor.map_comp]
  exact congrArg moduleSpecΓFunctor.map
    (moduleHigherDirectImageAffineIso_of_counit_quasiIso_hom_comp f M I hI n)

end AlgebraicGeometry.Scheme.Cohomology
