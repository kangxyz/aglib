/-
Copyright (c) 2026 algebraic-geometry contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.Cohomology.DirectImage.Affine.Counit
public import Aglib.CategoryTheory.Abelian.Injective.ExtZero
public import Aglib.AlgebraicGeometry.Cohomology.DirectImage.ResolutionSections.Coefficients
public import Aglib.AlgebraicGeometry.Cohomology.Modules.Ext.DegreeZero
public import Aglib.Algebra.Homology.DerivedCategory.RightDerivedFunctorPlus.SingleHomology
public import Aglib.Algebra.Homology.ShortComplex.Adjunction.Counit
public import Aglib.AlgebraicGeometry.Modules.QuasiCoherent.Affine.TildeExact

/-!
# Actual affine higher-image sections and unchanged cohomology

The actual higher direct image over a spectrum has the original cohomology
module as its sections, with the specified structural action. The comparison
uses the original counit computation, original tilde unit and actual section
complex of the supplied native module injective resolution. The installed
bounded-below derived functor at the original single has the same canonical
comparison through the native higher-derived/homology isomorphism.
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

/-- Actual affine sections of the original higher direct image are unchanged original
cohomology, with its actual structural ring action and original resolution classes. -/
def moduleHigherDirectImageAffineSectionsLinearEquivOfCounitQuasiIso
    (I : InjectiveResolution M)
    (hI : QuasiIso (Scheme.Modules.Complex.tildeGlobalSectionsCounit
      (CommRingCat.of R) (.up ℤ)
      (((Scheme.Modules.pushforward f).mapHomologicalComplex (.up ℤ)).obj I.cochainComplex)))
    (n : ℕ) :
    let α := f.appTop.hom.comp (Scheme.ΓSpecIso (CommRingCat.of R)).inv.hom
    letI := moduleCohomologyModuleOfHom X α M n
    moduleSpecΓFunctor.obj (((Scheme.Modules.pushforward f).rightDerived n).obj M) ≃ₗ[R]
      Sheaf.H.{u + 1} (moduleAddSheaf X M) n := by
  let α := f.appTop.hom.comp (Scheme.ΓSpecIso (CommRingCat.of R)).inv.hom
  letI := moduleCohomologyModuleOfHom X α M n
  let K := ((Scheme.Modules.pushforward f).mapHomologicalComplex (.up ℤ)).obj I.cochainComplex
  let C := (moduleSpecΓFunctor.mapHomologicalComplex (.up ℤ)).obj K
  let e₀ := moduleSpecΓFunctor.mapIso
    (moduleHigherDirectImageAffineIsoOfCounitQuasiIso f M I hI n)
  let e₁ := (tilde.toTildeΓNatIso (R := CommRingCat.of R)).app (C.homology (n : ℤ))
  let e₂ := (homologyFunctor (ModuleCat.{u} R) (.up ℤ) (n : ℤ)).mapIso
    (moduleSpecPushforwardGlobalSectionsComplexIso f (.up ℤ) I.cochainComplex)
  exact e₀.toLinearEquiv.trans (e₁.symm.toLinearEquiv.trans
    (e₂.toLinearEquiv.trans (moduleResolutionSectionsCohomologyLinearEquiv X α I n)))


end AlgebraicGeometry.Scheme.Cohomology
