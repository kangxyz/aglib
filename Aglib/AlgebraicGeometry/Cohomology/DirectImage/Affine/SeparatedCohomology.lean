/-
Copyright (c) 2026 algebraic-geometry contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.Cohomology.DirectImage.Affine.Separated
public import Aglib.AlgebraicGeometry.Cohomology.DirectImage.Affine.SectionsCounit
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
  (f : X ⟶ Spec (CommRingCat.of R)) [QuasiCompact f] [IsSeparated f]
  (M : X.Modules) [M.IsQuasicoherent]

/-- Actual affine sections of the original higher direct image are unchanged original
cohomology, with its actual structural ring action and original resolution classes. -/
def moduleHigherDirectImageAffineSectionsLinearEquivOfIsSeparated
    (I : InjectiveResolution M) (n : ℕ) :
    let α := f.appTop.hom.comp (Scheme.ΓSpecIso (CommRingCat.of R)).inv.hom
    letI := moduleCohomologyModuleOfHom X α M n
    moduleSpecΓFunctor.obj (((Scheme.Modules.pushforward f).rightDerived n).obj M) ≃ₗ[R]
      Sheaf.H.{u + 1} (moduleAddSheaf X M) n :=
  moduleHigherDirectImageAffineSectionsLinearEquivOfCounitQuasiIso f M I
    (moduleResolutionPushforwardTildeCounit_quasiIso_of_isSeparated f M I) n


end AlgebraicGeometry.Scheme.Cohomology
