/-
Copyright (c) 2026 algebraic-geometry contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.Cohomology.BaseChange.Modules.Separated.Cartesian
public import Aglib.AlgebraicGeometry.Cohomology.DirectImage.Affine.Localization.OpenScalarMate

/-!
# Localization of the original open-cohomology restriction

The canonical tensor mate at a localization is transported through the
original top and open cohomology identifications and the native module
restriction/pullback isomorphism. The resulting localizing map is exactly
the unchanged `Sheaf.H'` restriction from the whole space to the open.
-/

@[expose] public section

noncomputable section

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open CategoryTheory CategoryTheory.Limits CategoryTheory.Abelian
open AlgebraicGeometry TopologicalSpace Opposite

namespace AlgebraicGeometry.Scheme.Cohomology

universe u

variable {R S : Type u} [CommRing R] [CommRing S] {X : Scheme.{u}}

/-- In the supplied localization square, the original whole-to-open `H'` restriction is
localizing for every quasicoherent coefficient on a quasi-compact separated source. -/
theorem moduleHPrimeRestriction_isLocalizedModule_of_isPullback_of_isSeparated
    (V : X.Opens) (q : V.toScheme ⟶ Spec (CommRingCat.of S))
    (f : X ⟶ Spec (CommRingCat.of R)) [QuasiCompact f] [IsSeparated f]
    (T : Submonoid R) (σ : R →+* S)
    (h : IsPullback V.ι q f (Spec.map (CommRingCat.ofHom σ)))
    (hloc : letI := σ.toAlgebra; IsLocalization T S)
    (M : X.Modules) [M.IsQuasicoherent] (n : ℕ) :
    let α := f.appTop.hom.comp (Scheme.ΓSpecIso (CommRingCat.of R)).inv.hom
    letI := moduleHPrimeModuleOfHom X α M n ⊤
    letI := moduleHPrimeModuleOfHom X α M n V
    IsLocalizedModule T
      (moduleHPrimeRestrictionOfHom X α M n (homOfLE (show V ≤ ⊤ from le_top))) := by
  let : Algebra R S := σ.toAlgebra
  let : IsLocalization T S := hloc
  exact moduleHPrimeRestriction_isLocalizedModule_of_isPullback_of_tensor_isIso
    V q f T σ h hloc M n
    (moduleCohomologyTensorMap_isIso_of_isPullback
      V.ι q f σ h (IsLocalization.flat S T) M n)

end AlgebraicGeometry.Scheme.Cohomology
