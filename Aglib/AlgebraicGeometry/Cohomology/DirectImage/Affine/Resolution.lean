/-
Copyright (c) 2026 algebraic-geometry contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.Cohomology.DirectImage.Affine.Localization.Principal
public import Aglib.AlgebraicGeometry.Cohomology.DirectImage.Affine.ResolutionLocality

/-!
# Principal localization of the actual direct-image resolution

The supplied actual module injective resolution is pushed forward termwise.
The original affine-base section comparison and original open-resolution
cohomology equivalence identify its actual section-homology restriction
with the unchanged native `H'` restriction. The proved canonical qcqs flat
base-change theorem makes that exact homology map a localization.
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

/-- Principal-open restriction of the native section complex of the actual pushed-forward
resolution localizes homology in every nonnegative degree. -/
theorem moduleResolutionPushforwardSectionsRestriction_isLocalized_nat
    (f : X ⟶ Spec (CommRingCat.of R)) [QuasiCompact f] [QuasiSeparated f]
    (M : X.Modules) [M.IsQuasicoherent] (I : InjectiveResolution M) (r : R) (n : ℕ) :
    let K := ((Scheme.Modules.pushforward f).mapHomologicalComplex (.up ℤ)).obj I.cochainComplex
    IsLocalizedModule.Away r
      (homologyMap (Scheme.Modules.Complex.specSectionsComplexRestriction
        (CommRingCat.of R) (.up ℤ) (PrimeSpectrum.basicOpen r) K) (n : ℤ)).hom :=
  moduleResolutionPushforwardSectionsRestriction_isLocalized_nat_of_principal_localization f M I
    (fun r n => moduleHPrimeRestriction_isLocalizedModule_principal f M r n) r n

/-- The same original principal restriction localizes actual resolution-section homology in
every integer degree; the original resolution is zero in negative degrees. -/
theorem moduleResolutionPushforwardSectionsRestriction_isLocalized
    (f : X ⟶ Spec (CommRingCat.of R)) [QuasiCompact f] [QuasiSeparated f]
    (M : X.Modules) [M.IsQuasicoherent] (I : InjectiveResolution M) (r : R) (i : ℤ) :
    let K := ((Scheme.Modules.pushforward f).mapHomologicalComplex (.up ℤ)).obj I.cochainComplex
    IsLocalizedModule.Away r
      (homologyMap (Scheme.Modules.Complex.specSectionsComplexRestriction
        (CommRingCat.of R) (.up ℤ) (PrimeSpectrum.basicOpen r) K) i).hom :=
  moduleResolutionPushforwardSectionsRestriction_isLocalized_of_principal_localization f M I
    (fun r n => moduleHPrimeRestriction_isLocalizedModule_principal f M r n) r i

/-- The original affine tilde–global-sections counit on the actual pushed-forward module
resolution is a quasi-isomorphism for every quasicoherent coefficient and qcqs morphism. -/
theorem moduleResolutionPushforwardTildeCounit_quasiIso
    (f : X ⟶ Spec (CommRingCat.of R)) [QuasiCompact f] [QuasiSeparated f]
    (M : X.Modules) [M.IsQuasicoherent] (I : InjectiveResolution M) :
    let K := ((Scheme.Modules.pushforward f).mapHomologicalComplex (.up ℤ)).obj I.cochainComplex
    QuasiIso (Scheme.Modules.Complex.tildeGlobalSectionsCounit (CommRingCat.of R) (.up ℤ) K) :=
  moduleResolutionPushforwardTildeCounit_quasiIso_of_principal_localization f M I
    (fun r n => moduleHPrimeRestriction_isLocalizedModule_principal f M r n)


end AlgebraicGeometry.Scheme.Cohomology
