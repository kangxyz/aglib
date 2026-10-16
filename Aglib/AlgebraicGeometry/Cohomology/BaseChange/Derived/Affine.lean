/-
Copyright (c) 2026 algebraic-geometry contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.Cohomology.BaseChange.Derived.Affine.Counit

/-!
# The original derived flat base-change map on quasicoherent singles over affine bases

The actual resolved geometric map is a quasi-isomorphism by the original
affine counit and original section-complex scalar mate. The original
installed derived-unit equation identifies its localized image with the
existing derived flat base-change map on the coefficient single. The square
is supplied, the direct-image morphism is qcqs, and scalar flatness is the
only base-change hypothesis. No Noetherianity or finite generation is used.
-/

@[expose] public section

noncomputable section

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry HomologicalComplex

namespace AlgebraicGeometry.Scheme.Modules

universe u

/-- All comparisons retain the original installed standard derived models. -/
local instance affineDerivedBaseChangeStandard (Z : Scheme.{u}) :
    HasDerivedCategory.{u + 1} Z.Modules := HasDerivedCategory.standard _

/-- The existing derived flat base-change map on a quasicoherent coefficient single is
invertible for every supplied affine-base Cartesian square and qcqs original morphism. -/
theorem derivedFlatBaseChangeMap_isIso_single_of_spec
    {X Y : Scheme.{u}} {R S : CommRingCat.{u}}
    (a : Y ⟶ X) (b : Y ⟶ Spec S) (f : X ⟶ Spec R) [QuasiCompact f] [QuasiSeparated f]
    (φ : R ⟶ S) (h : IsPullback a b f (Spec.map φ)) (hflat : φ.hom.Flat)
    (M : X.Modules) [M.IsQuasicoherent] :
    letI : Flat (Spec.map φ) := Flat.SpecMap_iff.mpr hflat
    IsIso ((derivedFlatBaseChangeMap a b f (Spec.map φ) h).app
      ((DerivedCategory.Plus.singleFunctor X.Modules 0).obj M)) := by
  let : Flat (Spec.map φ) := Flat.SpecMap_iff.mpr hflat
  let := flat_cartesian_baseChange a b f (Spec.map φ) h
  let I := injectiveResolution M
  let J := injectiveResolution ((pullback a).obj M)
  let γ := flatBaseChangeResolutionMapPlus a b f (Spec.map φ) h M I J
  let : QuasiIso γ.hom :=
    Scheme.Cohomology.flatBaseChangeResolutionMapPlus_quasiIso_of_spec a b f φ h I J hflat
  let : IsIso (DerivedCategory.Plus.Q.map γ) :=
    Localization.inverts DerivedCategory.Plus.Q (CochainComplex.Plus.quasiIso (Spec S).Modules) γ
      (show QuasiIso γ.hom from inferInstance)
  have hm := flatBaseChangeResolutionMapPlus_derived a b f (Spec.map φ) h M I J
  have hi : IsIso ((flatBaseChangeResolutionSourceIso f (Spec.map φ) M I).hom ≫
      (derivedFlatBaseChangeMap a b f (Spec.map φ) h).app
        ((DerivedCategory.Plus.singleFunctor X.Modules 0).obj M)) := by
    rw [← hm]
    change IsIso (DerivedCategory.Plus.Q.map γ ≫ (flatBaseChangeResolutionTargetIso a b M J).hom)
    infer_instance
  let := hi
  exact IsIso.of_isIso_comp_left (flatBaseChangeResolutionSourceIso f (Spec.map φ) M I).hom _

end AlgebraicGeometry.Scheme.Modules
