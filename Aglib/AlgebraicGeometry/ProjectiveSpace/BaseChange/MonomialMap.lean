/-
Copyright (c) 2026 algebraic-geometry contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.ProjectiveSpace.HomogeneousEvaluation
public import Aglib.AlgebraicGeometry.ProjectiveSpace.BaseChange.HomogeneousSections
public import Aglib.AlgebraicGeometry.Modules.Pullback.FreeMap
public import Aglib.AlgebraicGeometry.Modules.Pullback.UnitSections
public import Aglib.RingTheory.MvPolynomial.GradedMapBasis

/-!
# The monomial map under base change of the coefficient ring

For a ring map `σ : A →+* B` and `map σ ι : P^n_B ⟶ P^n_A`, the pullback of the monomial map
`monomialMap ι A r : 𝒪^{monomials} ⟶ 𝒪(r)` (`ProjectiveSpace/HomogeneousEvaluation`) along
`map σ ι`, through `pullbackFreeMap` and the base-change isomorphism
`twistingPullbackIso σ ι r : (map σ ι)^* 𝒪(r) ≅ 𝒪(r)`, is the monomial map over `B`
(`pullbackFreeMap_monomialMap`). On each basis section this is the base change of the section of a
homogeneous polynomial (`twistingPullbackIso_hom_unit_homogeneousSection`) for the monomial basis,
which `σ` preserves (`MvPolynomial.gradedMap_homogeneousPieceBasis`). No hypothesis on `σ` is
needed. Consumer: the evaluation map of a Hilbert family over an affine open
(`HilbertScheme/DirectImageSheafEpi`).
-/

@[expose] public section

noncomputable section

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open CategoryTheory CategoryTheory.Limits Opposite
open AlgebraicGeometry.Scheme.Modules

universe u

namespace AlgebraicGeometry.ProjectiveSpace

variable (ι : Type u) {A B : Type u} [CommRing A] [CommRing B]

/-- **The monomials under base change**: the pullback of `monomialMap` along `map σ ι`, through
`twistingPullbackIso`, is `monomialMap` over the new ring. -/
theorem pullbackFreeMap_monomialMap (σ : A →+* B) (r : ℕ) :
    pullbackFreeMap (map σ ι) (monomialMap ι A r) ≫ (twistingPullbackIso σ ι r).hom =
      monomialMap ι B r := by
  refine Cofan.IsColimit.hom_ext (SheafOfModules.isColimitFreeCofan _) _ _ fun a => ?_
  change SheafOfModules.ιFree a ≫ _ = SheafOfModules.ιFree a ≫ _
  rw [ιFree_monomialMap, pullbackFreeMap_def, Category.assoc, ιFree_comp_pullbackFreeIso_inv_assoc,
    ← CategoryTheory.Functor.map_comp_assoc, ιFree_monomialMap]
  apply (unitHomGlobalSectionsEquiv _ _).injective
  rw [Equiv.apply_symm_apply, unitHomGlobalSectionsEquiv_apply]
  change (twistingPullbackIso σ ι r).hom.val.app (op ⊤)
      ((unitHomGlobalSectionsEquiv _ _) ((pullbackUnitIso (map σ ι)).inv ≫
        (Scheme.Modules.pullback (map σ ι)).map
          ((unitHomGlobalSectionsEquiv _ _).symm (monomialSection ι A r a)))) = _
  rw [unitHomGlobalSectionsEquiv_pullbackUnitIso_inv_comp, monomialSection,
    twistingPullbackIso_hom_unit_homogeneousSection, MvPolynomial.gradedMap_homogeneousPieceBasis]
  rfl

end AlgebraicGeometry.ProjectiveSpace
