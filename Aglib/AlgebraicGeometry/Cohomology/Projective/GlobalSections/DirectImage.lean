/-
Copyright (c) 2026 algebraic-geometry contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.Cohomology.Projective.GlobalSections.PolynomialSections
public import Aglib.AlgebraicGeometry.Cohomology.BaseChange.NoetherianPushforward
public import Aglib.AlgebraicGeometry.Modules.QuasiCoherent.Affine.Exactness
public import Aglib.AlgebraicGeometry.Modules.BaseChange.FreeMap
public import Aglib.AlgebraicGeometry.ProjectiveSpace.HomogeneousEvaluation

/-!
# The direct image of projective space to its base and its global sections

For a ring `B`, finitely many coordinates `ι` and `toSpec B ι : P^n_B ⟶ Spec B`:

* `isQuasicoherent_pushforward_toSpec`: the direct image `(toSpec)_* M` of a quasi-coherent
  module is quasi-coherent (the degree-zero affine higher direct image,
  `moduleHigherDirectImageAffine_isQuasicoherent`);
* `pushforwardToSpecSectionsLinearEquiv`: the global sections of `(toSpec)_* M` are
  `H^0(P^n_B, M)`, linearly over `B` (`moduleHigherDirectImageAffineSectionsLinearEquiv` in degree
  zero), and `equiv₀_pushforwardToSpecSectionsLinearEquiv` identifies the composite with the
  ordinary section comparison `Sheaf.H.equiv₀`. The `B`-module structure on `H^0` is
  `moduleCohomologyModuleOfHom` through the structure morphism (named `h0Module` in
  `HilbertScheme/GrassmannianPoint`);
* `epi_pushforwardFreeMap_monomialMap`: **the monomials generate `𝒪(r)` over `Spec B`**. For
  `ι ≃ Fin (n + 1)` and every natural `r`, the adjoint `𝒪^{monomials} ⟶ (toSpec)_* 𝒪(r)` of the
  monomial map (`pushforwardFreeMap`, `monomialMap`) is an epimorphism: the monomial sections form
  a basis of `H^0(P^n_B, 𝒪(r)) = B[x]_r` (`twistingH0PolynomialLinearEquiv`), and an epimorphism
  on global sections of quasi-coherent sheaves on `Spec B` is an epimorphism
  (`epi_of_epi_globalSections`).

No hypothesis on `B` is needed. Consumers: the evaluation map onto the direct image of a Hilbert
family (`HilbertScheme/DirectImageSheafEpi`) and its global form
(`HilbertScheme/UniversalSubschemePullback`), for the map `π_{T*} E_T(r) → π_{T*} F(r)` of Nitsure,
*Construction of Hilbert and Quot schemes*, arXiv:math/0504590v1, §5, p. 26.
-/

@[expose] public section

noncomputable section

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open CategoryTheory CategoryTheory.Limits Opposite
open AlgebraicGeometry.Scheme.Modules AlgebraicGeometry.Scheme.Modules.QuasiCoherent

universe u

namespace AlgebraicGeometry.ProjectiveSpace

open Scheme.Cohomology

variable (ι : Type u) (n : ℕ) (e : ι ≃ Fin (n + 1)) {B : Type u} [CommRing B]

/-- The direct image along `toSpec` of a quasi-coherent module is quasi-coherent. -/
theorem isQuasicoherent_pushforward_toSpec [Finite ι] (M : (ProjectiveSpace B ι).Modules)
    [M.IsQuasicoherent] : ((Scheme.Modules.pushforward (toSpec B ι)).obj M).IsQuasicoherent :=
  (SheafOfModules.isQuasicoherent _).prop_of_iso
    ((Scheme.Modules.pushforward (toSpec B ι)).rightDerivedZeroIsoSelf.app M)
    (moduleHigherDirectImageAffine_isQuasicoherent (toSpec B ι) M 0)

/-- The global sections of `(toSpec)_* M` as `H^0(P^n_B, M)`, linearly over `B`. -/
def pushforwardToSpecSectionsLinearEquiv [Finite ι] (M : (ProjectiveSpace B ι).Modules)
    [M.IsQuasicoherent] :
    letI := moduleCohomologyModuleOfHom (ProjectiveSpace B ι)
      ((toSpec B ι).appTop.hom.comp (Scheme.ΓSpecIso (CommRingCat.of B)).inv.hom) M 0
    moduleSpecΓFunctor.obj ((Scheme.Modules.pushforward (toSpec B ι)).obj M) ≃ₗ[B]
      Sheaf.H.{u + 1} (moduleAddSheaf (ProjectiveSpace B ι) M) 0 :=
  (((moduleSpecΓFunctor (R := CommRingCat.of B)).mapIso
      ((Scheme.Modules.pushforward (toSpec B ι)).rightDerivedZeroIsoSelf.app M).symm
    ).toLinearEquiv).trans
    (moduleHigherDirectImageAffineSectionsLinearEquiv (toSpec B ι) M (injectiveResolution M) 0)

theorem equiv₀_pushforwardToSpecSectionsLinearEquiv [Finite ι]
    (M : (ProjectiveSpace B ι).Modules) [M.IsQuasicoherent]
    (y : moduleSpecΓFunctor.obj ((Scheme.Modules.pushforward (toSpec B ι)).obj M)) :
    Sheaf.H.equiv₀ (moduleAddSheaf (ProjectiveSpace B ι) M) Limits.isTerminalTop
        (pushforwardToSpecSectionsLinearEquiv ι M y) = y := by
  rw [pushforwardToSpecSectionsLinearEquiv, LinearEquiv.trans_apply,
    moduleHigherDirectImageAffineSectionsLinearEquiv_zero_apply]
  change ((((Scheme.Modules.pushforward (toSpec B ι)).rightDerivedZeroIsoSelf.app M).inv ≫
    ((Scheme.Modules.pushforward (toSpec B ι)).rightDerivedZeroIsoSelf.app M).hom).val.app
      (op ⊤)) y = y
  rw [Iso.inv_hom_id]
  rfl

include e in
/-- **The monomials generate `𝒪(r)` over `Spec B`**: the adjoint
`𝒪^{monomials} ⟶ (toSpec)_* 𝒪(r)` of `monomialMap` is an epimorphism, since the monomial
sections form a basis of `H^0(P^n_B, 𝒪(r)) = B[x]_r`. -/
theorem epi_pushforwardFreeMap_monomialMap (r : ℕ) :
    Epi (pushforwardFreeMap (toSpec B ι) (monomialMap ι B r)) := by
  have : Fintype ι := Fintype.ofEquiv _ e.symm
  have : (twistingSheaf B ι (r : ℤ)).IsQuasicoherent := inferInstance
  have := isQuasicoherent_pushforward_toSpec ι (twistingSheaf B ι (r : ℤ))
  suffices hΓ : Function.Surjective (moduleSpecΓFunctor.map
      (pushforwardFreeMap (toSpec B ι) (monomialMap ι B r))).hom by
    have : Epi (moduleSpecΓFunctor.map
        (pushforwardFreeMap (toSpec B ι) (monomialMap ι B r))) :=
      (ModuleCat.epi_iff_surjective _).mpr hΓ
    exact epi_of_epi_globalSections (CommRingCat.of B) _
  let := moduleCohomologyModuleOfHom (ProjectiveSpace B ι)
    ((toSpec B ι).appTop.hom.comp (Scheme.ΓSpecIso (CommRingCat.of B)).inv.hom)
    (twistingSheaf B ι (r : ℤ)) 0
  let L₀ := pushforwardToSpecSectionsLinearEquiv ι (twistingSheaf B ι (r : ℤ))
  let T₀ := twistingH0PolynomialLinearEquiv B ι (e.symm 0) r
  have hΨ (a : Monomials ι r) :
      L₀ ((moduleSpecΓFunctor.map (pushforwardFreeMap (toSpec B ι) (monomialMap ι B r))).hom
        (unitHomGlobalSectionsEquiv _ _ (SheafOfModules.ιFree a))) =
        T₀.symm (MvPolynomial.homogeneousPieceBasis (ι := ι) B r a) := by
    apply (Sheaf.H.equiv₀ (moduleAddSheaf _ (twistingSheaf B ι (r : ℤ)))
      Limits.isTerminalTop).injective
    rw [equiv₀_pushforwardToSpecSectionsLinearEquiv, equiv₀_twistingH0PolynomialLinearEquiv_symm]
    have h1 := unitHomGlobalSectionsEquiv_ιFree_pushforwardFreeMap (toSpec B ι)
      (monomialMap ι B r) a
    rw [ιFree_monomialMap, Equiv.apply_symm_apply, monomialSection,
      unitHomGlobalSectionsEquiv_apply] at h1
    rw [unitHomGlobalSectionsEquiv_apply]
    exact h1
  have hsurj : Function.Surjective ((L₀.trans T₀).toLinearMap.comp
      (moduleSpecΓFunctor.map (pushforwardFreeMap (toSpec B ι) (monomialMap ι B r))).hom) := by
    rw [← LinearMap.range_eq_top, eq_top_iff,
      ← (MvPolynomial.homogeneousPieceBasis (ι := ι) B r).span_eq, Submodule.span_le]
    rintro _ ⟨a, rfl⟩
    refine LinearMap.mem_range.mpr
      ⟨unitHomGlobalSectionsEquiv _ _ (SheafOfModules.ιFree a), ?_⟩
    rw [LinearMap.comp_apply, LinearEquiv.coe_coe, LinearEquiv.trans_apply, hΨ,
      LinearEquiv.apply_symm_apply]
  intro y
  obtain ⟨z, hz⟩ := hsurj ((L₀.trans T₀) y)
  refine ⟨z, (L₀.trans T₀).injective ?_⟩
  rw [← hz, LinearMap.comp_apply, LinearEquiv.coe_coe]

end AlgebraicGeometry.ProjectiveSpace
