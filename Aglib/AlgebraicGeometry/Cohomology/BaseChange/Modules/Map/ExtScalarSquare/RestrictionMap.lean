/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.Cohomology.BaseChange.Modules.Map.ExtScalarSquare.Core
public import Aglib.CategoryTheory.Abelian.Ext.DiagramMap.Scalars.NormalizedRestrictionMap.Values
public import Aglib.AlgebraicGeometry.Cohomology.BaseChange.Modules.Map.Open.Values
public import Aglib.AlgebraicGeometry.Cohomology.Modules.Scalars.Open.Values
public import Aglib.AlgebraicGeometry.Cohomology.MayerVietoris.Scalars.Values

/-! # The original normalized coefficient-restriction map

This is the geometric specialization of the same map used as the normalized
scalar square's right field. Expanded formulas remain compatibility laws.
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true
universe u
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry TopologicalSpace Opposite
namespace AlgebraicGeometry.Scheme.Cohomology

/-- The original restriction/index/top map, from its unique scalar Ext constructor. -/
def moduleHPrimeRestrictionPostcompMap
    (X : Scheme.{u}) {R : Type u} [CommRing R] (α : R →+* Γ(X, ⊤))
    (U : X.Opens) (M : X.Modules) {N : U.toScheme.Modules}
    (ε : M.restrict U.ι ⟶ N) (n : ℕ) :
    letI := moduleCohomologyModuleOfHom U.toScheme (U.ι.appTop.hom.comp α) N n
    (moduleHPrimePresheaf X α M n).obj (op U) ⟶
      (ModuleCat.restrictScalars (RingHom.id R)).obj
        (ModuleCat.of R (Sheaf.H.{u + 1} (moduleAddSheaf U.toScheme N) n)) := by
  let a := U.ι
  let αU := a.appTop.hom.comp α
  let φ := (Scheme.Modules.restrictAdjunction a).unit.app M ≫
    (Scheme.Modules.pushforward a).map ε
  exact (zariskiPullback a).extScalarNormalizedRestrictionMap.{u + 1, u, u + 1, u,
      u, u, u, u, u, u + 1}
    (TopCat.Sheaf.openFreeAbelianFunctor X.toTopCat)
    (TopCat.Sheaf.openFreeAbelianFunctor U.toScheme.toTopCat)
    (Opens.map a.base) (TopCat.Sheaf.openFreeAbelianPullbackIso a.base)
    (moduleAddSheaf X M) (moduleAddSheaf U.toScheme N)
    (moduleCoefficientScalarAction X α M) (moduleCoefficientScalarAction U.toScheme αU N)
    (moduleCoefficientPullback a φ)
    (moduleCoefficientScalarAction_compatible a (RingHom.id R) α αU (by rfl) φ)
    n (op U) (eqToHom U.ι_preimage_self.symm).op
    (additiveOpenTopIsoInteger U.toScheme)

/-- The expanded original restriction formula is unchanged. -/
theorem moduleHPrimeRestrictionPostcompMap_eq
    (X : Scheme.{u}) {R : Type u} [CommRing R] (α : R →+* Γ(X, ⊤))
    (U : X.Opens) (M : X.Modules) {N : U.toScheme.Modules}
    (ε : M.restrict U.ι ⟶ N) (n : ℕ) :
    let αU := U.ι.appTop.hom.comp α
    let η := (Scheme.Modules.restrictAdjunction U.ι).unit.app M
    let C := moduleHPrimePresheaf U.toScheme αU N n
    let κ := (eqToHom U.ι_preimage_self.symm).op
    letI := moduleHPrimeModuleOfHom X α M n U
    letI := moduleHPrimeModuleOfHom U.toScheme αU N n ⊤
    letI := moduleCohomologyModuleOfHom U.toScheme αU (M.restrict U.ι) n
    letI := moduleCohomologyModuleOfHom U.toScheme αU N n
    moduleHPrimeRestrictionPostcompMap X α U M ε n =
      (moduleHPrimeRestrictionMap U.ι (RingHom.id R) α αU (by rfl)
      (η ≫ (Scheme.Modules.pushforward U.ι).map ε) n).app (op U) ≫
        (ModuleCat.restrictScalars (RingHom.id R)).map (C.map κ) ≫
        (ModuleCat.restrictScalars (RingHom.id R)).map
          (moduleHPrimeTopLinearEquivOfHom U.toScheme αU N n).toModuleIso.hom := by
  let a := U.ι
  let αU := a.appTop.hom.comp α
  let φ := (Scheme.Modules.restrictAdjunction a).unit.app M ≫
    (Scheme.Modules.pushforward a).map ε
  let κ := (eqToHom U.ι_preimage_self.symm).op
  let := moduleHPrimeModuleOfHom X α M n U
  let := moduleHPrimeModuleOfHom U.toScheme αU N n ⊤
  let := moduleCohomologyModuleOfHom U.toScheme αU N n
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro x
  change moduleHPrimeRestrictionPostcompMap X α U M ε n x =
    moduleHPrimeTopLinearEquivOfHom U.toScheme αU N n
      ((moduleHPrimePresheaf U.toScheme αU N n).map κ
        ((moduleHPrimeRestrictionMap a (RingHom.id R) α αU (by rfl) φ n).app (op U) x))
  rw [moduleHPrimeTopLinearEquivOfHom_apply_ext, moduleHPrimePresheaf_map_apply_ext,
    moduleHPrimeRestrictionMap_apply_ext]
  exact (zariskiPullback a).extScalarNormalizedRestrictionMap_apply.{u + 1, u, u + 1, u,
    u, u, u, u, u, u + 1}
    (TopCat.Sheaf.openFreeAbelianFunctor X.toTopCat)
    (TopCat.Sheaf.openFreeAbelianFunctor U.toScheme.toTopCat)
    (Opens.map a.base) (TopCat.Sheaf.openFreeAbelianPullbackIso a.base)
    (moduleAddSheaf X M) (moduleAddSheaf U.toScheme N)
    (moduleCoefficientScalarAction X α M) (moduleCoefficientScalarAction U.toScheme αU N)
    (moduleCoefficientPullback a φ)
    (moduleCoefficientScalarAction_compatible a (RingHom.id R) α αU (by rfl) φ)
    n (op U) κ (additiveOpenTopIsoInteger U.toScheme) x

/-- The square's original right field is the shared map itself. -/
theorem moduleOpenPullbackExtTensorSquare_right_map
    {X Y : Scheme.{u}} {R S : Type u} [CommRing R] [CommRing S]
    (p : Y ⟶ X) (σ : R →+* S)
    (α : R →+* Γ(X, ⊤)) (β : S →+* Γ(Y, ⊤))
    (hσ : p.appTop.hom.comp α = β.comp σ)
    (M : X.Modules) (U : X.Opens) (n : ℕ) :
    let V := p ⁻¹ᵁ U
    let a := V.ι
    let b := p ∣_ U
    let j := U.ι
    let h : IsPullback a b p j := (isPullback_morphismRestrict p U).flip
    let N := (Scheme.Modules.pullback p).obj M
    let ε := inv ((Scheme.Modules.cartesianPullbackBaseChangeMate a b p j h).app M)
    (moduleOpenPullbackExtTensorSquare p σ α β hσ M U n).f₂₄ =
      moduleHPrimeRestrictionPostcompMap Y β V N ε n := rfl

end AlgebraicGeometry.Scheme.Cohomology
