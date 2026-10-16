/-
Copyright (c) 2026 algebraic-geometry contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.Cohomology.DirectImage.Affine.Localization
public import Aglib.AlgebraicGeometry.Cohomology.Restriction.Top
public import Aglib.AlgebraicGeometry.Modules.BaseChange.OpenImmersion.Pullback

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

private theorem moduleCohomologyMapAlong_postcomp_apply {X Y : Scheme.{u}} (p : Y ⟶ X)
    {M : X.Modules} {N P : Y.Modules}
    (φ : M ⟶ (Scheme.Modules.pushforward p).obj N) (ε : N ⟶ P) (n : ℕ)
    (x : Sheaf.H.{u + 1} (moduleAddSheaf X M) n) :
    Sheaf.H.map ((SheafOfModules.toSheaf Y.ringCatSheaf).map ε) n
        (moduleCohomologyMapAlong p φ n x) =
      moduleCohomologyMapAlong p (φ ≫ (Scheme.Modules.pushforward p).map ε) n x := by
  let z := (Ext.mk₀ ((constantPullbackIso p).inv.app
    (AddCommGrpCat.of (ULift.{u} ℤ)))).comp
      (x.mapExactFunctor (zariskiPullback p)) (Nat.zero_add n)
  change (z.comp (Ext.mk₀ (moduleCoefficientPullback p φ)) (Nat.add_zero n)).comp
      (Ext.mk₀ ((SheafOfModules.toSheaf Y.ringCatSheaf).map ε)) (Nat.add_zero n) =
    z.comp (Ext.mk₀ (moduleCoefficientPullback p
      (φ ≫ (Scheme.Modules.pushforward p).map ε))) (Nat.add_zero n)
  rw [moduleCoefficientPullback_postcomp, Ext.comp_assoc_of_third_deg_zero, Ext.mk₀_comp_mk₀]

variable {R S : Type u} [CommRing R] [CommRing S] {X : Scheme.{u}}

private def moduleCohomologyScalarRestrictionIso (Y : Scheme.{u})
    (α : R →+* Γ(Y, ⊤)) (β : S →+* Γ(Y, ⊤)) (σ : R →+* S)
    (h : α = β.comp σ) (P : Y.Modules) (n : ℕ) :
    letI := moduleCohomologyModuleOfHom Y β P n
    letI := moduleCohomologyModuleOfHom Y α P n
    (ModuleCat.restrictScalars σ).obj
        (ModuleCat.of S (Sheaf.H.{u + 1} (moduleAddSheaf Y P) n)) ≅
      ModuleCat.of R (Sheaf.H.{u + 1} (moduleAddSheaf Y P) n) := by
  letI := moduleCohomologyModuleOfHom Y β P n
  letI := moduleCohomologyModuleOfHom Y α P n
  let G := moduleCohomologyGlobalScalars Y P n
  have hG : G.comp α = (G.comp β).comp σ := by rw [h, RingHom.comp_assoc]
  exact (ModuleCat.restrictScalarsComp'App σ (G.comp β) (G.comp α) hG
    (ModuleCat.of (AddMonoid.End (Sheaf.H.{u + 1} (moduleAddSheaf Y P) n))
      (Sheaf.H.{u + 1} (moduleAddSheaf Y P) n))).symm

private def moduleHPrimeLocalizationTargetIso (V : X.Opens)
    (α : R →+* Γ(X, ⊤)) (β : S →+* Γ(V.toScheme, ⊤)) (σ : R →+* S)
    (h : V.ι.appTop.hom.comp α = β.comp σ) (M : X.Modules) (n : ℕ) :
    let N : V.toScheme.Modules := (Scheme.Modules.pullback V.ι).obj M
    letI := moduleCohomologyModuleOfHom V.toScheme β N n
    letI := moduleHPrimeModuleOfHom X α M n V
    (ModuleCat.restrictScalars σ).obj
        (ModuleCat.of S (Sheaf.H.{u + 1} (moduleAddSheaf V.toScheme N) n)) ≅
      ModuleCat.of R (Sheaf.H'.{u + 1} (moduleAddSheaf X M) n V) := by
  letI := moduleCohomologyModuleOfHom V.toScheme β
    ((Scheme.Modules.pullback V.ι).obj M) n
  letI := moduleCohomologyModuleOfHom V.toScheme β (M.restrict V.ι) n
  letI := moduleCohomologyModuleOfHom V.toScheme (V.ι.appTop.hom.comp α) (M.restrict V.ι) n
  letI := moduleHPrimeModuleOfHom X α M n V
  let e := ((Scheme.Modules.restrictFunctorIsoPullback V.ι).app M).symm
  exact (ModuleCat.restrictScalars σ).mapIso (moduleCohomologyIsoOfHom V.toScheme β e n) ≪≫
    moduleCohomologyScalarRestrictionIso V.toScheme (V.ι.appTop.hom.comp α) β σ h
      (M.restrict V.ι) n ≪≫ (moduleHPrimeOpenLinearEquiv X α M V n).toModuleIso.symm

private theorem moduleHPrimeLocalizationTargetIso_hom_apply (V : X.Opens)
    (α : R →+* Γ(X, ⊤)) (β : S →+* Γ(V.toScheme, ⊤)) (σ : R →+* S)
    (h : V.ι.appTop.hom.comp α = β.comp σ) (M : X.Modules) (n : ℕ)
    (x : Sheaf.H.{u + 1}
      (moduleAddSheaf V.toScheme ((Scheme.Modules.pullback V.ι).obj M)) n) :
    letI := moduleHPrimeModuleOfHom X α M n V
    letI := moduleCohomologyModuleOfHom V.toScheme (V.ι.appTop.hom.comp α) (M.restrict V.ι) n
    (moduleHPrimeLocalizationTargetIso V α β σ h M n).hom x =
      (moduleHPrimeOpenLinearEquiv X α M V n).symm
        (Sheaf.H.map ((SheafOfModules.toSheaf V.toScheme.ringCatSheaf).map
          ((Scheme.Modules.restrictFunctorIsoPullback V.ι).inv.app M)) n x) := rfl

private theorem moduleHPrimeRestriction_eq_localizationComposite (V : X.Opens)
    (α : R →+* Γ(X, ⊤)) (β : S →+* Γ(V.toScheme, ⊤)) (σ : R →+* S)
    (h : V.ι.appTop.hom.comp α = β.comp σ) (M : X.Modules) (n : ℕ) :
    let N : V.toScheme.Modules := (Scheme.Modules.pullback V.ι).obj M
    let φ : M ⟶ (Scheme.Modules.pushforward V.ι).obj N :=
      (Scheme.Modules.pullbackPushforwardAdjunction V.ι).unit.app M
    letI := moduleHPrimeModuleOfHom X α M n ⊤
    letI := moduleHPrimeModuleOfHom X α M n V
    letI := moduleCohomologyModuleOfHom X α M n
    letI := moduleCohomologyModuleOfHom V.toScheme β N n
    moduleHPrimeRestrictionOfHom X α M n (homOfLE (show V ≤ ⊤ from le_top)) =
      ((moduleHPrimeTopLinearEquivOfHom X α M n).toModuleIso.hom ≫
        moduleCohomologyRestrictionMap V.ι σ α β h φ n ≫
        (moduleHPrimeLocalizationTargetIso V α β σ h M n).hom).hom := by
  let := moduleHPrimeModuleOfHom X α M n ⊤
  let := moduleHPrimeModuleOfHom X α M n V
  let := moduleCohomologyModuleOfHom X α M n
  let := moduleCohomologyModuleOfHom V.toScheme β ((Scheme.Modules.pullback V.ι).obj M) n
  let := moduleCohomologyModuleOfHom V.toScheme (V.ι.appTop.hom.comp α) (M.restrict V.ι) n
  ext x
  apply (moduleHPrimeOpenLinearEquiv X α M V n).injective
  change moduleHPrimeOpenLinearEquiv X α M V n
      (moduleHPrimeRestrictionOfHom X α M n (homOfLE le_top) x) =
    moduleHPrimeOpenLinearEquiv X α M V n
      ((moduleHPrimeLocalizationTargetIso V α β σ h M n).hom
        (moduleCohomologyMapAlong V.ι
          ((Scheme.Modules.pullbackPushforwardAdjunction V.ι).unit.app M) n
          (moduleHPrimeTopLinearEquivOfHom X α M n x)))
  rw [moduleHPrimeLocalizationTargetIso_hom_apply, LinearEquiv.apply_symm_apply,
    moduleHPrimeOpenLinearEquiv_restriction_top_geometric,
    moduleCohomologyMapAlong_postcomp_apply]
  apply congrArg (fun φ => moduleCohomologyMapAlong V.ι φ n
    (moduleHPrimeTopLinearEquivOfHom X α M n x))
  exact (Scheme.Modules.restrictFunctorIsoPullback_inv_adjunction_unit V.ι M).symm

/-- In the supplied localization square, the original whole-to-open `H'` restriction is
localizing for every quasicoherent coefficient on a qcqs source. -/
theorem moduleHPrimeRestriction_isLocalizedModule_of_isPullback
    (V : X.Opens) (q : V.toScheme ⟶ Spec (CommRingCat.of S))
    (f : X ⟶ Spec (CommRingCat.of R)) [QuasiCompact f] [QuasiSeparated f]
    (T : Submonoid R) (σ : R →+* S)
    (h : IsPullback V.ι q f (Spec.map (CommRingCat.ofHom σ)))
    (hloc : letI := σ.toAlgebra; IsLocalization T S)
    (M : X.Modules) [M.IsQuasicoherent] (n : ℕ) :
    let α := f.appTop.hom.comp (Scheme.ΓSpecIso (CommRingCat.of R)).inv.hom
    letI := moduleHPrimeModuleOfHom X α M n ⊤
    letI := moduleHPrimeModuleOfHom X α M n V
    IsLocalizedModule T
      (moduleHPrimeRestrictionOfHom X α M n (homOfLE (show V ≤ ⊤ from le_top))) := by
  let α := f.appTop.hom.comp (Scheme.ΓSpecIso (CommRingCat.of R)).inv.hom
  let β := q.appTop.hom.comp (Scheme.ΓSpecIso (CommRingCat.of S)).inv.hom
  let hs := moduleSectionsBaseChangeScalars V.ι q f σ h.w
  let N : V.toScheme.Modules := (Scheme.Modules.pullback V.ι).obj M
  let φ : M ⟶ (Scheme.Modules.pushforward V.ι).obj N :=
    (Scheme.Modules.pullbackPushforwardAdjunction V.ι).unit.app M
  let := moduleHPrimeModuleOfHom X α M n ⊤
  let := moduleHPrimeModuleOfHom X α M n V
  let := moduleCohomologyModuleOfHom X α M n
  let := moduleCohomologyModuleOfHom V.toScheme β N n
  let a := (moduleHPrimeTopLinearEquivOfHom X α M n).toModuleIso
  let b := moduleHPrimeLocalizationTargetIso V α β σ hs M n
  let ψ := moduleCohomologyRestrictionMap V.ι σ α β hs φ n
  let : IsLocalizedModule T ψ.hom :=
    moduleCohomologyRestrictionMap_isLocalizedModule_of_isPullback V.ι q f T σ h hloc M n
  let : IsLocalizedModule T (ψ.hom.comp a.hom.hom) :=
    IsLocalizedModule.of_linearEquiv_right T ψ.hom a.toLinearEquiv
  have htot : IsLocalizedModule T (a.hom ≫ ψ ≫ b.hom).hom :=
    IsLocalizedModule.of_linearEquiv T (ψ.hom.comp a.hom.hom) b.toLinearEquiv
  change IsLocalizedModule T (moduleHPrimeRestrictionOfHom X α M n
    (homOfLE (show V ≤ ⊤ from le_top)))
  rw [moduleHPrimeRestriction_eq_localizationComposite V α β σ hs M n]
  exact htot

end AlgebraicGeometry.Scheme.Cohomology
