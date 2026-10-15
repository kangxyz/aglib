/-
Copyright (c) 2026 algebraic-geometry contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.Cohomology.DirectImage.Affine.Localization.Principal
public import Aglib.AlgebraicGeometry.Cohomology.DirectImage.ResolutionSections.Pushforward.Spec
public import Aglib.AlgebraicGeometry.Cohomology.DirectImage.ResolutionSections.Open.Naturality

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
        (CommRingCat.of R) (.up ℤ) (PrimeSpectrum.basicOpen r) K) (n : ℤ)).hom := by
  let K := ((Scheme.Modules.pushforward f).mapHomologicalComplex (.up ℤ)).obj I.cochainComplex
  let α := f.appTop.hom.comp (Scheme.ΓSpecIso (CommRingCat.of R)).inv.hom
  let V := f ⁻¹ᵁ PrimeSpectrum.basicOpen r
  let := moduleHPrimeModuleOfHom X α M n ⊤
  let := moduleHPrimeModuleOfHom X α M n V
  let e₀ := (homologyFunctor (ModuleCat.{u} R) (.up ℤ) (n : ℤ)).mapIso
    (moduleSpecPushforwardSectionsComplexIso f (.up ℤ) I.cochainComplex ⊤)
  let e₁ := (homologyFunctor (ModuleCat.{u} R) (.up ℤ) (n : ℤ)).mapIso
    (moduleSpecPushforwardSectionsComplexIso f (.up ℤ) I.cochainComplex
      (PrimeSpectrum.basicOpen r))
  let a := e₀.toLinearEquiv.trans
    (moduleResolutionOpenSectionsCohomologyLinearEquiv X α ⊤ I n)
  let b := e₁.toLinearEquiv.trans
    (moduleResolutionOpenSectionsCohomologyLinearEquiv X α V I n)
  let ρ := moduleHPrimeRestrictionOfHom X α M n (homOfLE (show V ≤ ⊤ from le_top))
  let t := homologyMap (Scheme.Modules.Complex.specSectionsComplexRestriction
    (CommRingCat.of R) (.up ℤ) (PrimeSpectrum.basicOpen r) K) (n : ℤ)
  let : IsLocalizedModule (Submonoid.powers r) ρ :=
    moduleHPrimeRestriction_isLocalizedModule_principal f M r n
  have hc := moduleSpecPushforwardSectionsComplexIso_restriction f (.up ℤ)
    I.cochainComplex (PrimeSpectrum.basicOpen r)
  have hh := congrArg ((homologyFunctor (ModuleCat.{u} R) (.up ℤ) (n : ℤ)).map) hc
  simp only [Functor.map_comp] at hh
  have heq : b.toLinearMap.comp t.hom = ρ.comp a.toLinearMap := by
    ext x
    have hx := ConcreteCategory.congr_hom hh x
    change e₁.hom (t x) = homologyMap
      (moduleResolutionOpenSectionRestriction X α (homOfLE (show V ≤ ⊤ from le_top)) I)
        (n : ℤ) (e₀.hom x) at hx
    change moduleResolutionOpenSectionsCohomologyLinearEquiv X α V I n (e₁.hom (t x)) =
      ρ (moduleResolutionOpenSectionsCohomologyLinearEquiv X α ⊤ I n (e₀.hom x))
    rw [hx]
    exact moduleResolutionOpenSectionsCohomologyLinearEquiv_restriction X α
      (homOfLE (show V ≤ ⊤ from le_top)) I n (e₀.hom x)
  have hpre : IsLocalizedModule (Submonoid.powers r) (ρ.comp a.toLinearMap) :=
    IsLocalizedModule.of_linearEquiv_right (Submonoid.powers r) ρ a
  have hb : IsLocalizedModule (Submonoid.powers r) (b.toLinearMap.comp t.hom) := by
    rw [heq]
    exact hpre
  change IsLocalizedModule (Submonoid.powers r) t.hom
  exact (IsLocalizedModule.comp_iff_of_bijective_left (Submonoid.powers r)
    b.toLinearMap b.bijective).mp hb

/-- The same original principal restriction localizes actual resolution-section homology in
every integer degree; the original resolution is zero in negative degrees. -/
theorem moduleResolutionPushforwardSectionsRestriction_isLocalized
    (f : X ⟶ Spec (CommRingCat.of R)) [QuasiCompact f] [QuasiSeparated f]
    (M : X.Modules) [M.IsQuasicoherent] (I : InjectiveResolution M) (r : R) (i : ℤ) :
    let K := ((Scheme.Modules.pushforward f).mapHomologicalComplex (.up ℤ)).obj I.cochainComplex
    IsLocalizedModule.Away r
      (homologyMap (Scheme.Modules.Complex.specSectionsComplexRestriction
        (CommRingCat.of R) (.up ℤ) (PrimeSpectrum.basicOpen r) K) i).hom := by
  by_cases hi : 0 ≤ i
  · obtain ⟨n, rfl⟩ := Int.eq_ofNat_of_zero_le hi
    exact moduleResolutionPushforwardSectionsRestriction_isLocalized_nat f M I r n
  · let K := ((Scheme.Modules.pushforward f).mapHomologicalComplex (.up ℤ)).obj I.cochainComplex
    let A := (moduleSpecΓFunctor.mapHomologicalComplex (.up ℤ)).obj K
    let F : (Spec (CommRingCat.of R)).Modules ⥤ ModuleCat.{u} R :=
      Scheme.Modules.Complex.specSectionsFunctor (CommRingCat.of R) (PrimeSpectrum.basicOpen r)
    let : F.PreservesZeroMorphisms := ⟨by intros; rfl⟩
    let B := (F.mapHomologicalComplex (.up ℤ)).obj K
    have hi' : i < 0 := lt_of_not_ge hi
    let : Subsingleton (A.homology i) :=
      ModuleCat.subsingleton_of_isZero (CochainComplex.isZero_of_isGE A 0 i hi')
    let : Subsingleton (B.homology i) :=
      ModuleCat.subsingleton_of_isZero (CochainComplex.isZero_of_isGE B 0 i hi')
    constructor
    · intro s
      have he : (algebraMap R (Module.End R (B.homology i))) s = 1 := Subsingleton.elim _ _
      rw [he]
      exact isUnit_one
    · intro y
      exact ⟨(0, 1), Subsingleton.elim _ _⟩
    · intro x y _
      exact ⟨1, Subsingleton.elim _ _⟩

/-- The original affine tilde–global-sections counit on the actual pushed-forward module
resolution is a quasi-isomorphism for every quasicoherent coefficient and qcqs morphism. -/
theorem moduleResolutionPushforwardTildeCounit_quasiIso
    (f : X ⟶ Spec (CommRingCat.of R)) [QuasiCompact f] [QuasiSeparated f]
    (M : X.Modules) [M.IsQuasicoherent] (I : InjectiveResolution M) :
    let K := ((Scheme.Modules.pushforward f).mapHomologicalComplex (.up ℤ)).obj I.cochainComplex
    QuasiIso (Scheme.Modules.Complex.tildeGlobalSectionsCounit (CommRingCat.of R) (.up ℤ) K) :=
  Scheme.Modules.Complex.tildeGlobalSectionsCounit_quasiIso_of_isLocalized
    (CommRingCat.of R) _
    (fun r i => moduleResolutionPushforwardSectionsRestriction_isLocalized f M I r i)

end AlgebraicGeometry.Scheme.Cohomology
