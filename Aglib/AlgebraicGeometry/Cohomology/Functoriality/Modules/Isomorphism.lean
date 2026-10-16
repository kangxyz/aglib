/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.Cohomology.Functoriality.Modules
public import Aglib.AlgebraicGeometry.Cohomology.Functoriality.Isomorphism
public import Aglib.AlgebraicGeometry.Modules.IsomorphismFunctors
public import Aglib.AlgebraicGeometry.Cohomology.BaseChange.Modules.Map

/-!
# Original module cohomology maps along scheme isomorphisms

The original additive coefficient mate is invertible for a scheme
isomorphism and an invertible module coefficient arrow. Consequently the
original `moduleCohomologyMapAlong` and ordinary module-pullback maps are
bijective. The proofs use the existing additive cohomology theorem and
the native module adjunction unit, with no quasicoherence or finiteness
hypothesis and no new cohomology map.
-/

@[expose] public section

noncomputable section

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

universe u

open CategoryTheory AlgebraicGeometry

namespace AlgebraicGeometry.Scheme.Cohomology

variable {X Y : Scheme.{u}} (f : X ⟶ Y) [IsIso f]

/-- An actual invertible coefficient arrow has an invertible original additive mate
along a scheme isomorphism. -/
theorem moduleCoefficientPullback_isIso_of_isIso {M : Y.Modules} {N : X.Modules}
    (φ : M ⟶ (Scheme.Modules.pushforward f).obj N) [IsIso φ] :
    IsIso (moduleCoefficientPullback f φ) := by
  let : (TopCat.Sheaf.pushforward AddCommGrpCat.{u} f.base).IsEquivalence :=
    zariskiPushforward_isEquivalence f
  dsimp only [moduleCoefficientPullback]
  rw [Adjunction.homEquiv_counit]
  infer_instance

/-- The original geometric module cohomology map is bijective for a scheme isomorphism
and an actual invertible module coefficient arrow. -/
theorem moduleCohomologyMapAlong_bijective {M : Y.Modules} {N : X.Modules}
    (φ : M ⟶ (Scheme.Modules.pushforward f).obj N) [IsIso φ] (q : ℕ) :
    Function.Bijective (moduleCohomologyMapAlong f φ q) := by
  let : IsIso (moduleCoefficientPullback f φ) := moduleCoefficientPullback_isIso_of_isIso f φ
  exact zariskiCohomologyMap_bijective f _ _ (moduleCoefficientPullback f φ) q

/-- Ordinary pullback along a scheme isomorphism gives a bijection on original module
cohomology through its unchanged geometric adjunction unit. -/
theorem moduleCohomologyPullback_bijective (M : Y.Modules) (q : ℕ) :
    Function.Bijective (moduleCohomologyPullback f M q) := by
  let : (Scheme.Modules.pullback f).IsEquivalence :=
    Scheme.Modules.pullback_isEquivalence_of_isIso f
  exact moduleCohomologyMapAlong_bijective f
    ((Scheme.Modules.pullbackPushforwardAdjunction f).unit.app M) q

/-- The original scalar-compatible cohomology map is an isomorphism for a scheme
isomorphism and an actual isomorphism from the ordinary pulled coefficient. -/
def moduleCohomologyRestrictionIsoOfPullbackIso
    {R S : Type u} [CommRing R] [CommRing S]
    (σ : R →+* S) (α : R →+* Γ(Y, ⊤)) (β : S →+* Γ(X, ⊤))
    (h : f.appTop.hom.comp α = β.comp σ) (M : Y.Modules) {N : X.Modules}
    (C : (Scheme.Modules.pullback f).obj M ≅ N) (q : ℕ) :
    letI := moduleCohomologyModuleOfHom Y α M q
    letI := moduleCohomologyModuleOfHom X β N q
    ModuleCat.of R (Sheaf.H.{u + 1} (moduleAddSheaf Y M) q) ≅
      (ModuleCat.restrictScalars σ).obj
        (ModuleCat.of S (Sheaf.H.{u + 1} (moduleAddSheaf X N) q)) := by
  letI := moduleCohomologyModuleOfHom Y α M q
  letI := moduleCohomologyModuleOfHom X β N q
  let φ : M ⟶ (Scheme.Modules.pushforward f).obj N :=
    (Scheme.Modules.pullbackPushforwardAdjunction f).unit.app M ≫
      (Scheme.Modules.pushforward f).map C.hom
  let : (Scheme.Modules.pullback f).IsEquivalence :=
    Scheme.Modules.pullback_isEquivalence_of_isIso f
  let : IsIso φ := inferInstanceAs (IsIso
    ((Scheme.Modules.pullbackPushforwardAdjunction f).unit.app M ≫
      (Scheme.Modules.pushforward f).map C.hom))
  let μ := moduleCohomologyRestrictionMap f σ α β h φ q
  let : IsIso μ := (ConcreteCategory.isIso_iff_bijective μ).mpr
    (moduleCohomologyMapAlong_bijective f φ q)
  exact asIso μ

/-- The scalar-compatible cohomology isomorphism retains the original geometric map
and the original module adjunction unit in its forward arrow. -/
theorem moduleCohomologyRestrictionIsoOfPullbackIso_hom_apply
    {R S : Type u} [CommRing R] [CommRing S]
    (σ : R →+* S) (α : R →+* Γ(Y, ⊤)) (β : S →+* Γ(X, ⊤))
    (h : f.appTop.hom.comp α = β.comp σ) (M : Y.Modules) {N : X.Modules}
    (C : (Scheme.Modules.pullback f).obj M ≅ N) (q : ℕ)
    (x : Sheaf.H.{u + 1} (moduleAddSheaf Y M) q) :
    (moduleCohomologyRestrictionIsoOfPullbackIso f σ α β h M C q).hom x =
      moduleCohomologyMapAlong f
        ((Scheme.Modules.pullbackPushforwardAdjunction f).unit.app M ≫
          (Scheme.Modules.pushforward f).map C.hom) q x := rfl

end AlgebraicGeometry.Scheme.Cohomology
