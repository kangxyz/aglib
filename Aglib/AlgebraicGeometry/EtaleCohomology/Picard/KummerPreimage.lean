/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.EtaleCohomology.Kummer.BoundaryNaturality

/-! # Original Kummer preimages of actual power-trivial line bundles

The original short exact Kummer sequence supplies an original H1(mu_n) class
with the literal Picard image on an arbitrary scheme. The original inclusion
square controls all geometric restrictions of a chosen preimage. No roots of
all global units, uniqueness of the preimage, or curve hypothesis is needed.
-/

@[expose] public noncomputable section

open CategoryTheory AlgebraicGeometry
open AlgebraicGeometry.Scheme.Modules.Invertible
open GroupCohomology.Kummer.Coefficients GroupCohomology.Kummer.CoefficientBaseChange

namespace AlgebraicGeometry.Scheme.EtaleCohomology

universe u w w'

namespace Picard

variable (X : Scheme.{u}) [HasExt.{w} (AbelianSheaf.{u, u + 1} X)]

/-- Original Kummer exactness lifts every original n-torsion Picard class. -/
theorem exists_kummerPreimage_of_nsmul_eq_zero (n : ℕ) (hn : 0 < n)
    (hinv : IsUnit (n : Γ(X, ⊤))) (c : PicardGroup X) (hc : n • c = 0) :
    ∃ ξ : Sheaf.H.{w} (mu X n) 1,
      Sheaf.H.map (inclusion X n) 1 ξ = picardCohomologyEquiv X c := by
  apply Sheaf.H.longSequence_exact₂ (Kummer.shortExact X n hn hinv)
  change Sheaf.H.map (power X n) 1 (picardCohomologyEquiv X c) = 0
  have hp (a : Sheaf.H.{w} (gm X) 1) :
      Sheaf.H.map (power X n) 1 a = n • a := by
    change (Sheaf.functorH _ 1).map (n • 𝟙 (gm X)) a = n • a
    rw [CategoryTheory.Functor.map_nsmul, CategoryTheory.Functor.map_id]
    rfl
  rw [hp, ← map_nsmul, hc, map_zero]

/-- An actual power trivialization gives an original Kummer preimage of the
literal line-bundle class, without imposing a global-unit root hypothesis. -/
theorem exists_lineBundle_kummerPreimage (L : LineBundle X) (n : ℕ) (hn : 0 < n)
    (hinv : IsUnit (n : Γ(X, ⊤)))
    (τ : (tensorPowerLineBundle X L n).val ≅ SheafOfModules.unit X.ringCatSheaf) :
    ∃ ξ : Sheaf.H.{w} (mu X n) 1,
      Sheaf.H.map (inclusion X n) 1 ξ = picardCohomologyEquiv X (classOf X L) :=
  exists_kummerPreimage_of_nsmul_eq_zero X n hn hinv (classOf X L)
    (TrivializedPower.pair_class_nsmul X ⟨L, τ⟩)

/-- One original H1 class chosen from Kummer exactness. No uniqueness or
compatibility with separately chosen preimages is asserted. -/
def lineBundleKummerClass (L : LineBundle X) (n : ℕ) (hn : 0 < n)
    (hinv : IsUnit (n : Γ(X, ⊤)))
    (τ : (tensorPowerLineBundle X L n).val ≅ SheafOfModules.unit X.ringCatSheaf) :
    Sheaf.H.{w} (mu X n) 1 :=
  (exists_lineBundle_kummerPreimage X L n hn hinv τ).choose

/-- The chosen class maps to the original frame class of the actual line bundle. -/
theorem lineBundleKummerClass_inclusion (L : LineBundle X) (n : ℕ) (hn : 0 < n)
    (hinv : IsUnit (n : Γ(X, ⊤)))
    (τ : (tensorPowerLineBundle X L n).val ≅ SheafOfModules.unit X.ringCatSheaf) :
    Sheaf.H.map (inclusion X n) 1 (lineBundleKummerClass X L n hn hinv τ) =
      picardCohomologyEquiv X (classOf X L) :=
  (exists_lineBundle_kummerPreimage X L n hn hinv τ).choose_spec

end Picard

variable {X S : Scheme.{u}}
  [HasExt.{w} (AbelianSheaf.{u, u + 1} X)]
  [HasExt.{w'} (AbelianSheaf.{u, u + 1} S)]

namespace Kummer

/-- The original root inclusion commutes with original geometric cohomology
pullback. The Gm coefficient comparison need not be invertible. -/
theorem rootsCohomologyPullback_inclusion (f : S ⟶ X) (n : ℕ) (hn : 0 < n)
    (hinv : IsUnit (n : Γ(X, ⊤))) (q : ℕ) (ξ : Sheaf.H.{w} (mu X n) q) :
    Sheaf.H.map (inclusion S n) q (rootsCohomologyPullback f n hn hinv q ξ) =
      Picard.gmCohomologyPullback f q (Sheaf.H.map (inclusion X n) q ξ) := by
  simp only [rootsCohomologyPullback, Picard.gmCohomologyPullback,
    AddMonoidHom.comp_apply]
  rw [cohomologyPullback_coefficientMap, ← Sheaf.H.map_comp_apply,
    ← Sheaf.H.map_comp_apply, ← rootsUnit_adjoint f n hn hinv]
  exact congrArg (fun a => Sheaf.H.map a q (cohomologyPullback f (mu X n) q ξ))
    (adjoint_square (inverseImageAdjunction f) (inclusion X n) (inclusion S n)
      (rootsUnit f n) (gmUnit f) (inclusion_unit f n)).symm

end Kummer

namespace Picard

/-- Every actual restriction of one chosen preimage has the literal pulled
line-bundle Picard image. This does not compare independently chosen lifts. -/
theorem kummerPreimage_pullback (f : S ⟶ X) (L : LineBundle X)
    (n : ℕ) (hn : 0 < n) (hinv : IsUnit (n : Γ(X, ⊤)))
    (ξ : Sheaf.H.{w} (mu X n) 1)
    (hξ : Sheaf.H.map (inclusion X n) 1 ξ = picardCohomologyEquiv X (classOf X L)) :
    Sheaf.H.map (inclusion S n) 1 (Kummer.rootsCohomologyPullback f n hn hinv 1 ξ) =
      picardCohomologyEquiv S (classOf S (pullbackLineBundle f L)) := by
  rw [Kummer.rootsCohomologyPullback_inclusion, hξ, picardCohomologyEquiv_pullback,
    pullbackClass_classOf]

/-- Specialization of the selected original class, with the original root
coefficient map and the literal pulled line bundle retained. -/
theorem lineBundleKummerClass_pullback_inclusion (f : S ⟶ X) (L : LineBundle X)
    (n : ℕ) (hn : 0 < n) (hinv : IsUnit (n : Γ(X, ⊤)))
    (τ : (tensorPowerLineBundle X L n).val ≅ SheafOfModules.unit X.ringCatSheaf) :
    Sheaf.H.map (inclusion S n) 1
        (Kummer.rootsCohomologyPullback f n hn hinv 1
          (lineBundleKummerClass X L n hn hinv τ)) =
      picardCohomologyEquiv S (classOf S (pullbackLineBundle f L)) :=
  kummerPreimage_pullback f L n hn hinv _ (lineBundleKummerClass_inclusion X L n hn hinv τ)

end Picard

end AlgebraicGeometry.Scheme.EtaleCohomology
