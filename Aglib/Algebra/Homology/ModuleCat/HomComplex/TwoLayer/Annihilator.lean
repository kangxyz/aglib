/-
Copyright (c) 2026 kangxyz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.Algebra.Homology.ModuleCat.HomComplex.TwoLayer.Cohomology
public import Aglib.Algebra.Category.ModuleCat.ChangeOfRings.Coinduction.FiniteLengthExt

/-!
# Original unit-image annihilation on the actual first homology module

The original single-one dual homology is compared A-linearly with native
A-Ext-two into the literal coinduced coefficient. The coefficient augmentation
is the coinduction of the supplied base resolution. The actual unit Postnikov
row then detects scalars on the original H1 module once the actual dual H1
vanishes and scalar multiples of the native coefficient lie in the original
unit image. Those two geometric inputs are explicit, not derived here.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits CategoryTheory.Abelian
open Opposite HomologicalComplex

universe u

private theorem annihilator_exact_surjective_linearEquiv_comp
    {B L M N P : Type*} [CommRing B]
    [AddCommGroup L] [AddCommGroup M] [AddCommGroup N] [AddCommGroup P]
    [Module B L] [Module B M] [Module B N] [Module B P]
    (f : L →ₗ[B] M) (b : M →ₗ[B] N) (E : N ≃ₗ[B] P)
    (hex : Function.Exact f b) (hsurj : Function.Surjective b) :
    Function.Exact f (E.toLinearMap.comp b) ∧
      Function.Surjective (E.toLinearMap.comp b) := by
  constructor
  · intro φ
    constructor
    · intro hφ
      have hz : b φ = 0 := E.injective
        ((show E (b φ) = 0 from hφ).trans (map_zero E).symm)
      exact (hex φ).mp hz
    · intro hφ
      have hz : b φ = 0 := (hex φ).mpr hφ
      exact (congrArg E hz).trans (map_zero E)
  · intro z
    obtain ⟨φ, hφ⟩ := hsurj (E.symm z)
    refine ⟨φ, ?_⟩
    exact (congrArg E hφ).trans (E.apply_symm_apply z)

private theorem annihilator_scalar_of_exact_image
    {B L M N : Type*} [CommRing B]
    [AddCommGroup L] [AddCommGroup M] [AddCommGroup N]
    [Module B L] [Module B M] [Module B N]
    (f : L →ₗ[B] M) (b : M →ₗ[B] N)
    (hex : Function.Exact f b) (hsurj : Function.Surjective b)
    (a : B) (himage : ∀ φ : M, a • φ ∈ LinearMap.range f) :
    ∀ z : N, a • z = 0 := by
  intro z
  obtain ⟨φ, rfl⟩ := hsurj z
  obtain ⟨x, hx⟩ := himage φ
  calc
    a • b φ = b (a • φ) := (b.map_smul a φ).symm
    _ = b (f x) := congrArg b hx.symm
    _ = 0 := hex.apply_apply_eq_zero x

namespace CochainComplex.HomComplex.TwoLayerDual

/-- The standard derived-category model for modules over the coefficient ring. -/
local instance twoLayerAnnihilatorModuleDerived (B : Type u) [CommRing B] :
    HasDerivedCategory.{u + 1} (ModuleCat.{u} B) := HasDerivedCategory.standard _

variable {R A : Type u} [CommRing R] [CommRing A]
  (σ : R →+* A) (I : InjectiveResolution (ModuleCat.of R R))
  [hProjective : Module.Projective R
    ((ModuleCat.restrictScalars σ).obj (ModuleCat.of A A))]

local instance twoLayerAnnihilatorCoefficientKInjective :
    (resolutionCoefficient σ I).IsKInjective :=
  (ModuleCat.restrictCoextendScalarsAdj σ).isKInjective_map_of_injectiveComplex
    I.cochainComplex 0

local instance twoLayerAnnihilatorCoefficientQuasiIso :
    QuasiIso (coinducedCoefficientAugmentation σ I.cochainComplex I.ι') :=
  coefficientAugmentation_quasiIso σ I

include hProjective

/-- The original single-one comparison, model comparison and A-Ext comparison.
The coefficient and its augmentation are exactly the native coinduced ones. -/
def singleOneExtTwoLinearEquiv (M : ModuleCat.{u} A) :
    homology (resolutionCoefficient σ I) 1 (firstLayer M) ≃ₗ[A]
      Ext.{u} M (coinducedCoefficient σ) 2 := by
  let J := resolutionCoefficient σ I
  let L := (singleFunctor (ModuleCat.{u} A) 0).obj M
  let S := (DerivedCategory.singleFunctor (ModuleCat.{u} A) 0).obj M
  let e₁ : homology J 1 (firstLayer M) ≃ₗ[A] homology J 2 S :=
    singleOneHomologyEquiv.{u, u + 1} J M 1
  let e₂ : homology J 2 S ≃ₗ[A] (moduleComplex A L J).homology 2 :=
    (singleHomologyIso.{u, u + 1} J M 2).toLinearEquiv
  let e₃ : (moduleComplex A L J).homology 2 ≃ₗ[A]
      Ext.{u} M (coinducedCoefficient σ) 2 :=
    singleHomologyExtLinearEquiv.{u, u, u + 1, u}
      M (coinducedCoefficient σ) J
      (coinducedCoefficientAugmentation σ I.cochainComplex I.ι') 2
  exact e₁.trans (e₂.trans e₃)

/-- The forward value retains all three original comparison maps. -/
theorem singleOneExtTwoLinearEquiv_apply (M : ModuleCat.{u} A)
    (z : homology (resolutionCoefficient σ I) 1 (firstLayer M)) :
    singleOneExtTwoLinearEquiv σ I M z =
      singleHomologyExtLinearEquiv.{u, u, u + 1, u}
        M (coinducedCoefficient σ) (resolutionCoefficient σ I)
        (coinducedCoefficientAugmentation σ I.cochainComplex I.ι') 2
        ((singleHomologyIso.{u, u + 1} (resolutionCoefficient σ I) M 2).hom
          (singleOneHomologyEquiv.{u, u + 1} (resolutionCoefficient σ I) M 1 z)) := rfl

section UnitPostnikov

variable (X : DerivedCategory.Plus (ModuleCat.{u} A)) [X.IsGE 0] [X.IsLE 1]
  (η : (DerivedCategory.Plus.singleFunctor (ModuleCat.{u} A) 0).obj
    (ModuleCat.of A A) ⟶ X)
  [IsIso ((DerivedCategory.Plus.homologyFunctor (ModuleCat.{u} A) 0).map η)]

/-- The actual unsigned unit-Postnikov boundary in native A-Ext-two coordinates. -/
def unitPostnikovExtBoundary :
    coinducedCoefficient σ →ₗ[A]
      Ext.{u} ((DerivedCategory.Plus.homologyFunctor (ModuleCat.{u} A) 1).obj X)
        (coinducedCoefficient σ) 2 :=
  (singleOneExtTwoLinearEquiv σ I
    ((DerivedCategory.Plus.homologyFunctor (ModuleCat.{u} A) 1).obj X)).toLinearMap.comp
      (boundaryMap σ I
        ((DerivedCategory.Plus.homologyFunctor (ModuleCat.{u} A) 1).obj X)
        (unitPostnikovTriangle X η).mor₃)

/-- The literal original unit gives the short exact Ext-two row when the actual
dual H1 vanishes. The original triangle and all its arrows are constructed here. -/
theorem unitPostnikovExtBoundary_exact [IsRegularLocalRing R]
    (hR : ringKrullDim R = (2 : ℕ))
    (hM : IsFiniteLength R ((ModuleCat.restrictScalars σ).obj
      ((DerivedCategory.Plus.homologyFunctor (ModuleCat.{u} A) 1).obj X)))
    (hdual : IsZero (homology (resolutionCoefficient σ I) 1
      (DerivedCategory.Plus.ι.obj X))) :
    Function.Injective
        (unitMap σ I (DerivedCategory.Plus.ι.obj X) (DerivedCategory.Plus.ι.map η)) ∧
      Function.Exact
        (unitMap σ I (DerivedCategory.Plus.ι.obj X) (DerivedCategory.Plus.ι.map η))
        (unitPostnikovExtBoundary σ I X η) ∧
      Function.Surjective (unitPostnikovExtBoundary σ I X η) := by
  let M : ModuleCat.{u} A :=
    (DerivedCategory.Plus.homologyFunctor (ModuleCat.{u} A) 1).obj X
  let C : DerivedCategory (ModuleCat.{u} A) := DerivedCategory.Plus.ι.obj X
  let L : ModuleCat.{u} A := homology (resolutionCoefficient σ I) 0 C
  let Ω : ModuleCat.{u} A := coinducedCoefficient σ
  let N : ModuleCat.{u} A := homology (resolutionCoefficient σ I) 1 (firstLayer M)
  let P := Ext.{u} M Ω 2
  let T := unitPostnikovTriangle X η
  let f : L →ₗ[A] Ω := unitMap σ I C (DerivedCategory.Plus.ι.map η)
  let b : Ω →ₗ[A] N := boundaryMap σ I M T.mor₃
  let p := projectionMap σ I M C T.mor₂
  let E : N ≃ₗ[A] P := singleOneExtTwoLinearEquiv σ I M
  have hrow : Function.Injective f ∧ Function.Exact f b ∧
      Function.Exact b p ∧ Function.Surjective p :=
    unitPostnikov_obstruction_exact σ I hR X η hM
  let : Subsingleton (homology (resolutionCoefficient σ I) 1 C) :=
    ModuleCat.subsingleton_of_isZero hdual
  have hb : Function.Surjective b := by
    intro z
    exact (hrow.2.2.1 z).mp (Subsingleton.elim (p z) 0)
  have h := annihilator_exact_surjective_linearEquiv_comp f b E hrow.2.1 hb
  exact ⟨hrow.1, h.1, h.2⟩

/-- Scalar multiples in the ORIGINAL unit image annihilate the original H1
module, using native A-linearity and the coinduced Ext-two annihilator theorem. -/
theorem unitPostnikov_scalar_annihilates_of_image [IsRegularLocalRing R]
    (hR : ringKrullDim R = (2 : ℕ))
    (hM : IsFiniteLength R ((ModuleCat.restrictScalars σ).obj
      ((DerivedCategory.Plus.homologyFunctor (ModuleCat.{u} A) 1).obj X)))
    (hdual : IsZero (homology (resolutionCoefficient σ I) 1
      (DerivedCategory.Plus.ι.obj X)))
    (a : A)
    (himage : ∀ φ : coinducedCoefficient σ,
      a • φ ∈ LinearMap.range
        (unitMap σ I (DerivedCategory.Plus.ι.obj X) (DerivedCategory.Plus.ι.map η))) :
    ∀ m : (DerivedCategory.Plus.homologyFunctor (ModuleCat.{u} A) 1).obj X,
      a • m = 0 := by
  let M : ModuleCat.{u} A :=
    (DerivedCategory.Plus.homologyFunctor (ModuleCat.{u} A) 1).obj X
  let C : DerivedCategory (ModuleCat.{u} A) := DerivedCategory.Plus.ι.obj X
  let L : ModuleCat.{u} A := homology (resolutionCoefficient σ I) 0 C
  let Ω : ModuleCat.{u} A := coinducedCoefficient σ
  let P := Ext.{u} M Ω 2
  let f : L →ₗ[A] Ω := unitMap σ I C (DerivedCategory.Plus.ι.map η)
  let b : Ω →ₗ[A] P := unitPostnikovExtBoundary σ I X η
  have hrow : Function.Injective f ∧ Function.Exact f b ∧ Function.Surjective b :=
    unitPostnikovExtBoundary_exact σ I X η hR hM hdual
  have hExt : ∀ z : Ext.{u} M (coinducedCoefficient σ) 2, a • z = 0 :=
    annihilator_scalar_of_exact_image f b hrow.2.1 hrow.2.2 a himage
  exact (ModuleCat.coinducedExtTwo_scalar_annihilates_iff σ hR M hM a).mp hExt

end UnitPostnikov

end CochainComplex.HomComplex.TwoLayerDual
