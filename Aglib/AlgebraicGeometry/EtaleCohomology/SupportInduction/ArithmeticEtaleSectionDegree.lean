/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import
  Aglib.AlgebraicGeometry.EtaleCohomology.SupportInduction.ArithmeticSectionDegreeProperty
public import
  Aglib.AlgebraicGeometry.EtaleCohomology.Localization.CoefficientCartesianTargetZero
public import Aglib.CategoryTheory.Limits.Shapes.CartesianBaseChangeFamily
public import Aglib.RingTheory.KrullDimension.FiniteTypeBound

/-! # The original injective class over an actual arithmetic etale section

An actual etale base change gives an actual etale coefficient change. Its
inverse image preserves the given module injective by the lower-shriek
adjunction. The original Cartesian family and original class are transported
canonically. The supplied all-ranks curve property is then the sole local-zero
producer, and the resulting whole zero returns to the unchanged family.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits
open scoped TensorProduct

namespace AlgebraicGeometry.Scheme.EtaleCohomology

open Coefficients

universe u

attribute [local instance] hasSheafifyLarge hasSheafifyModules HasExt.standard

/-- Consume the all-ranks property at a genuine arithmetic etale section,
without a local-zero hypothesis or a new injective envelope. The original
base ring need not itself be arithmetic; the actual new base and original
coefficient ring have the displayed arithmetic hypotheses. -/
theorem exists_pointed_degree_refinement_of_arithmetic_etale_section
    (k : ℕ) (ih : ∀ d, ArithmeticPointedCurveModuleEffacement.{u} k d)
    (R S E : Type u) [CommRing R] [CommRing S] [CommRing E]
    [Algebra R S] [Algebra R E]
    [Algebra.FiniteType ℤ S] [Algebra.FiniteType ℤ E] [Algebra.Etale R E]
    {G Y : Scheme.{u}} [IsAffine G] (p : G ⟶ Spec (.of R))
    [SmoothOfRelativeDimension 1 p]
    (σ : Spec (.of E) ⟶ pullback p (Spec.algebraMap R E))
    (hσ : σ ≫ pullback.snd p (Spec.algebraMap R E) = 𝟙 _)
    (a : Y ⟶ G) (b : Y ⟶ Spec (.of S))
    (H : IsPullback a b p (Spec.algebraMap R S))
    (n : ℕ) (hn : 0 < n) (hunit : IsUnit (n : R))
    (I : ModuleSheaf (Spec (.of S)) (ULift.{u + 1} (ZMod n))) [Injective I]
    (c : Sheaf.H.{u + 2} ((inverseImage b).obj
      ((SheafOfModules.toSheaf (constantRing (Spec (.of S))
        (ULift.{u + 1} (ZMod n)))).obj I)) k)
    (Ω : Type u) [Field Ω] [IsSepClosed Ω] (xE : Spec (.of Ω) ⟶ Spec (.of E)) :
    ∃ (U : G.Etale) (xU : Spec (.of Ω) ⟶ U.left),
      xU ≫ U.hom = xE ≫ σ ≫ pullback.fst p (Spec.algebraMap R E) ∧
      cohomologyPullback.{u, u + 2, u + 2} (pullback.snd U.hom a) _ k c = 0 := by
  let C := E ⊗[R] S
  let : Algebra ℤ C := Ring.toIntAlgebra C
  let e := Spec.algebraMap R E
  let β := Spec.algebraMap R S
  let q := pullback.fst p e
  let pE := pullback.snd p e
  let T : Spec (.of C) ≅ pullback e β := (pullbackSpecIso R E S).symm
  let δ := T.hom ≫ pullback.fst e β
  let i := T.hom ≫ pullback.snd e β
  have K : IsPullback δ i e β :=
    IsPullback.of_iso_pullback ⟨by
      dsimp only [δ, i]
      simp only [Category.assoc, pullback.condition]⟩ T rfl rfl
  let : Etale e := HasRingHomProperty.Spec_iff.mpr
    (RingHom.etale_algebraMap.mpr (inferInstance : Algebra.Etale R E))
  let : Etale i := inferInstanceAs (Etale (T.hom ≫ pullback.snd e β))
  let : Etale q := inferInstanceAs (Etale (pullback.fst p e))
  let : MorphismProperty.IsStableUnderBaseChange (@SmoothOfRelativeDimension.{u} 1) :=
    smoothOfRelativeDimension_isStableUnderBaseChange 1
  let : SmoothOfRelativeDimension 1 pE :=
    MorphismProperty.of_isPullback (P := @SmoothOfRelativeDimension.{u} 1)
      (IsPullback.of_hasPullback p e) (inferInstance : SmoothOfRelativeDimension 1 p)
  let : IsScalarTower ℤ R S := IsScalarTower.of_algebraMap_eq' (Subsingleton.elim _ _)
  let : Algebra.FiniteType R S := Algebra.FiniteType.of_restrictScalars_finiteType ℤ R S
  let : IsScalarTower ℤ E C := IsScalarTower.of_algebraMap_eq' (Subsingleton.elim _ _)
  let : Algebra.FiniteType ℤ C := Algebra.FiniteType.trans
    (inferInstance : Algebra.FiniteType ℤ E) (inferInstance : Algebra.FiniteType E C)
  let : IsNoetherianRing E := Algebra.FiniteType.isNoetherianRing ℤ E
  obtain ⟨d, hd⟩ := Algebra.FiniteType.exists_ringKrullDim_le_of_finiteType_int C
  let v := pullback.snd i b
  let bE := pullback.fst i b
  let aE := H.baseChangeFamilyMap K
  have HE : IsPullback aE bE pE δ := H.baseChangeFamilyMap_isPullback K
  have HT : IsPullback aE v q a := H.baseChangeFamilyMap_target_isPullback K
  have hw : v ≫ b = bE ≫ i := pullback.condition.symm
  let J := (moduleInverseImage i (ULift.{u + 1} (ZMod n))).obj I
  let : Injective J := moduleInverseImage_etale_injective i (ULift.{u + 1} (ZMod n)) I
  let cE := moduleCoefficientComponentClass.{u, u + 2, u + 2}
    i v b bE hw (ULift.{u + 1} (ZMod n)) I k c
  have hunitE : IsUnit (n : E) := by
    simpa only [map_natCast] using hunit.map (algebraMap R E)
  have haff (F : Type u) [Field F] (f : Spec (.of F) ⟶ Spec (.of E)) :
      IsAffine (pullback pE f : Scheme.{u}) := inferInstance
  obtain ⟨U, z, hz, hc⟩ := exists_pointed_degree_refinement_of_section_of_arithmetic_rank_property
    k d (ih d) E C hd pE σ hσ haff δ aE bE HE n hn hunitE J cE Ω xE
  let V : G.Etale := Scheme.Etale.mk (U.hom ≫ q)
  refine ⟨V, z, ?_, ?_⟩
  · change z ≫ U.hom ≫ q = xE ≫ σ ≫ q
    rw [← Category.assoc, hz, Category.assoc]
  · exact moduleCoefficientComponentClass_target_zero
      i v b bE hw q a aE HT U.hom (ULift.{u + 1} (ZMod n)) I k c hc

end AlgebraicGeometry.Scheme.EtaleCohomology
