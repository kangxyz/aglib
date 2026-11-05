/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import
  Aglib.AlgebraicGeometry.EtaleCohomology.SupportInduction.ArithmeticNormalHigherSelected
public import
Aglib.AlgebraicGeometry.EtaleCohomology.Fields.TwoFieldEffacement.GenericHigherNormalOpenEffacement
public import Aglib.AlgebraicGeometry.EtaleCohomology.Continuity.StagePrincipalPullbackZero

/-! # Actual higher-class production closes the normal coefficient branch

The existing generic higher-class producer constructs its finite fields and
literal normal principal zero internally. The full selected-field support
construction consumes that produced result. The original source and target
mark are unchanged, with only lower-degree and smaller-rank induction inputs.
-/

@[expose] public noncomputable section
open CategoryTheory CategoryTheory.Limits
open IsLocalization.PrincipalDiagram
open scoped nonZeroDivisors
namespace AlgebraicGeometry.Scheme.EtaleCohomology
open Coefficients TwoFieldEffacement
universe u
attribute [local instance] hasSheafifyLarge hasSheafifyModules HasExt.standard

/-- Actual generic higher vanishing and support induction give the original
pointed zero over a normal arithmetic coefficient domain. -/
theorem exists_arithmetic_normal_coefficient_higher_refinement_of_lower_rank
    (q : ℕ) (hq : 2 ≤ q)
    (houter : ∀ r : ℕ, 1 ≤ r → r < q → ArithmeticCurveModuleInjectiveVanishing.{u} r)
    (d : ℕ) (ih : ∀ r < d, ArithmeticPointedCurveModuleEffacement.{u} q r)
    (R B : Type u) [CommRing R] [CommRing B] [IsDomain B] [IsIntegrallyClosed B]
    [Algebra.FiniteType ℤ R] [Algebra.FiniteType ℤ B]
    (hd : ringKrullDim B ≤ (d : ℕ))
    {G Y : Scheme.{u}} (p : G ⟶ Spec (.of R))
    [SmoothOfRelativeDimension 1 p] [GeometricallyConnected p]
    [QuasiCompact p] [QuasiSeparated p]
    (σ : Spec (.of R) ⟶ G) (hσ : σ ≫ p = 𝟙 _)
    (haff : ∀ (K : Type u) [Field K] (z : Spec (.of K) ⟶ Spec (.of R)),
      IsAffine (pullback p z : Scheme.{u}))
    (β : Spec (.of B) ⟶ Spec (.of R))
    (a : Y ⟶ G) (b : Y ⟶ Spec (.of B)) (H : IsPullback a b p β)
    (n : ℕ) (hn : 0 < n) (hunit : IsUnit (n : R))
    (I : ModuleSheaf (Spec (.of B)) (ULift.{u + 1} (ZMod n))) [Injective I]
    (c : Sheaf.H.{u + 2} ((inverseImage b).obj
      ((SheafOfModules.toSheaf (constantRing (Spec (.of B))
        (ULift.{u + 1} (ZMod n)))).obj I)) q)
    (Ω : Type u) [Field Ω] [IsSepClosed Ω] (x : Spec (.of Ω) ⟶ Spec (.of R)) :
    ∃ (U : G.Etale) (xU : Spec (.of Ω) ⟶ U.left),
      xU ≫ U.hom = x ≫ σ ∧
      cohomologyPullback.{u, u + 2, u + 2} (pullback.snd U.hom a) _ q c = 0 := by
  let : IsNoetherianRing B := Algebra.FiniteType.isNoetherianRing ℤ B
  let F := FractionRing B
  let k := Spec.algebraMap B F
  let : QuasiCompact b := MorphismProperty.of_isPullback H inferInstance
  let : QuasiSeparated b := MorphismProperty.of_isPullback H inferInstance
  have Hgeneric : IsPullback (pullback.fst b k ≫ a) (pullback.snd b k) p (k ≫ β) :=
    (IsPullback.of_hasPullback b k).paste_horiz H
  let : IsAffine (pullback p (k ≫ β) : Scheme.{u}) := haff F (k ≫ β)
  let : IsAffine (pullback b k : Scheme.{u}) := IsAffine.of_isIso Hgeneric.isoPullback.hom
  let : MorphismProperty.IsStableUnderBaseChange (@SmoothOfRelativeDimension.{u} 1) :=
    smoothOfRelativeDimension_isStableUnderBaseChange 1
  let : SmoothOfRelativeDimension 1 (pullback.snd b k) :=
    MorphismProperty.of_isPullback (P := @SmoothOfRelativeDimension.{u} 1) Hgeneric
      (inferInstance : SmoothOfRelativeDimension 1 p)
  let : GeometricallyConnected (pullback.snd b k) :=
    MorphismProperty.of_isPullback Hgeneric inferInstance
  let M := (SheafOfModules.toSheaf (constantRing (Spec (.of B))
    (ULift.{u + 1} (ZMod n)))).obj I
  have hkill : n • 𝟙 M = 0 := Functor.map_nsmul_id_eq_zero
    (SheafOfModules.toSheaf (constantRing (Spec (.of B)) (ULift.{u + 1} (ZMod n)))) I n
    (ModuleCat.Sheaf.ConstantRing.uLiftZMod_nsmul_id_eq_zero
      (Spec (.of B)).smallEtaleTopology n I)
  have hunitB : IsUnit (n : B) := by
    simpa only [map_natCast] using hunit.map (Spec.preimage β).hom
  obtain ⟨K, E, hE, hKE, hnormal⟩ := exists_generic_higher_normal_principalOpen_zero
    B F b M n hn hkill hunitB q hq c
  let : Field E := hE
  let : Algebra K E := hKE
  let : Algebra F E := ((algebraMap K E).comp (algebraMap F K)).toAlgebra
  let : Algebra B E := ((algebraMap F E).comp (algebraMap B F)).toAlgebra
  let : IsScalarTower B F E := IsScalarTower.of_algebraMap_eq' rfl
  exact exists_arithmetic_degree_refinement_of_normal_principal_zero
    q (by omega) houter d ih R B F E hd p σ hσ haff β a b H n hn hunit I c hnormal Ω x

end AlgebraicGeometry.Scheme.EtaleCohomology
