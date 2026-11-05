/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import
  Aglib.AlgebraicGeometry.EtaleCohomology.SupportInduction.ArithmeticFiniteCoefficientDegreeStep
public import
  Aglib.AlgebraicGeometry.EtaleCohomology.Fields.TwoFieldEffacement.NormalModelClassZeroSpreading
public import Aglib.AlgebraicGeometry.EtaleCohomology.Continuity.StagePrincipalPullbackZero

/-! # The complete fixed-degree induction construction on selected normal models

The literal integral closure retains its supplied fraction-field tower. Its
finite coefficient map is surjective by actual lying over, and its original
principal zero feeds finite coefficient and lower-rank support induction.
This full variable-field construction is specialized only after generic
higher-class production, avoiding dependent repackaging of a large producer.
-/

@[expose] public noncomputable section
open CategoryTheory CategoryTheory.Limits
open IsLocalization.PrincipalDiagram
open scoped nonZeroDivisors
namespace AlgebraicGeometry.Scheme.EtaleCohomology
open Coefficients TwoFieldEffacement
universe u
attribute [local instance] hasSheafifyLarge hasSheafifyModules HasExt.standard

/-- The selected actual normal coefficient model supplies pointed degree-q zero. -/
theorem exists_arithmetic_degree_refinement_of_normal_principal_zero
    (q : ℕ) (hq : 0 < q)
    (houter : ∀ r : ℕ, 1 ≤ r → r < q → ArithmeticCurveModuleInjectiveVanishing.{u} r)
    (d : ℕ) (ih : ∀ r < d, ArithmeticPointedCurveModuleEffacement.{u} q r)
    (R B F E : Type u) [CommRing R] [CommRing B] [Field F] [Field E]
    [Algebra B F] [IsFractionRing B F] [Algebra F E] [Algebra B E]
    [IsScalarTower B F E] [Algebra.FiniteType ℤ R] [Algebra.FiniteType ℤ B]
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
    (hzero : NormalPrincipalOpenClassZero B E b
      ((inverseImage b).obj ((SheafOfModules.toSheaf (constantRing (Spec (.of B))
        (ULift.{u + 1} (ZMod n)))).obj I)) q c)
    (Ω : Type u) [Field Ω] [IsSepClosed Ω] (x : Spec (.of Ω) ⟶ Spec (.of R)) :
    ∃ (U : G.Etale) (xU : Spec (.of Ω) ⟶ U.left),
      xU ≫ U.hom = x ≫ σ ∧
      cohomologyPullback.{u, u + 2, u + 2} (pullback.snd U.hom a) _ q c = 0 := by
  let L := integralClosure B E
  obtain ⟨hfin, _hnoeth, _hnormal, _hfrac, _hfinite, t, ht, _hne, hopen⟩ := hzero
  let : Module.Finite B L := hfin
  let : Algebra ℤ L := Ring.toIntAlgebra L
  let : IsScalarTower ℤ B L := IsScalarTower.of_algebraMap_eq' (Subsingleton.elim _ _)
  let : Algebra.FiniteType ℤ L := Algebra.FiniteType.trans
    (inferInstance : Algebra.FiniteType ℤ B) (inferInstance : Algebra.FiniteType B L)
  let : FaithfulSMul B L := (faithfulSMul_iff_algebraMap_injective B L).mpr
    (SeparableBaseSquare.closure_algebraMap_injective B F E)
  let : Surjective (Spec.algebraMap B L) := ⟨Algebra.IsIntegral.comap_surjective B L⟩
  have hprincipal := Continuity.principalPullback_zero_of_stageOpen_zero L⁰ t
    (pullback.snd b (Spec.algebraMap B L)) (pullback.fst b (Spec.algebraMap B L))
    _ q c hopen
  exact exists_arithmetic_finite_coefficient_degree_refinement_of_lower_rank
    q hq houter d ih R B L hd p σ hσ haff β a b H n hn hunit I c
    (denominator L⁰ t) ht hprincipal Ω x

end AlgebraicGeometry.Scheme.EtaleCohomology
