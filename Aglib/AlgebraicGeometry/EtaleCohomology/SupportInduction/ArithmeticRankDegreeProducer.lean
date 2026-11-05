/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import
  Aglib.AlgebraicGeometry.EtaleCohomology.SupportInduction.ArithmeticNormalArrayDegreeProducer
public import Aglib.AlgebraicGeometry.Spec.MinimalPrimeNormalizationArrow

/-! # Arithmetic coefficient-rank induction in a fixed higher degree

The actual minimal-prime normalization arrow gives finite arithmetic source
and coefficient components. The genuine higher-degree normal producer kills
each component, and the original finite-family return retains the point and
class. Natural-number strong induction discharges every smaller-rank input.
Strictly smaller cohomological degrees remain explicit outer assumptions.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry.Scheme.EtaleCohomology

open Coefficients
open AlgebraicGeometry.Scheme.EtaleCohomology.Finite
open AlgebraicGeometry.Scheme.EtaleCohomology.Finite.GeometricNeighborhood

universe u eY

attribute [local instance] hasSheafifyLarge hasSheafifyModules HasExt.standard

/-- The full induction step for arithmetic finite-type rings and an arbitrary
original coefficient arrow, without a local-zero premise. -/
theorem exists_arithmetic_arrow_pointed_degree_zero_of_lower_rank
    (k : ℕ) (hk : 2 ≤ k)
    (houter : ∀ r : ℕ, 1 ≤ r → r < k → ArithmeticCurveModuleInjectiveVanishing.{u} r)
    (d : ℕ) (ih : ∀ r < d, ArithmeticPointedCurveModuleEffacement.{u} k r)
    (A B : Type u)
    [CommRing A]
    [CommRing B]
    (f : A →+* B)
    [Algebra.FiniteType ℤ A] [Algebra.FiniteType ℤ B]
    (hd : ringKrullDim B ≤ (d : ℕ))
    {X Y : Scheme.{u}} (p : X ⟶ Spec (CommRingCat.of A))
    [SmoothOfRelativeDimension 1 p] [GeometricallyConnected p]
    [QuasiCompact p] [QuasiSeparated p]
    (σ : Spec (CommRingCat.of A) ⟶ X) (hσ : σ ≫ p = 𝟙 _)
    (haff : ∀ (F : Type u) [Field F]
      (z : Spec (CommRingCat.of F) ⟶ Spec (CommRingCat.of A)),
      IsAffine (pullback p z : Scheme.{u}))
    (a : Y ⟶ X) (b : Y ⟶ Spec (CommRingCat.of B))
    (H : IsPullback a b p (Spec.map (CommRingCat.ofHom f)))
    (n : ℕ) (hn : 0 < n) (hunit : IsUnit (n : A))
    (I : ModuleSheaf (Spec (CommRingCat.of B)) (ULift.{u + 1} (ZMod n))) [Injective I]
    [HasExt.{eY} (AbelianSheaf.{u, u + 1} Y)]
    (c : Sheaf.H.{eY} ((inverseImage b).obj
      ((SheafOfModules.toSheaf (constantRing (Spec (CommRingCat.of B))
        (ULift.{u + 1} (ZMod n)))).obj I)) k)
    (Ω : Type u) [Field Ω] [IsSepClosed Ω]
    (x : Spec (CommRingCat.of Ω) ⟶ Spec (CommRingCat.of A)) :
    ∃ (U : X.Etale) (xU : Spec (CommRingCat.of Ω) ⟶ U.left),
      xU ≫ U.hom = x ≫ σ ∧
      cohomologyPullback.{u, eY, u + 2} (pullback.snd U.hom a) _ k c = 0 := by
  classical
  have hA : IsNagataRing.{u, 0} A := IsNagataRing.of_finiteType_int A
  have hB : IsNagataRing.{u, 0} B := IsNagataRing.of_finiteType_int B
  let : IsNoetherianRing B := hB.isNoetherianRing
  let : Fintype (minimalPrimes B) :=
    (minimalPrimes.finite_of_isNoetherianRing (R := B)).fintype
  let R (i : minimalPrimes B) : Type u := RingHom.MinimalPrimeNormalization.sourceComponent f i
  let S (i : minimalPrimes B) : Type u := Algebra.minimalPrimeNormalization B i
  have hR (i : minimalPrimes B) :=
    RingHom.MinimalPrimeNormalization.sourceComponent_properties f hA i
  have hS (i : minimalPrimes B) :=
    RingHom.MinimalPrimeNormalization.coefficientComponent_properties hB i
  let : ∀ i, CommRing (R i) := fun i => inferInstance
  let : ∀ i, CommRing (S i) := fun i => inferInstance
  let : ∀ i, IsDomain (R i) := fun i => (hR i).1
  let : ∀ i, IsIntegrallyClosed (R i) := fun i => (hR i).2.1
  let : ∀ i, IsDomain (S i) := fun i => (hS i).2.1
  let : ∀ i, IsIntegrallyClosed (S i) := fun i => (hS i).2.2.1
  let r (i : minimalPrimes B) : R i →+* S i := RingHom.MinimalPrimeNormalization.componentMap f i
  let s (i : minimalPrimes B) : A →+* R i := RingHom.MinimalPrimeNormalization.sourceMap f i
  let t (i : minimalPrimes B) : B →+* S i := algebraMap B (S i)
  let : ∀ i, Algebra A (R i) := fun i => (s i).toAlgebra
  let : ∀ i, Module.Finite A (R i) := fun i => RingHom.finite_algebraMap.mp
    (RingHom.MinimalPrimeNormalization.sourceMap_finite f hA i)
  let : ∀ i, Algebra ℤ (R i) := fun i => Ring.toIntAlgebra (R i)
  let : ∀ i, IsScalarTower ℤ A (R i) := fun i =>
    IsScalarTower.of_algebraMap_eq' (Subsingleton.elim _ _)
  let : ∀ i, Algebra.FiniteType ℤ (R i) := fun i => Algebra.FiniteType.trans
    (inferInstance : Algebra.FiniteType ℤ A) (inferInstance : Algebra.FiniteType A (R i))
  let : ∀ i, Algebra B (S i) := fun i => inferInstance
  let : ∀ i, Module.Finite B (S i) := fun i => (hS i).1
  let : ∀ i, Algebra ℤ (S i) := fun i => Ring.toIntAlgebra (S i)
  let : ∀ i, IsScalarTower ℤ B (S i) := fun i =>
    IsScalarTower.of_algebraMap_eq' (Subsingleton.elim _ _)
  let : ∀ i, Algebra.FiniteType ℤ (S i) := fun i => Algebra.FiniteType.trans
    (inferInstance : Algebra.FiniteType ℤ B) (inferInstance : Algebra.FiniteType B (S i))
  obtain ⟨R₀, hR₀, hAlg, e, he, hxe⟩ :=
    exists_affineSpec_chart_of_fieldPoint Ω (x ≫ σ)
  let : CommRing R₀ := hR₀
  let : Algebra R₀ Ω := hAlg
  let : IsOpenImmersion e := he
  have hpoint : (Spec.algebraMap R₀ Ω ≫ e) (IsLocalRing.closedPoint Ω) ∈ Set.range σ := by
    rw [hxe]
    exact ⟨x (IsLocalRing.closedPoint Ω), rfl⟩
  have hsquare (i : minimalPrimes B) : (r i).comp (s i) = (t i).comp f :=
    RingHom.MinimalPrimeNormalization.componentMap_sourceMap f i
  have hgfinite : IsFinite (Sigma.desc (fun i => Spec.map (CommRingCat.ofHom (t i)))) :=
    MinimalPrimeNormalizationArrow.coefficientCover_isFinite hB
  have hgsurj : Surjective (Sigma.desc (fun i => Spec.map (CommRingCat.ofHom (t i)))) :=
    MinimalPrimeNormalizationArrow.coefficientCover_surjective hB
  obtain ⟨V, hV⟩ := exists_arithmetic_normal_array_affine_stage_degree_zero_of_lower_rank
    (ι := minimalPrimes B)
    k hk houter d ih A B R S (fun i => (hS i).2.2.2.2.trans hd)
    r
    s t (fun i => RingHom.MinimalPrimeNormalization.sourceMap_finite f hA i)
    p σ hσ haff f
    hsquare a b H hgfinite hgsurj
    n hn hunit I c R₀ Ω e hpoint
  let v : Spec (CommRingCat.of V.algebra) ⟶ Spec (CommRingCat.of R₀) :=
    (etaleObject R₀ Ω V).hom
  let : Etale v := (etaleObject R₀ Ω V).prop
  let U : X.Etale := Scheme.Etale.mk (v ≫ e)
  let xU : Spec (CommRingCat.of Ω) ⟶ U.left :=
    Spec.map (CommRingCat.ofHom V.point.toRingHom)
  refine ⟨U, xU, ?_, hV⟩
  change Spec.map (CommRingCat.ofHom V.point.toRingHom) ≫ (v ≫ e) = _
  exact (Category.assoc (Spec.map (CommRingCat.ofHom V.point.toRingHom)) v e).symm.trans
    ((congrArg (fun k : Spec (CommRingCat.of Ω) ⟶ Spec (CommRingCat.of R₀) => k ≫ e)
      (stagePoint_over R₀ Ω V)).trans hxe)

/-- At the fixed higher degree, close the full coefficient-rank induction.
Only strictly smaller cohomological degrees remain outer assumptions. -/
theorem arithmeticPointedCurveModuleEffacement_of_lower_degrees
    (k : ℕ) (hk : 2 ≤ k)
    (houter : ∀ r : ℕ, 1 ≤ r → r < k → ArithmeticCurveModuleInjectiveVanishing.{u} r)
    (d : ℕ) : ArithmeticPointedCurveModuleEffacement.{u} k d := by
  induction d using Nat.strong_induction_on with
  | h d ih =>
    intro R S hR hS hftR hftS hd G Y p hp hgc hqc hqs σ hσ haff β a b H
      n hn hunit I hI c Ω hΩ hSep x
    let f : R →+* S := (Spec.preimage β).hom
    have hf : Spec.map (CommRingCat.ofHom f) = β := Spec.map_preimage β
    have Hf : IsPullback a b p (Spec.map (CommRingCat.ofHom f)) := hf.symm ▸ H
    exact exists_arithmetic_arrow_pointed_degree_zero_of_lower_rank k hk houter d ih
      R S f hd p σ hσ haff a b Hf n hn hunit I c Ω x

end AlgebraicGeometry.Scheme.EtaleCohomology
