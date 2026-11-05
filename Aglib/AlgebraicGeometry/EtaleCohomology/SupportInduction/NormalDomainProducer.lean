/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import
  Aglib.AlgebraicGeometry.EtaleCohomology.SupportInduction.NormalDomainSelectedProducer

/-! # Actual normal-domain pointed effacement from smaller coefficient rank

The generic producer is invoked on the original bounded class, without a
zero premise. Its actual two fields, literal finite normal models, whole
marked cover and coefficient-open zero feed the support-induction step.
Only after these models have been produced is one genuine coefficient and
its original detector chosen. The same coefficient is used on every later
chart. The induction hypothesis remains the full Nagata-ring property, so
the nonnormal principal quotient belongs to its actual scope.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits CategoryTheory.PreGaloisCategory
open AlgebraicGeometry.Scheme.FiniteEtale

namespace AlgebraicGeometry.Scheme.EtaleCohomology

open Coefficients _root_.AlgebraicGeometry.Scheme.EtaleCohomology.Finite
  _root_.AlgebraicGeometry.Scheme.EtaleCohomology.Finite.GeometricNeighborhood
  TwoFieldEffacement

universe u eY

attribute [local instance] hasSheafifyLarge hasSheafifyModules HasExt.standard

/-- The original class over normal source and coefficient domains has an
actual pointed zero stage, using the full smaller-rank property only on the
strictly smaller closed residual. No generic, open or local zero is assumed.
The chosen compatible fraction fields are retained throughout the proof. -/
theorem exists_normal_domain_affine_stage_H1_zero_of_lower_rank
    (d : ℕ) (ih : ∀ q < d, PointedCurveModuleInjectiveH1Effacement.{u} q)
    (A B k K R₀ Ω : Type u)
    [CommRing A] [IsDomain A] [IsIntegrallyClosed A]
    [CommRing B] [IsDomain B] [IsIntegrallyClosed B]
    [Field k] [Field K] [CommRing R₀] [Field Ω] [Algebra R₀ Ω] [IsSepClosed Ω]
    [Algebra A B] [Algebra A k] [IsFractionRing A k]
    [Algebra A K] [Algebra B K] [IsFractionRing B K] [Algebra k K]
    [IsScalarTower A B K] [IsScalarTower A k K]
    (hA : IsNagataRing.{u, 0} A) (hB : IsNagataRing.{u, 0} B)
    (hd : ringKrullDim B ≤ (d : ℕ))
    {X : Scheme.{u}} (p : X ⟶ Spec (CommRingCat.of A))
    [SmoothOfRelativeDimension 1 p] [GeometricallyConnected p]
    [QuasiCompact p] [QuasiSeparated p]
    (σ : Spec (CommRingCat.of A) ⟶ X) (hσ : σ ≫ p = 𝟙 _)
    (haff : ∀ (F : Type u) [Field F]
      (z : Spec (CommRingCat.of F) ⟶ Spec (CommRingCat.of A)),
      IsAffine (pullback p z : Scheme.{u}))
    (e : Spec (CommRingCat.of R₀) ⟶ X)
    (hpoint : (Spec.algebraMap R₀ Ω ≫ e) (IsLocalRing.closedPoint Ω) ∈ Set.range σ)
    (n : ℕ) (hn : 0 < n) (hunit : IsUnit (n : A))
    (I : ModuleSheaf (Spec (CommRingCat.of B)) (ULift.{u + 1} (ZMod n))) [Injective I]
    [HasExt.{eY} (AbelianSheaf.{u, u + 1} (pullback p (Spec.algebraMap A B)))]
    (c : Sheaf.H.{eY} ((inverseImage (pullback.snd p (Spec.algebraMap A B))).obj
      ((SheafOfModules.toSheaf (constantRing (Spec (CommRingCat.of B))
        (ULift.{u + 1} (ZMod n)))).obj I)) 1) :
    ∃ V : GeometricEtaleNeighborhood R₀ Ω,
      cohomologyPullback.{u, eY, u + 2}
        (pullback.snd (Spec.algebraMap R₀ V.algebra ≫ e)
          (pullback.fst p (Spec.algebraMap A B))) _ 1 c = 0 := by
  let : IsNoetherianRing A := hA.isNoetherianRing
  let : IsNoetherianRing B := hB.isNoetherianRing
  let : IsAffine (pullback p (Spec.algebraMap A k) : Scheme.{u}) :=
    haff k (Spec.algebraMap A k)
  let M := (SheafOfModules.toSheaf (constantRing (Spec (CommRingCat.of B))
    (ULift.{u + 1} (ZMod n)))).obj I
  have hM : n • 𝟙 M = 0 := Functor.map_nsmul_id_eq_zero
    (SheafOfModules.toSheaf (constantRing (Spec (CommRingCat.of B))
      (ULift.{u + 1} (ZMod n)))) I n
    (ModuleCat.Sheaf.ConstantRing.uLiftZMod_nsmul_id_eq_zero
      (Scheme.smallEtaleTopology (Spec (CommRingCat.of B))) n I)
  obtain ⟨L, C, hC, hCF, _hkill, Hstage⟩ :=
    exists_generic_H1_normal_whole_coefficient_open A B k K p σ hσ M n hn hM hunit c
  let : AddCommGroup C := hC
  let : Finite C := hCF
  let : Algebra k L := ((algebraMap K L).comp (algebraMap k K)).toAlgebra
  let : IsScalarTower k K L := IsScalarTower.of_algebraMap_eq' rfl
  obtain ⟨F, E, hFieldE, hLE, Hfields⟩ := Hstage
  let : Field E := hFieldE
  let : Algebra L E := hLE
  let : Algebra k E := ((algebraMap L E).comp (algebraMap k L)).toAlgebra
  let : IsScalarTower k L E := IsScalarTower.of_algebraMap_eq' rfl
  obtain ⟨hfinF, hfinE, _jE, a, _ha, Z, _hG, _hcard, z, Hnormal⟩ := Hfields
  let : Module.Finite k F := hfinF
  let : Module.Finite L E := hfinE
  exact exists_normal_domain_affine_stage_H1_zero_of_generic_whole_open
    d ih A B k K R₀ Ω hA hB hd p σ hσ haff e hpoint n hn hunit I c L F E a Z z Hnormal

end AlgebraicGeometry.Scheme.EtaleCohomology
