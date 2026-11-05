/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.EtaleCohomology.SupportInduction.AffinePointedPrincipalStep
public import Aglib.AlgebraicGeometry.EtaleCohomology.Fields.TwoFieldEffacement.NormalCoefficientFamilySquare
public import Aglib.AlgebraicGeometry.EtaleCohomology.Continuity.StagePrincipalPullbackFactorZero
public import Aglib.AlgebraicGeometry.Morphisms.Smooth.FiniteEtaleSectionComponent

/-! # Whole normal marked covers supply the actual support-induction step

The original generic producer supplies a finite etale cover with a whole
section and coefficient-stage open zero. This theorem selects its true
section component, transports that same open zero through the original
normal-family comparison, invokes lower-rank induction and returns the
original target-stage class with the supplied fixed coefficient detector.
The cover is not assumed geometrically connected over the normal source.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits
open IsLocalization.PrincipalDiagram
open scoped nonZeroDivisors

namespace AlgebraicGeometry.Scheme.EtaleCohomology

open Coefficients _root_.AlgebraicGeometry.Scheme.EtaleCohomology.Finite
  _root_.AlgebraicGeometry.Scheme.EtaleCohomology.Finite.GeometricNeighborhood
  TwoFieldEffacement
open PrincipalNeighborhoodLimit

universe u eY

attribute [local instance] hasSheafifyLarge hasSheafifyModules HasExt.standard

/-- A genuine whole-cover coefficient-open zero is enough for the complete
pointed support-induction step. The section component, all field fibres,
Cartesian family maps and all residue marks are constructed internally.
The original coefficient, adjunct and finite detector are unchanged. -/
theorem exists_affine_stage_zero_of_whole_normal_open_lower_rank
    (d : ℕ) (ih : ∀ q < d, PointedCurveModuleInjectiveH1Effacement.{u} q)
    (R₀ Ω A B R S : Type u) [CommRing R₀] [Field Ω] [Algebra R₀ Ω] [IsSepClosed Ω]
    [CommRing A] [CommRing B] [CommRing R] [CommRing S] [IsDomain S]
    (hR : IsNagataRing.{u, 0} R) (hS : IsNagataRing.{u, 0} S)
    (hd : ringKrullDim S ≤ (d : ℕ))
    {X G : Scheme.{u}} (p : X ⟶ Spec (CommRingCat.of A))
    [SmoothOfRelativeDimension 1 p] [QuasiCompact p] [QuasiSeparated p]
    (σ : Spec (CommRingCat.of A) ⟶ X) (hσ : σ ≫ p = 𝟙 _)
    (haff : ∀ (F : Type u) [Field F]
      (z : Spec (CommRingCat.of F) ⟶ Spec (CommRingCat.of A)),
      IsAffine (pullback p z : Scheme.{u}))
    (r : Spec (CommRingCat.of R) ⟶ Spec (CommRingCat.of A)) [IsFinite r]
    (b : Spec (CommRingCat.of B) ⟶ Spec (CommRingCat.of A))
    (g : Spec (CommRingCat.of S) ⟶ Spec (CommRingCat.of B))
    (β : Spec (CommRingCat.of S) ⟶ Spec (CommRingCat.of R)) (hβ : β ≫ r = g ≫ b)
    (e : Spec (CommRingCat.of R₀) ⟶ X)
    (hpoint : (Spec.algebraMap R₀ Ω ≫ e) (IsLocalRing.closedPoint Ω) ∈ Set.range σ)
    (k : G ⟶ pullback p r) [Etale k] [IsFinite k]
    (ρ : Spec (CommRingCat.of R) ⟶ G)
    (hρ : ρ ≫ k = pullback.sectionMap p r σ hσ)
    (n : ℕ) (hn : 0 < n) (hunit : IsUnit (n : R))
    (I : ModuleSheaf (Spec (CommRingCat.of B)) (ULift.{u + 1} (ZMod n)))
    (J : ModuleSheaf (Spec (CommRingCat.of S)) (ULift.{u + 1} (ZMod n))) [Injective J]
    (α : (moduleInverseImage g (ULift.{u + 1} (ZMod n))).obj I ⟶ J)
    (hdetect : ∀ {Y₀ Y₁ : Scheme.{u}}
      (l : Y₁ ⟶ Y₀) (b₀ : Y₀ ⟶ Spec (CommRingCat.of B))
      (b₁ : Y₁ ⟶ Spec (CommRingCat.of S)) (H₀ : IsPullback b₁ l g b₀) (q : ℕ)
      (d₀ : Sheaf.H.{u + 2} ((inverseImage b₀).obj
        ((SheafOfModules.toSheaf (constantRing (Spec (CommRingCat.of B))
          (ULift.{u + 1} (ZMod n)))).obj I)) q),
      Sheaf.H.map (moduleClosedPullbackCoefficientMap g l b₀ b₁ H₀.w.symm
        (ULift.{u + 1} (ZMod n)) I J α) q
          (cohomologyPullback.{u, u + 2, u + 2} l _ q d₀) = 0 → d₀ = 0)
    [HasExt.{eY} (AbelianSheaf.{u, u + 1} (pullback p b))]
    (c : Sheaf.H.{eY} ((inverseImage (pullback.snd p b)).obj
      ((SheafOfModules.toSheaf (constantRing (Spec (CommRingCat.of B))
        (ULift.{u + 1} (ZMod n)))).obj I)) 1)
    (t : Finset S⁰) (ht : denominator S⁰ t ≠ 0)
    (hopen : cohomologyPullback.{u, eY, u + 2}
      ((stageSourceOpen S⁰
          (pullback.snd k (pullback.fst (pullback.snd p r) β) ≫
            pullback.snd (pullback.snd p r) β) t).ι ≫
        pullback.snd k (pullback.fst (pullback.snd p r) β) ≫
          normalizedFamilyMap p r b g β hβ) _ 1 c = 0) :
    ∃ V : GeometricEtaleNeighborhood R₀ Ω,
      cohomologyPullback.{u, eY, u + 2}
        (pullback.snd (Spec.algebraMap R₀ V.algebra ≫ e) (pullback.fst p b)) _ 1 c = 0 := by
  let : IsNoetherianRing R := hR.isNoetherianRing
  let : MorphismProperty.IsStableUnderBaseChange (@SmoothOfRelativeDimension.{u} 1) :=
    smoothOfRelativeDimension_isStableUnderBaseChange 1
  let : SmoothOfRelativeDimension 1 (pullback.snd p r) :=
    MorphismProperty.of_isPullback (P := @SmoothOfRelativeDimension.{u} 1)
      (IsPullback.of_hasPullback p r) (inferInstance : SmoothOfRelativeDimension 1 p)
  have haffR (F : Type u) [Field F]
      (z : Spec (CommRingCat.of F) ⟶ Spec (CommRingCat.of R)) :
      IsAffine (pullback (pullback.snd p r) z : Scheme.{u}) := by
    let : IsAffine (pullback p (z ≫ r) : Scheme.{u}) := haff F (z ≫ r)
    exact IsAffine.of_isIso (pullbackLeftPullbackSndIso p r z).hom
  have hρp : ρ ≫ (k ≫ pullback.snd p r) = 𝟙 _ := by
    rw [← Category.assoc, hρ]
    exact pullback.sectionMap_snd p r σ hσ
  obtain ⟨W, τ, _hW, hτ, hτp, hsm, hqc, hqs, hgc, hWaff⟩ :=
    exists_finiteEtale_sectionComponent_affine_fibers R (pullback.snd p r) 1 k ρ hρp haffR
  let kW := W.ι ≫ k
  let pW := kW ≫ pullback.snd p r
  let : SmoothOfRelativeDimension 1 pW := by
    simpa only [pW, kW, Category.assoc] using hsm
  let : QuasiCompact pW := by simpa only [pW, kW, Category.assoc] using hqc
  let : QuasiSeparated pW := by simpa only [pW, kW, Category.assoc] using hqs
  let : GeometricallyConnected pW := by simpa only [pW, kW, Category.assoc] using hgc
  have hτW : τ ≫ pW = 𝟙 _ := by
    simpa only [pW, kW, Category.assoc] using hτp
  have hτk : τ ≫ kW = pullback.sectionMap p r σ hσ := by
    dsimp only [kW]
    rw [← Category.assoc, hτ, hρ]
  have haffW (F : Type u) [Field F]
      (z : Spec (CommRingCat.of F) ⟶ Spec (CommRingCat.of R)) :
      IsAffine (pullback pW z : Scheme.{u}) := by
    simpa only [pW, kW, Category.assoc] using hWaff F z
  let v := normalCoefficientFamilyMap p r b g β hβ
  let l := normalCoefficientCoverMap p r b g β hβ k W.ι
  let bC := pullback.snd k (pullback.fst (pullback.snd p r) β) ≫
    pullback.snd (pullback.snd p r) β
  let hC := pullback.snd k (pullback.fst (pullback.snd p r) β) ≫
    normalizedFamilyMap p r b g β hβ
  have hlb : l ≫ bC = pullback.snd kW v ≫ pullback.fst g (pullback.snd p b) :=
    normalCoefficientCoverMap_coefficient p r b g β hβ k W.ι
  have hlh : l ≫ hC = pullback.snd kW v ≫ pullback.snd g (pullback.snd p b) :=
    normalCoefficientCoverMap_original p r b g β hβ k W.ι
  have hopenW : cohomologyPullback.{u, eY, u + 2}
      ((pullback.snd (principalSupportOpen S (denominator S⁰ t)).ι
          (pullback.snd kW v ≫ pullback.fst g (pullback.snd p b)) ≫
        pullback.snd kW v) ≫ pullback.snd g (pullback.snd p b)) _ 1 c = 0 := by
    exact Continuity.principalPullback_factor_zero_of_stageOpen_zero
      S⁰ t bC hC _ 1 c l
      (pullback.snd kW v ≫ pullback.fst g (pullback.snd p b))
      (pullback.snd kW v) (pullback.snd g (pullback.snd p b)) hlb hlh hopen
  exact exists_affine_stage_zero_of_principalOpen_lower_rank
    d ih R₀ Ω A R S hR hS hd p σ hσ r e hpoint pW τ hτW haffW kW hτk β g
    (pullback.snd p b) (pullback.fst p b) v
    (normalCoefficientFamilyMap_source p r b g β hβ)
    (normalCoefficientCoverMap_isPullback p r b g β hβ k W.ι)
    n hn hunit I J α hdetect c (denominator S⁰ t) ht hopenW

end AlgebraicGeometry.Scheme.EtaleCohomology
