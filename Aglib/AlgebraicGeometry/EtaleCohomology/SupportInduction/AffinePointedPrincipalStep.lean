/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.EtaleCohomology.SupportInduction.PrincipalOpenClassRefinement
public import Aglib.AlgebraicGeometry.EtaleCohomology.Finite.AffineFixedCoefficientStageReturn
public import Aglib.AlgebraicGeometry.EtaleCohomology.Finite.AffineChartWholeSectionResidueMarks
public import Aglib.AlgebraicGeometry.EtaleCohomology.Localization.ClosedChartZeroTransport
public import Aglib.RingTheory.Henselian.StrictHenselization.FiniteLocalFactors

/-! # Whole-curve support induction with one fixed coefficient and affine return

The original whole source family and section are retained during induction.
All residue marks are produced from the actual finite source and the single
original target point. Only the final target stage is restricted to its given
affine chart. The chosen genuine coefficient, adjunct and detector are inputs
and are never reselected. Principal-open vanishing is the actual existing
open branch; every whole chart zero is produced by lower-rank induction.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite

namespace AlgebraicGeometry.Scheme.EtaleCohomology

open Coefficients _root_.AlgebraicGeometry.Scheme.EtaleCohomology.Finite
  _root_.AlgebraicGeometry.Scheme.EtaleCohomology.Finite.GeometricNeighborhood

universe u eY

attribute [local instance] hasSheafifyLarge hasSheafifyModules HasExt.standard

/-- Apply genuine smaller-rank induction on the entire section component,
then return the original class on an affine target stage with the unchanged
coefficient detector. Canonical finite-model residue marks are constructed
internally; no local class-zero or residue-mark producer is assumed. -/
theorem exists_affine_stage_zero_of_principalOpen_lower_rank
    (d : ℕ) (ih : ∀ r < d, PointedCurveModuleInjectiveH1Effacement.{u} r)
    (R₀ Ω A₀ R S : Type u) [CommRing R₀] [Field Ω] [Algebra R₀ Ω] [IsSepClosed Ω]
    [CommRing A₀] [CommRing R] [CommRing S] [IsDomain S]
    (hR : IsNagataRing.{u, 0} R) (hS : IsNagataRing.{u, 0} S)
    (hd : ringKrullDim S ≤ (d : ℕ))
    {X G B Y : Scheme.{u}}
    (p₀ : X ⟶ Spec (CommRingCat.of A₀))
    (σ₀ : Spec (CommRingCat.of A₀) ⟶ X) (hσ₀ : σ₀ ≫ p₀ = 𝟙 _)
    (r : Spec (CommRingCat.of R) ⟶ Spec (CommRingCat.of A₀)) [IsFinite r]
    (e : Spec (CommRingCat.of R₀) ⟶ X)
    (hpoint : (Spec.algebraMap R₀ Ω ≫ e) (IsLocalRing.closedPoint Ω) ∈ Set.range σ₀)
    (p : G ⟶ Spec (CommRingCat.of R))
    [SmoothOfRelativeDimension 1 p] [GeometricallyConnected p]
    [QuasiCompact p] [QuasiSeparated p]
    (σ : Spec (CommRingCat.of R) ⟶ G) (hσ : σ ≫ p = 𝟙 _)
    (haff : ∀ (F : Type u) [Field F]
      (z : Spec (CommRingCat.of F) ⟶ Spec (CommRingCat.of R)),
      IsAffine (pullback p z : Scheme.{u}))
    (k : G ⟶ pullback p₀ r) [Etale k]
    (hσk : σ ≫ k = pullback.sectionMap p₀ r σ₀ hσ₀)
    (β : Spec (CommRingCat.of S) ⟶ Spec (CommRingCat.of R))
    (g : Spec (CommRingCat.of S) ⟶ B)
    (b : Y ⟶ B) (a : Y ⟶ X)
    (v : pullback g b ⟶ pullback p₀ r)
    (hv : v ≫ pullback.fst p₀ r = pullback.snd g b ≫ a)
    (H : IsPullback (pullback.fst k v)
      (pullback.snd k v ≫ pullback.fst g b) p β)
    (n : ℕ) (hn : 0 < n) (hunit : IsUnit (n : R))
    (I : ModuleSheaf B (ULift.{u + 1} (ZMod n)))
    (J : ModuleSheaf (Spec (CommRingCat.of S)) (ULift.{u + 1} (ZMod n))) [Injective J]
    (α : (moduleInverseImage g (ULift.{u + 1} (ZMod n))).obj I ⟶ J)
    (hdetect : ∀ {Y₀ Y₁ : Scheme.{u}}
      (l : Y₁ ⟶ Y₀) (b₀ : Y₀ ⟶ B) (b₁ : Y₁ ⟶ Spec (CommRingCat.of S))
      (H₀ : IsPullback b₁ l g b₀) (q : ℕ)
      (d₀ : Sheaf.H.{u + 2} ((inverseImage b₀).obj
        ((SheafOfModules.toSheaf (constantRing B (ULift.{u + 1} (ZMod n)))).obj I)) q),
      Sheaf.H.map (moduleClosedPullbackCoefficientMap g l b₀ b₁ H₀.w.symm
        (ULift.{u + 1} (ZMod n)) I J α) q
          (cohomologyPullback.{u, u + 2, u + 2} l _ q d₀) = 0 → d₀ = 0)
    [HasExt.{eY} (AbelianSheaf.{u, u + 1} Y)]
    (c : Sheaf.H.{eY} ((inverseImage b).obj
      ((SheafOfModules.toSheaf (constantRing B (ULift.{u + 1} (ZMod n)))).obj I)) 1)
    (s : S) (hs : s ≠ 0)
    (hopen : cohomologyPullback.{u, eY, u + 2}
      ((pullback.snd (principalSupportOpen S s).ι
          (pullback.snd k v ≫ pullback.fst g b) ≫ pullback.snd k v) ≫
        pullback.snd g b) _ 1 c = 0) :
    ∃ V : GeometricEtaleNeighborhood R₀ Ω,
      cohomologyPullback.{u, eY, u + 2}
        (pullback.snd (Spec.algebraMap R₀ V.algebra ≫ e) a) _ 1 c = 0 := by
  classical
  let f := pullback.fst p₀ r
  let fO := pullback.snd f e
  let : IsFinite fO := inferInstanceAs (IsFinite (pullback.snd f e))
  let A := limitSourceRing R₀ Ω fO
  let := limitSourceAlgebra R₀ Ω fO
  let : Module.Finite (GeometricEtaleColimit R₀ Ω) A :=
    limitSource_moduleFinite R₀ Ω fO
  let : ∀ i : MaximalSpectrum A,
      IsSepClosed (IsLocalRing.ResidueField (Localization.AtPrime i.asIdeal)) :=
    fun i => HenselianLocalRing.residueField_isSepClosed_localizationAtPrime
      (GeometricEtaleColimit R₀ Ω) A i.asIdeal
  let x (i : MaximalSpectrum A) :=
    affineChartWholeSectionBasePoint R₀ Ω p₀ r e i
  have hx (i : MaximalSpectrum A) :
      (x i ≫ σ) ≫ k = limitResidueMap R₀ Ω fO i ≫ pullback.fst f e :=
    affineChartWholeSectionBasePoint_lift_over R₀ Ω p₀ r e σ₀ hσ₀
      k σ hσk hpoint i
  let F := (SheafOfModules.toSheaf
    (constantRing (Spec (CommRingCat.of S)) (ULift.{u + 1} (ZMod n)))).obj J
  let cJ := moduleFiniteImageClass.{u, eY, u + 2} g (pullback.snd g b) b
    (pullback.fst g b) (pullback.condition (f := g) (g := b)).symm
    (ULift.{u + 1} (ZMod n)) I J α 1 c
  have hopenJ : cohomologyPullback.{u, u + 2, u + 2}
      (pullback.snd (principalSupportOpen S s).ι
          (pullback.snd k v ≫ pullback.fst g b) ≫ pullback.snd k v) _ 1 cJ = 0 :=
    coefficient_restriction_zero_of_composite_zero (pullback.snd g b)
      (pullback.snd (principalSupportOpen S s).ι
        (pullback.snd k v ≫ pullback.fst g b) ≫ pullback.snd k v) _ _
      (moduleClosedPullbackCoefficientMap g (pullback.snd g b) b (pullback.fst g b)
        (pullback.condition (f := g) (g := b)).symm
        (ULift.{u + 1} (ZMod n)) I J α) 1 c hopen
  have hcharts (i : MaximalSpectrum A) :
      ∃ (U : G.Etale)
        (z : Spec (CommRingCat.of
          (IsLocalRing.ResidueField (Localization.AtPrime i.asIdeal))) ⟶ U.left),
        z ≫ U.hom = x i ≫ σ ∧
        cohomologyPullback.{u, u + 2, u + 2}
          (pullback.snd U.hom (pullback.fst k v) ≫ pullback.snd k v) _ 1 cJ = 0 := by
    exact exists_pointed_principalOpen_composite_H1_zero_of_lower_rank
      d ih R S hR hS hd p σ hσ haff β (pullback.fst k v)
      (pullback.snd k v ≫ pullback.fst g b) H n hn hunit J
      (pullback.snd k v) ((inverseImage (pullback.fst g b)).obj F)
      ((inverseImageComp (pullback.fst g b) (pullback.snd k v)).symm.app F)
      cJ s hs hopenJ
      (IsLocalRing.ResidueField (Localization.AtPrime i.asIdeal)) (x i)
  choose U z hz hzero using hcharts
  let : ∀ i : MaximalSpectrum A, Etale (U i).hom := fun i => (U i).prop
  let U' : MaximalSpectrum A → (pullback p₀ r).Etale :=
    fun i => Scheme.Etale.mk ((U i).hom ≫ k)
  have hmarks (i : MaximalSpectrum A) : z i ≫ (U' i).hom =
      limitResidueMap R₀ Ω fO i ≫ pullback.fst f e := by
    change z i ≫ ((U i).hom ≫ k) = _
    rw [← Category.assoc, hz i]
    exact hx i
  have hchartZero (i : MaximalSpectrum A) :
      cohomologyPullback.{u, u + 2, u + 2}
        (pullback.snd (U' i).hom v) _ 1 cJ = 0 := by
    have H' : IsPullback (pullback.fst (U i).hom (pullback.fst k v))
        (pullback.snd (U i).hom (pullback.fst k v) ≫ pullback.snd k v)
        ((U i).hom ≫ k) v :=
      (IsPullback.of_hasPullback (U i).hom (pullback.fst k v)).paste_vert
        (IsPullback.of_hasPullback k v)
    exact original_class_zero_on_pullback_of_chart _ _ _ _ H' _ 1 cJ (hzero i)
  obtain ⟨V, _w, _hw, _hm, hc⟩ := Finite.exists_affine_stage_zero_of_fixed_coefficient
    R₀ Ω f e g b a v hv (ULift.{u + 1} (ZMod n)) I J α hdetect
    U' z hmarks 1 c hchartZero
  exact ⟨V, hc⟩

end AlgebraicGeometry.Scheme.EtaleCohomology
