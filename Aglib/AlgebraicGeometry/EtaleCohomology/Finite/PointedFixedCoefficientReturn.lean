/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.EtaleCohomology.Finite.PointedCoefficientRefinementZero
public import Aglib.AlgebraicGeometry.EtaleCohomology.Localization.FinitePrincipalClosedResidual
public import Aglib.AlgebraicGeometry.EtaleCohomology.Localization.ClosedCoefficientRefinement

/-! # A fixed genuine finite coefficient through pointed target refinement

Choose the genuine upstairs injective and its actual coefficient adjunct once.
The class transformed by this same arrow is then used by generic spreading,
closed residual detection and later pointed chart refinement. Its actual
restriction-zero transports through canonical coefficient-square coherence.
The original finite detector, with the same upstairs injective and adjunct,
returns the original target-refined class zero.

No geometric-pullback zero of the original class is substituted for transformed
class zero. No arbitrary inverse image of an injective is assumed injective.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite

namespace AlgebraicGeometry.Scheme.EtaleCohomology.Finite

open Coefficients GeometricNeighborhood

universe u eY

attribute [local instance] hasSheafifyLarge hasSheafifyModules HasExt.standard

/-- The same original finite detector returns zero after a whole target-stage
factorization, consuming restriction-zero of its fixed transformed class. -/
theorem coefficientRefinement_zero_of_fixed_class_zero
    {B B' X X' Y H U : Scheme.{u}}
    [HasExt.{eY} (AbelianSheaf.{u, u + 1} Y)]
    (g : B' ⟶ B) (b : Y ⟶ B) (a : Y ⟶ X) (t : H ⟶ X)
    (f : X' ⟶ X) (p : pullback g b ⟶ X')
    (hp : p ≫ f = pullback.snd g b ≫ a)
    (u : U ⟶ X') (v : pullback t f ⟶ U) (hv : v ≫ u = pullback.snd t f)
    (Λ : Type (u + 1)) [Ring Λ] (I : ModuleSheaf B Λ) (J : ModuleSheaf B' Λ)
    (α : (moduleInverseImage g Λ).obj I ⟶ J)
    (hdetect : ∀ {Y₀ Y₁ : Scheme.{u}}
      (k : Y₁ ⟶ Y₀) (b₀ : Y₀ ⟶ B) (b₁ : Y₁ ⟶ B')
      (h : IsPullback b₁ k g b₀) (q : ℕ)
      (d : Sheaf.H.{u + 2} ((inverseImage b₀).obj
        ((SheafOfModules.toSheaf (constantRing B Λ)).obj I)) q),
      Sheaf.H.map (moduleClosedPullbackCoefficientMap g k b₀ b₁ h.w.symm
        Λ I J α) q (cohomologyPullback.{u, u + 2, u + 2} k _ q d) = 0 → d = 0)
    (q : ℕ) (c : Sheaf.H.{eY} ((inverseImage b).obj
      ((SheafOfModules.toSheaf (constantRing B Λ)).obj I)) q)
    (hc : cohomologyPullback.{u, u + 2, u + 2} (pullback.snd u p) _ q
      (moduleFiniteImageClass.{u, eY, u + 2} g (pullback.snd g b) b (pullback.fst g b)
        (pullback.condition (f := g) (g := b)).symm Λ I J α q c) = 0) :
    cohomologyPullback.{u, eY, u + 2} (X := Y) (S := pullback t a)
      (pullback.snd t a) _ q c = 0 := by
  let r := pullback.coefficientRefinementOriginal g b a t
  let k := pullback.snd g (pullback.snd t a ≫ b)
  have hK : IsPullback (r ≫ pullback.fst g b) k g (pullback.snd t a ≫ b) := by
    dsimp only [r, k]
    rw [pullback.coefficientRefinementOriginal_fst]
    exact IsPullback.of_hasPullback _ _
  have ht : k ≫ pullback.snd t a = r ≫ pullback.snd g b :=
    (pullback.coefficientRefinementOriginal_snd g b a t).symm
  let F := (SheafOfModules.toSheaf (constantRing B Λ)).obj I
  let cU : Sheaf.H.{u + 2} ((inverseImage (pullback.snd t a ≫ b)).obj F) q :=
    Sheaf.H.map ((inverseImageComp b (pullback.snd t a)).inv.app F) q
      (cohomologyPullback.{u, eY, u + 2} (pullback.snd t a) _ q c)
  have hold : cohomologyPullback.{u, u + 2, u + 2} r _ q
      (moduleFiniteImageClass.{u, eY, u + 2} g (pullback.snd g b) b (pullback.fst g b)
        (pullback.condition (f := g) (g := b)).symm Λ I J α q c) = 0 :=
    TwoFieldEffacement.original_class_zero_of_map_law
      (pullback.coefficientRefinementFactor g b a t f p hp u v hv)
      (pullback.snd u p) r
      (pullback.coefficientRefinementFactor_family g b a t f p hp u v hv) _ q _ hc
  have hnew : Sheaf.H.map
      (moduleClosedPullbackCoefficientMap g k (pullback.snd t a ≫ b)
        (r ≫ pullback.fst g b) hK.w.symm Λ I J α) q
      (cohomologyPullback.{u, u + 2, u + 2} k _ q cU) = 0 :=
    (moduleClosedPullbackCoefficientClass_refinement_eq_zero_iff
      g (pullback.snd g b) k b (pullback.fst g b) (pullback.snd t a) r
      (pullback.condition (f := g) (g := b)).symm ht hK.w.symm Λ I J α q c).mpr hold
  have hzero : cU = 0 := hdetect k (pullback.snd t a ≫ b)
    (r ≫ pullback.fst g b) hK q cU hnew
  apply Sheaf.H.map_injective_of_isIso
    ((inverseImageComp b (pullback.snd t a)).inv.app F) q
  exact hzero.trans (map_zero _).symm

/-- The original full pointed-stage construction for an already chosen
upstairs coefficient and its already proved finite detector. All subsequent
chart restrictions concern this same literal transformed class. -/
theorem exists_pointed_stage_zero_of_fixed_coefficient
    (R Ω S A : Type u) [CommRing R] [Field Ω] [Algebra R Ω]
    [CommRing S] [HenselianLocalRing S] [CommRing A]
    [Algebra S A] [Module.Finite S A]
    {X B B' Y : Scheme.{u}}
    (f : X ⟶ Spec (.of R)) [QuasiCompact f] [QuasiSeparated f]
    (E : Spec (.of A) ≅ (baseChangedCone R Ω f).pt.left)
    (g : B' ⟶ B) (b : Y ⟶ B) (a : Y ⟶ Spec (.of R))
    (p : pullback g b ⟶ X) (hp : p ≫ f = pullback.snd g b ≫ a)
    [HasExt.{eY} (AbelianSheaf.{u, u + 1} Y)]
    (Λ : Type (u + 1)) [Ring Λ] (I : ModuleSheaf B Λ) (J : ModuleSheaf B' Λ)
    (α : (moduleInverseImage g Λ).obj I ⟶ J)
    (hdetect : ∀ {Y₀ Y₁ : Scheme.{u}}
      (k : Y₁ ⟶ Y₀) (b₀ : Y₀ ⟶ B) (b₁ : Y₁ ⟶ B')
      (h : IsPullback b₁ k g b₀) (q : ℕ)
      (d : Sheaf.H.{u + 2} ((inverseImage b₀).obj
        ((SheafOfModules.toSheaf (constantRing B Λ)).obj I)) q),
      Sheaf.H.map (moduleClosedPullbackCoefficientMap g k b₀ b₁ h.w.symm
        Λ I J α) q (cohomologyPullback.{u, u + 2, u + 2} k _ q d) = 0 → d = 0)
    (U : MaximalSpectrum A → X.Etale)
    (m : ∀ i : MaximalSpectrum A,
      Spec (.of (IsLocalRing.ResidueField (Localization.AtPrime i.asIdeal))) ⟶ (U i).left)
    (hm : ∀ i : MaximalSpectrum A, m i ≫ (U i).hom =
      localComponentResidueMap A i ≫ localComponentInclusion A i ≫
        E.hom ≫ (baseChangedCone R Ω f).pt.hom)
    (q : ℕ) (c : Sheaf.H.{eY} ((inverseImage b).obj
      ((SheafOfModules.toSheaf (constantRing B Λ)).obj I)) q)
    (hc : ∀ i : MaximalSpectrum A,
      cohomologyPullback.{u, u + 2, u + 2} (pullback.snd (U i).hom p) _ q
        (moduleFiniteImageClass.{u, eY, u + 2} g (pullback.snd g b) b (pullback.fst g b)
          (pullback.condition (f := g) (g := b)).symm Λ I J α q c) = 0) :
    ∃ (V : GeometricEtaleNeighborhood R Ω)
      (v : (baseChangedDiagram R Ω f).obj (op V) ⟶ Over.mk (coproductEtale U).hom),
      (∀ i : MaximalSpectrum A,
        (localComponentResidueMap A i ≫ localComponentInclusion A i ≫ E.hom ≫
          ((baseChangedCone R Ω f).π.app (op V)).left) ≫ v.left =
            m i ≫ Sigma.ι (fun i => (U i).left) i) ∧
      cohomologyPullback.{u, eY, u + 2} (X := Y)
        (S := pullback (Spec.algebraMap R V.algebra) a)
        (pullback.snd (Spec.algebraMap R V.algebra) a) _ q c = 0 := by
  let : Finite (MaximalSpectrum A) := Module.finiteAlgebra_maximalSpectrum_finite S A
  have hwhole := finiteCoproductPullback_cohomologyPullback_eq_zero
    (fun i => (U i).left) (fun i => (U i).hom) p _ q
    (moduleFiniteImageClass.{u, eY, u + 2} g (pullback.snd g b) b (pullback.fst g b)
      (pullback.condition (f := g) (g := b)).symm Λ I J α q c) hc
  obtain ⟨V, v, hmarks, _⟩ := exists_finite_pointed_stage_lift R Ω S A f E U m hm
  refine ⟨V, v, hmarks, ?_⟩
  exact coefficientRefinement_zero_of_fixed_class_zero
    g b a (Spec.algebraMap R V.algebra) f p hp
    (coproductEtale U).hom v.left (Over.w v) Λ I J α hdetect q c hwhole

/-- Fix the genuine upstairs injective and coefficient adjunct before any
chart, residue mark, class or later target stage is selected. Once actual
chart-family zeros of that fixed transformed class are produced, the whole
pointed stage construction returns zero for the unchanged original class. -/
theorem exists_fixed_coefficient_pointed_return
    (R Ω S A : Type u) [CommRing R] [Field Ω] [Algebra R Ω]
    [CommRing S] [HenselianLocalRing S] [CommRing A]
    [Algebra S A] [Module.Finite S A]
    {X B B' Y : Scheme.{u}}
    (f : X ⟶ Spec (.of R)) [QuasiCompact f] [QuasiSeparated f]
    (E : Spec (.of A) ≅ (baseChangedCone R Ω f).pt.left)
    (g : B' ⟶ B) [IsFinite g] [Surjective g]
    (b : Y ⟶ B) (a : Y ⟶ Spec (.of R))
    (p : pullback g b ⟶ X) (hp : p ≫ f = pullback.snd g b ≫ a)
    [HasExt.{eY} (AbelianSheaf.{u, u + 1} Y)]
    (Λ : Type (u + 1)) [Ring Λ] (I : ModuleSheaf B Λ) [Injective I] :
    ∃ J : ModuleSheaf B' Λ, Injective J ∧
      ∃ α : (moduleInverseImage g Λ).obj I ⟶ J,
        ∀ (U : MaximalSpectrum A → X.Etale)
          (m : ∀ i : MaximalSpectrum A,
            Spec (.of (IsLocalRing.ResidueField (Localization.AtPrime i.asIdeal))) ⟶ (U i).left)
          (_hm : ∀ i : MaximalSpectrum A, m i ≫ (U i).hom =
            localComponentResidueMap A i ≫ localComponentInclusion A i ≫
              E.hom ≫ (baseChangedCone R Ω f).pt.hom)
          (q : ℕ) (c : Sheaf.H.{eY} ((inverseImage b).obj
            ((SheafOfModules.toSheaf (constantRing B Λ)).obj I)) q),
          (∀ i : MaximalSpectrum A,
            cohomologyPullback.{u, u + 2, u + 2} (pullback.snd (U i).hom p) _ q
              (moduleFiniteImageClass.{u, eY, u + 2} g (pullback.snd g b) b (pullback.fst g b)
                (pullback.condition (f := g) (g := b)).symm Λ I J α q c) = 0) →
          ∃ (V : GeometricEtaleNeighborhood R Ω)
            (v : (baseChangedDiagram R Ω f).obj (op V) ⟶ Over.mk (coproductEtale U).hom),
            (∀ i : MaximalSpectrum A,
              (localComponentResidueMap A i ≫ localComponentInclusion A i ≫ E.hom ≫
                ((baseChangedCone R Ω f).π.app (op V)).left) ≫ v.left =
                  m i ≫ Sigma.ι (fun i => (U i).left) i) ∧
            cohomologyPullback.{u, eY, u + 2} (X := Y)
              (S := pullback (Spec.algebraMap R V.algebra) a)
              (pullback.snd (Spec.algebraMap R V.algebra) a) _ q c = 0 := by
  obtain ⟨J, hJ, α, hdetect⟩ :=
    exists_moduleInjective_finite_refinement_detector.{u, u + 2, u + 2} g Λ I
  refine ⟨J, hJ, α, ?_⟩
  intro U m hm q c hc
  exact exists_pointed_stage_zero_of_fixed_coefficient R Ω S A f E g b a p hp Λ I J α
    (fun k b₀ b₁ h q d hd => hdetect k b₀ b₁ h q d hd) U m hm q c hc

end AlgebraicGeometry.Scheme.EtaleCohomology.Finite
