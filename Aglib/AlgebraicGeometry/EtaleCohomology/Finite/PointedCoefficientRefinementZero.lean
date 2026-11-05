/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.CategoryTheory.Limits.Shapes.CoefficientRefinementFactorization
public import Aglib.AlgebraicGeometry.EtaleCohomology.Finite.FinitePointedStageLift
public import Aglib.AlgebraicGeometry.EtaleCohomology.Finite.GeometricNeighborhoodFiniteModel
public import Aglib.AlgebraicGeometry.EtaleCohomology.Finite.RelativeCoproductClassZero
public import Aglib.AlgebraicGeometry.EtaleCohomology.Finite.ModuleInjectivePullbackZero

/-! # Original-class zero after pointed target refinement and finite coefficients

First lift the whole finite Henselian source into the genuine coproduct of
its marked etale charts. Its actual target-stage factorization induces a
map from the entire Cartesian coefficient pullback, not just its selected
points. Zero on the chart families therefore gives zero on that full
pullback. The finite detector then returns zero for the unchanged class and
its original injective coefficient on the original coefficient base.

No inverse image of an injective is declared injective. The commuting map
to the finite source is not assumed Cartesian. The existence theorem consumes
actual chart-family zeros and residue marks; it does not generate those zeros
or assume a final target-refined zero.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite

namespace AlgebraicGeometry.Scheme.EtaleCohomology.Finite

open Coefficients GeometricNeighborhood

universe u eY

attribute [local instance] hasSheafifyLarge hasSheafifyModules HasExt.standard

/-- Componentwise zeros of one original target class give zero on the whole
chart-family pullback, without replacing that class by a class on the charts. -/
theorem finiteCoproductPullback_composite_cohomologyPullback_eq_zero
    {X W Y : Scheme.{u}} [HasExt.{eY} (AbelianSheaf.{u, u + 1} Y)]
    {ι : Type u} [Finite ι] (U : ι → Scheme.{u}) (a : ∀ i, U i ⟶ X)
    (p : W ⟶ X) (h : W ⟶ Y)
    (M : AbelianSheaf.{u, u + 1} Y) (q : ℕ) (c : Sheaf.H.{eY} M q)
    (hc : ∀ i, cohomologyPullback.{u, eY, u + 2}
      (pullback.snd (a i) p ≫ h) M q c = 0) :
    cohomologyPullback.{u, eY, u + 2}
      (pullback.snd (Sigma.desc a) p ≫ h) M q c = 0 := by
  have hwhole := sigmaDesc_cohomologyPullback_eq_zero
    (fun i => pullback (a i) p) (fun i => pullback.snd (a i) p ≫ h) M q c hc
  have hdesc : Sigma.desc (fun i => pullback.snd (a i) p ≫ h) =
      Sigma.desc (fun i => pullback.snd (a i) p) ≫ h := by
    apply Sigma.hom_ext
    intro i
    exact (Sigma.ι_comp_desc (fun i => pullback.snd (a i) p ≫ h) i).trans
      (((congrArg (fun f => f ≫ h)
        (Sigma.ι_comp_desc (fun i => pullback.snd (a i) p) i)).symm).trans
          (Category.assoc _ _ _))
  have hmap : (FiniteCoproductPullback.iso U a p).inv ≫
      Sigma.desc (fun i => pullback.snd (a i) p ≫ h) =
        pullback.snd (Sigma.desc a) p ≫ h := by
    rw [hdesc, ← FiniteCoproductPullback.iso_hom_snd U a p]
    simp only [Iso.inv_hom_id_assoc, Category.assoc]
  exact TwoFieldEffacement.original_class_zero_of_map_law
    (FiniteCoproductPullback.iso U a p).inv _ _ hmap M q c hwhole

/-- A factorization of the whole target-stage source gives original-class
zero after removing its genuine finite Cartesian coefficient change. -/
theorem coefficientRefinement_zero_of_chartFamily_zero
    {B B' X X' Y H U : Scheme.{u}}
    [HasExt.{eY} (AbelianSheaf.{u, u + 1} Y)]
    (g : B' ⟶ B) [IsFinite g] [Surjective g]
    (b : Y ⟶ B) (a : Y ⟶ X) (t : H ⟶ X)
    (f : X' ⟶ X) (p : pullback g b ⟶ X')
    (hp : p ≫ f = pullback.snd g b ≫ a)
    (u : U ⟶ X') (v : pullback t f ⟶ U) (hv : v ≫ u = pullback.snd t f)
    (Λ : Type (u + 1)) [Ring Λ] (I : ModuleSheaf B Λ) [Injective I]
    (q : ℕ) (c : Sheaf.H.{eY} ((inverseImage b).obj
      ((SheafOfModules.toSheaf (constantRing B Λ)).obj I)) q)
    (hc : cohomologyPullback.{u, eY, u + 2}
      (pullback.snd u p ≫ pullback.snd g b) _ q c = 0) :
    cohomologyPullback.{u, eY, u + 2} (X := Y) (S := pullback t a)
      (pullback.snd t a) _ q c = 0 := by
  apply moduleInjective_restriction_eq_zero_of_finite_composite_eq_zero
    g b (pullback.snd t a)
    (pullback.snd g (pullback.snd t a ≫ b))
    (pullback.fst g (pullback.snd t a ≫ b)) (IsPullback.of_hasPullback _ _) Λ I q c
  exact TwoFieldEffacement.original_class_zero_of_map_law
    (pullback.coefficientRefinementFactor g b a t f p hp u v hv)
    (pullback.snd u p ≫ pullback.snd g b)
    (pullback.snd g (pullback.snd t a ≫ b) ≫ pullback.snd t a)
    (pullback.coefficientRefinementFactor_original g b a t f p hp u v hv)
    _ q c hc

/-- All actual finite-source residue marks and chart-family zeros construct
one pointed target stage where the original class is zero. The injective
coefficient remains on B throughout the finite return. -/
theorem exists_finite_pointed_coefficient_stage_zero
    (R Ω S A : Type u) [CommRing R] [Field Ω] [Algebra R Ω]
    [CommRing S] [HenselianLocalRing S] [CommRing A]
    [Algebra S A] [Module.Finite S A]
    {X B B' Y : Scheme.{u}}
    (f : X ⟶ Spec (.of R)) [QuasiCompact f] [QuasiSeparated f]
    (E : Spec (.of A) ≅ (baseChangedCone R Ω f).pt.left)
    (U : MaximalSpectrum A → X.Etale)
    (m : ∀ i : MaximalSpectrum A,
      Spec (.of (IsLocalRing.ResidueField (Localization.AtPrime i.asIdeal))) ⟶ (U i).left)
    (hm : ∀ i : MaximalSpectrum A, m i ≫ (U i).hom =
      localComponentResidueMap A i ≫ localComponentInclusion A i ≫
        E.hom ≫ (baseChangedCone R Ω f).pt.hom)
    (g : B' ⟶ B) [IsFinite g] [Surjective g]
    (b : Y ⟶ B) (a : Y ⟶ Spec (.of R))
    (p : pullback g b ⟶ X) (hp : p ≫ f = pullback.snd g b ≫ a)
    [HasExt.{eY} (AbelianSheaf.{u, u + 1} Y)]
    (Λ : Type (u + 1)) [Ring Λ] (I : ModuleSheaf B Λ) [Injective I]
    (q : ℕ) (c : Sheaf.H.{eY} ((inverseImage b).obj
      ((SheafOfModules.toSheaf (constantRing B Λ)).obj I)) q)
    (hc : ∀ i : MaximalSpectrum A,
      cohomologyPullback.{u, eY, u + 2}
        (pullback.snd (U i).hom p ≫ pullback.snd g b) _ q c = 0) :
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
  have hwhole := finiteCoproductPullback_composite_cohomologyPullback_eq_zero
    (fun i => (U i).left) (fun i => (U i).hom) p (pullback.snd g b) _ q c hc
  obtain ⟨V, v, hmarks, _⟩ := exists_finite_pointed_stage_lift R Ω S A f E U m hm
  refine ⟨V, v, hmarks, ?_⟩
  exact coefficientRefinement_zero_of_chartFamily_zero
    g b a (Spec.algebraMap R V.algebra) f p hp
    (coproductEtale U).hom v.left (Over.w v) Λ I q c hwhole

/-- The genuine finite source supplies its own Henselian model and original
reconstruction. Only the actual charts, full residue marks and their family
zeros remain inputs to pointed target-stage production. -/
theorem exists_native_finite_pointed_coefficient_stage_zero
    (R Ω : Type u) [CommRing R] [Field Ω] [Algebra R Ω]
    {X B B' Y : Scheme.{u}} (f : X ⟶ Spec (.of R)) [IsFinite f]
    (U : MaximalSpectrum (limitSourceRing R Ω f) → X.Etale)
    (m : ∀ i : MaximalSpectrum (limitSourceRing R Ω f),
      Spec (.of (IsLocalRing.ResidueField (Localization.AtPrime i.asIdeal))) ⟶ (U i).left)
    (hm : ∀ i : MaximalSpectrum (limitSourceRing R Ω f), m i ≫ (U i).hom =
      localComponentResidueMap (limitSourceRing R Ω f) i ≫
        localComponentInclusion (limitSourceRing R Ω f) i ≫ limitSourceTargetMap R Ω f)
    (g : B' ⟶ B) [IsFinite g] [Surjective g]
    (b : Y ⟶ B) (a : Y ⟶ Spec (.of R))
    (p : pullback g b ⟶ X) (hp : p ≫ f = pullback.snd g b ≫ a)
    [HasExt.{eY} (AbelianSheaf.{u, u + 1} Y)]
    (Λ : Type (u + 1)) [Ring Λ] (I : ModuleSheaf B Λ) [Injective I]
    (q : ℕ) (c : Sheaf.H.{eY} ((inverseImage b).obj
      ((SheafOfModules.toSheaf (constantRing B Λ)).obj I)) q)
    (hc : ∀ i : MaximalSpectrum (limitSourceRing R Ω f),
      cohomologyPullback.{u, eY, u + 2}
        (pullback.snd (U i).hom p ≫ pullback.snd g b) _ q c = 0) :
    ∃ (V : GeometricEtaleNeighborhood R Ω)
      (v : (baseChangedDiagram R Ω f).obj (op V) ⟶ Over.mk (coproductEtale U).hom),
      (∀ i : MaximalSpectrum (limitSourceRing R Ω f),
        (localComponentResidueMap (limitSourceRing R Ω f) i ≫
          localComponentInclusion (limitSourceRing R Ω f) i ≫ (limitSourceIso R Ω f).hom ≫
          ((baseChangedCone R Ω f).π.app (op V)).left) ≫ v.left =
            m i ≫ Sigma.ι (fun i => (U i).left) i) ∧
      cohomologyPullback.{u, eY, u + 2} (X := Y)
        (S := pullback (Spec.algebraMap R V.algebra) a)
        (pullback.snd (Spec.algebraMap R V.algebra) a) _ q c = 0 := by
  let := limitSourceAlgebra R Ω f
  let : Module.Finite (GeometricEtaleColimit R Ω) (limitSourceRing R Ω f) :=
    limitSource_moduleFinite R Ω f
  exact exists_finite_pointed_coefficient_stage_zero
    R Ω (GeometricEtaleColimit R Ω) (limitSourceRing R Ω f) f (limitSourceIso R Ω f)
    U m (by intro i; simpa only [limitSourceTargetMap, Category.assoc] using hm i)
    g b a p hp Λ I q c hc

end AlgebraicGeometry.Scheme.EtaleCohomology.Finite
