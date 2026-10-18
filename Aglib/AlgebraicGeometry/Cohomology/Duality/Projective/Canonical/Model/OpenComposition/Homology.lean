/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.Cohomology.Duality.Projective.Canonical.Model.OpenComposition.Complex
public import Aglib.Algebra.Homology.ShortComplex.MapHomology

/-!
# Composition of the native restricted-model homology comparisons

The actual restriction homology comparisons retain the strict fixed-resolution
composition equation. Naturality of the original global model isomorphism
then supplies the same composition square on native closed-adjoint homology.
-/

@[expose] public section
noncomputable section
set_option autoImplicit false
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry HomologicalComplex

universe u v
namespace AlgebraicGeometry.Scheme.Modules

/-- The standard derived-category model for modules on `Z`, used locally. -/
local instance canonicalModelCompositionHomologyStandardDerived (Z : Scheme.{u}) :
    HasDerivedCategory.{u + 1} Z.Modules := HasDerivedCategory.standard _

section Restriction
variable {V' V P : Scheme.{u}} (j : V ⟶ P) (k : V' ⟶ V)
  [IsOpenImmersion j] [IsOpenImmersion k]

/-- The original direct restriction comparison retains both native homology comparisons. -/
theorem canonicalRestrictionCompComplexIso_homology {ι : Type v} (shape : ComplexShape ι)
    (K : HomologicalComplex P.Modules shape) (n : ι) :
    (restrictFunctorComp k j).hom.app (K.homology n) ≫
        (restrictFunctor k).map ((K.sc n).mapHomologyIso (restrictFunctor j)).inv ≫
        (((((restrictFunctor j).mapHomologicalComplex shape).obj K).sc n).mapHomologyIso
          (restrictFunctor k)).inv =
      ((K.sc n).mapHomologyIso (restrictFunctor (k ≫ j))).inv ≫
        homologyMap (canonicalRestrictionCompComplexIso j k shape K).hom n := by
  let r := canonicalRestrictionCompComplexIso j k shape K
  let E :=
    (((((restrictFunctor j).mapHomologicalComplex shape).obj K).sc n).mapHomologyIso
      (restrictFunctor k)) ≪≫
      (restrictFunctor k).mapIso ((K.sc n).mapHomologyIso (restrictFunctor j))
  have hE : (K.sc n).mapHomologyIso (restrictFunctor j ⋙ restrictFunctor k) = E := by
    apply Iso.ext
    exact ShortComplex.mapHomologyIso_comp_hom (restrictFunctor j) (restrictFunctor k) (K.sc n)
  have hr : (shortComplexFunctor V'.Modules shape n).map r.hom =
      (K.sc n).mapNatTrans (restrictFunctorComp k j).hom := by
    ext <;> simp [r, canonicalRestrictionCompComplexIso]
  have h := NatTrans.app_homology (restrictFunctorComp k j).hom (K.sc n)
  erw [hE] at h
  have hh : (restrictFunctorComp k j).hom.app (K.homology n) =
      ((K.sc n).mapHomologyIso (restrictFunctor (k ≫ j))).inv ≫
        homologyMap r.hom n ≫ E.hom := by
    change (restrictFunctorComp k j).hom.app (K.homology n) =
      ((K.sc n).mapHomologyIso (restrictFunctor (k ≫ j))).inv ≫
        ShortComplex.homologyMap ((shortComplexFunctor V'.Modules shape n).map r.hom) ≫ E.hom
    rw [hr]
    exact h
  have hc := congrArg (fun t => t ≫ E.inv) hh
  have hc' : (restrictFunctorComp k j).hom.app (K.homology n) ≫ E.inv =
      ((K.sc n).mapHomologyIso (restrictFunctor (k ≫ j))).inv ≫ homologyMap r.hom n := by
    simpa only [Category.assoc, Iso.hom_inv_id, Category.comp_id] using hc
  simpa only [E, r, Iso.trans_inv, Functor.mapIso_inv] using hc'

end Restriction

section Closed
variable {W' W U V' V P : Scheme.{u}} (f : U ⟶ P) [IsClosedImmersion f]
  {L : P.Modules} (J : InjectiveResolution L)
  (a : W ⟶ U) (j : V ⟶ P) (b : W ⟶ V)
  [IsOpenImmersion a] [IsOpenImmersion j] [IsClosedImmersion b]
  (h : IsPullback a b f j)

/-- Original open comparison on ordinary fixed-model homology, with the native source map. -/
def closedImmersionChartModelStepHomologyMap (n : ℤ) :
    ((((closedImmersionRightAdjoint f).mapHomologicalComplex (.up ℤ)).obj
        J.cochainComplex).homology n).restrict a ⟶
      (((closedImmersionRightAdjoint b).mapHomologicalComplex (.up ℤ)).obj
        (canonicalAmbientChartResolution J j).cochainComplex).homology n :=
  (((((closedImmersionRightAdjoint f).mapHomologicalComplex (.up ℤ)).obj
    J.cochainComplex).sc n).mapHomologyIso (restrictFunctor a)).inv ≫
      homologyMap (closedImmersionModelOpenIso f J a j b h).hom n

/-- The original native restricted-model comparison followed by the actual open-model iso. -/
def closedImmersionChartModelHomologyIso (n : ℤ) :
    ((DerivedCategory.Plus.homologyFunctor U.Modules n).obj
      ((closedImmersionRightAdjoint f).rightDerivedFunctorPlus.obj
        ((DerivedCategory.Plus.singleFunctor P.Modules 0).obj L))).restrict a ≅
      (((closedImmersionRightAdjoint b).mapHomologicalComplex (.up ℤ)).obj
        (canonicalAmbientChartResolution J j).cochainComplex).homology n :=
  closedImmersionRestrictedModelHomologyIso f J a n ≪≫
    (homologyFunctor W.Modules (.up ℤ) n).mapIso (closedImmersionModelOpenIso f J a j b h)

/-- Its forward arrow retains the original global model isomorphism and native step map. -/
theorem closedImmersionChartModelHomologyIso_hom (n : ℤ) :
    (closedImmersionChartModelHomologyIso f J a j b h n).hom =
      (restrictFunctor a).map (closedImmersionModelHomologyIso f J n).hom ≫
        closedImmersionChartModelStepHomologyMap f J a j b h n := by
  change ((restrictFunctor a).map (closedImmersionModelHomologyIso f J n).hom ≫
      (((((closedImmersionRightAdjoint f).mapHomologicalComplex (.up ℤ)).obj
        J.cochainComplex).sc n).mapHomologyIso (restrictFunctor a)).inv) ≫
        homologyMap (closedImmersionModelOpenIso f J a j b h).hom n = _
  exact Category.assoc _ _ _

variable (c : W' ⟶ W) (k : V' ⟶ V) (d : W' ⟶ V')
  [IsOpenImmersion c] [IsOpenImmersion k] [IsClosedImmersion d]
  (h' : IsPullback c d b k)

/-- Native ordinary-model homology retains the original strict cochain composition square. -/
theorem closedImmersionChartModelStepHomologyMap_comp (n : ℤ) :
    (restrictFunctorComp c a).hom.app
        ((((closedImmersionRightAdjoint f).mapHomologicalComplex (.up ℤ)).obj
          J.cochainComplex).homology n) ≫
        (restrictFunctor c).map (closedImmersionChartModelStepHomologyMap f J a j b h n) ≫
        closedImmersionChartModelStepHomologyMap b
          (canonicalAmbientChartResolution J j) c k d h' n =
      closedImmersionChartModelStepHomologyMap f J (c ≫ a) (k ≫ j) d
          (h'.paste_horiz h) n ≫
        homologyMap (((closedImmersionRightAdjoint d).mapHomologicalComplex (.up ℤ)).map
          (canonicalAmbientResolutionCompLift j k J).hom') n := by
  let K := ((closedImmersionRightAdjoint f).mapHomologicalComplex (.up ℤ)).obj J.cochainComplex
  let K₁ := ((closedImmersionRightAdjoint b).mapHomologicalComplex (.up ℤ)).obj
    (canonicalAmbientChartResolution J j).cochainComplex
  let O₁ := closedImmersionModelOpenIso f J a j b h
  let O₂ := closedImmersionModelOpenIso b (canonicalAmbientChartResolution J j) c k d h'
  let O₀ := closedImmersionModelOpenIso f J (c ≫ a) (k ≫ j) d (h'.paste_horiz h)
  let r := canonicalRestrictionCompComplexIso a c (.up ℤ) K
  let q := ((closedImmersionRightAdjoint d).mapHomologicalComplex (.up ℤ)).map
    (canonicalAmbientResolutionCompLift j k J).hom'
  let e₁ := (K.sc n).mapHomologyIso (restrictFunctor a)
  let e₂ := (K₁.sc n).mapHomologyIso (restrictFunctor c)
  let e₁₂ := ((((restrictFunctor a).mapHomologicalComplex
    (.up ℤ)).obj K).sc n).mapHomologyIso (restrictFunctor c)
  let e₀ := (K.sc n).mapHomologyIso (restrictFunctor (c ≫ a))
  have hN := ShortComplex.mapHomologyIso_inv_naturality
    ((shortComplexFunctor W.Modules (.up ℤ) n).map O₁.hom) (restrictFunctor c)
  change (restrictFunctor c).map (homologyMap O₁.hom n) ≫ e₂.inv =
    e₁₂.inv ≫ homologyMap (((restrictFunctor c).mapHomologicalComplex (.up ℤ)).map O₁.hom) n
      at hN
  have hR := canonicalRestrictionCompComplexIso_homology a c (.up ℤ) K n
  have hC := closedImmersionModelOpenIso_comp_homology f J a j b h c k d h' n
  simp only [closedImmersionChartModelStepHomologyMap, Functor.map_comp, Category.assoc]
  change (restrictFunctorComp c a).hom.app (K.homology n) ≫
      (restrictFunctor c).map e₁.inv ≫ (restrictFunctor c).map (homologyMap O₁.hom n) ≫
      e₂.inv ≫ homologyMap O₂.hom n = e₀.inv ≫ homologyMap O₀.hom n ≫ homologyMap q n
  calc
    _ = (restrictFunctorComp c a).hom.app (K.homology n) ≫
        (restrictFunctor c).map e₁.inv ≫ e₁₂.inv ≫
        homologyMap (((restrictFunctor c).mapHomologicalComplex (.up ℤ)).map O₁.hom) n ≫
        homologyMap O₂.hom n := by
      simpa only [Category.assoc] using congrArg
        (fun t => (restrictFunctorComp c a).hom.app (K.homology n) ≫
          (restrictFunctor c).map e₁.inv ≫ t ≫ homologyMap O₂.hom n) hN
    _ = e₀.inv ≫ homologyMap r.hom n ≫
        homologyMap (((restrictFunctor c).mapHomologicalComplex (.up ℤ)).map O₁.hom) n ≫
        homologyMap O₂.hom n := by
      simpa only [r, e₁, e₁₂, e₀, Category.assoc] using congrArg
        (fun t => t ≫
          homologyMap (((restrictFunctor c).mapHomologicalComplex (.up ℤ)).map O₁.hom) n ≫
          homologyMap O₂.hom n) hR
    _ = _ := by
      simpa only [r, O₁, O₂, O₀, q, Category.assoc] using congrArg
        (fun t => e₀.inv ≫ t) hC

/-- The original global native homology comparison obeys the same chart-composition square. -/
theorem closedImmersionChartModelHomologyIso_comp (n : ℤ) :
    (restrictFunctorComp c a).hom.app
        ((DerivedCategory.Plus.homologyFunctor U.Modules n).obj
          ((closedImmersionRightAdjoint f).rightDerivedFunctorPlus.obj
            ((DerivedCategory.Plus.singleFunctor P.Modules 0).obj L))) ≫
        (restrictFunctor c).map (closedImmersionChartModelHomologyIso f J a j b h n).hom ≫
        closedImmersionChartModelStepHomologyMap b
          (canonicalAmbientChartResolution J j) c k d h' n =
      (closedImmersionChartModelHomologyIso f J (c ≫ a) (k ≫ j) d
        (h'.paste_horiz h) n).hom ≫
        homologyMap (((closedImmersionRightAdjoint d).mapHomologicalComplex (.up ℤ)).map
          (canonicalAmbientResolutionCompLift j k J).hom') n := by
  let K := ((closedImmersionRightAdjoint f).mapHomologicalComplex (.up ℤ)).obj J.cochainComplex
  let θ := (closedImmersionModelHomologyIso f J n).hom
  let S₁ := closedImmersionChartModelStepHomologyMap f J a j b h n
  let S₂ := closedImmersionChartModelStepHomologyMap b
    (canonicalAmbientChartResolution J j) c k d h' n
  let S₀ := closedImmersionChartModelStepHomologyMap f J (c ≫ a) (k ≫ j) d
    (h'.paste_horiz h) n
  let q := ((closedImmersionRightAdjoint d).mapHomologicalComplex (.up ℤ)).map
    (canonicalAmbientResolutionCompLift j k J).hom'
  have hθ := (restrictFunctorComp c a).hom.naturality θ
  change (restrictFunctor (c ≫ a)).map θ ≫
      (restrictFunctorComp c a).hom.app (K.homology n) =
    (restrictFunctorComp c a).hom.app
        ((DerivedCategory.Plus.homologyFunctor U.Modules n).obj
          ((closedImmersionRightAdjoint f).rightDerivedFunctorPlus.obj
            ((DerivedCategory.Plus.singleFunctor P.Modules 0).obj L))) ≫
      (restrictFunctor c).map ((restrictFunctor a).map θ) at hθ
  have hS := closedImmersionChartModelStepHomologyMap_comp f J a j b h c k d h' n
  rw [closedImmersionChartModelHomologyIso_hom, closedImmersionChartModelHomologyIso_hom]
  simp only [Functor.map_comp, Category.assoc]
  change (restrictFunctorComp c a).hom.app
      ((DerivedCategory.Plus.homologyFunctor U.Modules n).obj
        ((closedImmersionRightAdjoint f).rightDerivedFunctorPlus.obj
          ((DerivedCategory.Plus.singleFunctor P.Modules 0).obj L))) ≫
      (restrictFunctor c).map ((restrictFunctor a).map θ) ≫
      (restrictFunctor c).map S₁ ≫ S₂ =
    (restrictFunctor (c ≫ a)).map θ ≫ S₀ ≫ homologyMap q n
  calc
    _ = (restrictFunctor (c ≫ a)).map θ ≫
        (restrictFunctorComp c a).hom.app (K.homology n) ≫
        (restrictFunctor c).map S₁ ≫ S₂ := by
      simpa only [Category.assoc] using congrArg
        (fun t => t ≫ (restrictFunctor c).map S₁ ≫ S₂) hθ.symm
    _ = _ := by
      simpa only [S₁, S₂, S₀, q, Category.assoc] using congrArg
        (fun t => (restrictFunctor (c ≫ a)).map θ ≫ t) hS

end Closed
end AlgebraicGeometry.Scheme.Modules
