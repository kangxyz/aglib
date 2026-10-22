/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.Cohomology.GrothendieckExistence.FormalPullbackCompletionUnits
public import Aglib.AlgebraicGeometry.Modules.BaseChange.Affine.Mate

/-! # Base change of the specified formal modification isomorphism

The comparison is built from the native pullback-square isomorphism and the
original quotient-unit completion comparison. It applies both to open charts
and to completed affine bases; no projectivity or effectivity is presumed.
-/

@[expose] public noncomputable section
open CategoryTheory Opposite
namespace AlgebraicGeometry.Scheme.Modules.Coherent
universe u
variable {R : Type u} [CommRing R]
  {X Y X' Y' : Scheme.{u}}
  [IsLocallyNoetherian X] [IsLocallyNoetherian Y]
  [IsLocallyNoetherian X'] [IsLocallyNoetherian Y']
  (a : Y' ⟶ Y) (b : Y' ⟶ X') (p : Y ⟶ X) (g : X' ⟶ X)
  (h : a ≫ p = b ≫ g) (f : X ⟶ Spec (CommRingCat.of R)) (I : Ideal R)
  (F : AdicSystem X (idealThickeningIdealSheaf f I)) (G : Y.CoherentSheaf)
  (β : (baseIdealPullbackFunctor p f I).obj F ≅
    (completionFunctor Y (idealThickeningIdealSheaf (p ≫ f) I)).obj G)

omit [IsLocallyNoetherian X] [IsLocallyNoetherian Y]
  [IsLocallyNoetherian X'] [IsLocallyNoetherian Y'] in
include h in
/-- The structural ideal agrees along the original commutative square. -/
theorem formalModificationBaseChange_ideal :
    idealThickeningIdealSheaf (a ≫ (p ≫ f)) I =
      idealThickeningIdealSheaf (b ≫ (g ≫ f)) I := by
  rw [← Category.assoc, h, Category.assoc]

local instance : G.obj.IsQuasicoherent :=
  QuasiCoherent.quasicoherent_of_affineCharts _ (fun B j _ => (G.property B j).1)

/-- Original scalar quotient comparison with its actual structural-ideal transport. -/
def squarePullbackQuotientComparisonOfComm (n : ℕ) :
    {e : (pullback a).obj
        ((idealSheafQuotientFunctor Y (idealThickeningIdealSheaf (p ≫ f) I ^ n)).obj G.obj) ≅
      (idealSheafQuotientFunctor Y' (idealThickeningIdealSheaf (b ≫ (g ≫ f)) I ^ n)).obj
        ((pullback a).obj G.obj) //
      (pullback a).map
        ((idealSheafQuotientUnit Y (idealThickeningIdealSheaf (p ≫ f) I ^ n)).app G.obj) ≫
        e.hom = (idealSheafQuotientUnit Y'
          (idealThickeningIdealSheaf (b ≫ (g ≫ f)) I ^ n)).app ((pullback a).obj G.obj)} :=
  arrowFamilyComparison
    (fun K => (idealSheafQuotientFunctor Y' K).obj ((pullback a).obj G.obj))
    (fun K => (idealSheafQuotientUnit Y' K).app ((pullback a).obj G.obj))
    ((pullback a).map
      ((idealSheafQuotientUnit Y (idealThickeningIdealSheaf (p ≫ f) I ^ n)).app G.obj))
    (baseIdealPullbackQuotientIso a (p ≫ f) I G.obj n)
    (baseIdealPullbackQuotientIso_unit a (p ≫ f) I G.obj n)
    (congrArg (fun K => K ^ n) (formalModificationBaseChange_ideal a b p g h f I))

/-- Whole original base-change diagram, with its literal original stage arrows. -/
def formalModificationBaseChangeData :
    {e : (F.obj ⋙ pullback g) ⋙ pullback b ≅
      idealSheafQuotientTower Y' (idealThickeningIdealSheaf (b ≫ (g ≫ f)) I)
        ((pullback a).obj G.obj) // ∀ n,
      e.hom.app (op n) = (pullbackSquareIso a b p g h).hom.app (F.obj.obj (op n)) ≫
        (pullback a).map (β.hom.hom.app (op n)) ≫
          (squarePullbackQuotientComparisonOfComm a b p g h f I G n).val.hom} := by
  let c := transportDiagramUnitComparison
    (fun K => idealSheafQuotientTower Y' K ((pullback a).obj G.obj))
    (idealSheafQuotientTower Y (idealThickeningIdealSheaf (p ≫ f) I) G.obj ⋙ pullback a)
    ((pullback a).obj G.obj)
    (fun n => (pullback a).map
      ((idealSheafQuotientUnit Y (idealThickeningIdealSheaf (p ≫ f) I ^ n)).app G.obj))
    (fun K n => (idealSheafQuotientUnit Y' (K ^ n)).app ((pullback a).obj G.obj))
    (formalModificationBaseChange_ideal a b p g h f I)
    (pullbackCompletionDiagramComparison a (p ≫ f) I G)
  have hu : ∀ n, Epi ((pullback a).map
      ((idealSheafQuotientUnit Y (idealThickeningIdealSheaf (p ≫ f) I ^ n)).app G.obj)) :=
    fun n => by
      let : Epi ((idealSheafQuotientUnit Y
          (idealThickeningIdealSheaf (p ≫ f) I ^ n)).app G.obj) :=
        pullbackPushforwardUnit_epi (idealThickeningIdealSheaf (p ≫ f) I ^ n).subschemeι G.obj
      infer_instance
  exact originalModificationDiagramComparison F.obj (pullback p) (pullback g)
    (pullback a) (pullback b) (pullbackSquareIso a b p g h)
    (idealSheafQuotientTower Y (idealThickeningIdealSheaf (p ≫ f) I) G.obj)
    ((adicSystemToDiagram Y (idealThickeningIdealSheaf (p ≫ f) I)).mapIso β)
    (idealSheafQuotientTower Y' (idealThickeningIdealSheaf (b ≫ (g ≫ f)) I)
      ((pullback a).obj G.obj)) ((pullback a).obj G.obj)
    (fun n => (pullback a).map
      ((idealSheafQuotientUnit Y (idealThickeningIdealSheaf (p ≫ f) I ^ n)).app G.obj))
    (fun n => (idealSheafQuotientUnit Y' (idealThickeningIdealSheaf (b ≫ (g ≫ f)) I ^ n)).app
      ((pullback a).obj G.obj)) c
    (fun n => squarePullbackQuotientComparisonOfComm a b p g h f I G n) hu

/-- The original native diagram comparison, projected only after its certificate. -/
def formalModificationBaseChangeDiagramIso :
    (F.obj ⋙ pullback g) ⋙ pullback b ≅
      idealSheafQuotientTower Y' (idealThickeningIdealSheaf (b ≫ (g ≫ f)) I)
        ((pullback a).obj G.obj) :=
  (formalModificationBaseChangeData a b p g h f I F G β).val

/-- The formal iso and its original component equation are lifted together. -/
def formalModificationBaseChangeFormalData :
    {e : (baseIdealPullbackFunctor b (g ≫ f) I).obj
        ((baseIdealPullbackFunctor g f I).obj F) ≅
      (completionFunctor Y' (idealThickeningIdealSheaf (b ≫ (g ≫ f)) I)).obj
        ((coherentPullback a).obj G) //
      ∀ n, e.hom.hom.app (op n) =
        (pullbackSquareIso a b p g h).hom.app (F.obj.obj (op n)) ≫
          (pullback a).map (β.hom.hom.app (op n)) ≫
            (squarePullbackQuotientComparisonOfComm a b p g h f I G n).val.hom} :=
  formalIsoComparisonOfDiagram _
    ((baseIdealPullbackFunctor b (g ≫ f) I).obj
      ((baseIdealPullbackFunctor g f I).obj F))
    ((completionFunctor Y' (idealThickeningIdealSheaf (b ≫ (g ≫ f)) I)).obj
      ((coherentPullback a).obj G))
    (fun e => ∀ n, e.app (op n) =
      (pullbackSquareIso a b p g h).hom.app (F.obj.obj (op n)) ≫
        (pullback a).map (β.hom.hom.app (op n)) ≫
          (squarePullbackQuotientComparisonOfComm a b p g h f I G n).val.hom)
    (formalModificationBaseChangeData a b p g h f I F G β)

/-- Native ordinary formal pullback retains the specified upstairs
algebraization after arbitrary commutative base change. -/
def formalModificationBaseChangeIso :
    (baseIdealPullbackFunctor b (g ≫ f) I).obj
      ((baseIdealPullbackFunctor g f I).obj F) ≅
    (completionFunctor Y' (idealThickeningIdealSheaf (b ≫ (g ≫ f)) I)).obj
      ((coherentPullback a).obj G) :=
  (formalModificationBaseChangeFormalData a b p g h f I F G β).val

end AlgebraicGeometry.Scheme.Modules.Coherent
