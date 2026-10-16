/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.Modules.ProjectionFormula.Affine
public import Aglib.AlgebraicGeometry.Modules.ProjectionFormula.OpenBaseChange
public import Aglib.AlgebraicGeometry.Modules.Locality.Exactness
public import Aglib.AlgebraicGeometry.Modules.LocallyFree.Locality

/-!
Source: `Quillen/AlgebraicGeometry/Scheme/VectorBundle/ProjectionFormula.lean` at LOCAL Quillen
`189a8e779f0c68b2dfc6f8195daebb3e684a5905`. Selection: whole_general_prerequisite;
source ranges [[1, 85]]. Actual objects, maps and hypotheses are preserved.
-/

/-!
# Projection formula for finite locally free coefficients

Use the original cartesian open-base-change square and affine basis cover to
prove invertibility of the original projection-formula arrow. The scheme
morphism and source module are arbitrary; the target coefficient is finite
locally free. No derived projection formula is asserted.
-/

@[expose] public section
noncomputable section

section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
universe u
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open AlgebraicGeometry.Scheme.Modules

namespace AlgebraicGeometry.Scheme.Modules
open Scheme.Modules
/-- Actual open base change transports invertibility of the original projection-formula arrow. -/
theorem isIso_projectionFormulaMap_restrict_of_isIso
    {W U V X : Scheme.{u}} (a : W ⟶ U) (b : W ⟶ V) (f : U ⟶ X) (j : V ⟶ X)
    [IsOpenImmersion a] [IsOpenImmersion j] (h : IsPullback a b f j)
    (E : X.Modules) (M : U.Modules)
    [IsIso (projectionFormulaMap b (E.restrict j) (M.restrict a))] :
    IsIso ((restrictFunctor j).map (projectionFormulaMap f E M)) := by
  let A := (tensorRestrictionIso j E ((pushforward f).obj M)).hom
  let B := (cartesianOpenBaseChange a b f j h).hom.app
    ((moduleTensorLeftFunctor U ((Scheme.Modules.pullback f).obj E)).obj M)
  have ht : IsIso ((moduleTensorCoefficientMap W
      ((cartesianPullbackBaseChangeMate a b f j h).app E)).app (M.restrict a)) := by
    change IsIso ((moduleTensorRightFunctor W (M.restrict a)).map
      ((cartesianPullbackBaseChangeMate a b f j h).app E))
    infer_instance
  have : IsIso (A ≫ (restrictFunctor j).map (projectionFormulaMap f E M) ≫ B) := by
    change IsIso ((tensorRestrictionIso j E ((pushforward f).obj M)).hom ≫
      (restrictFunctor j).map (projectionFormulaMap f E M) ≫ _)
    rw [projectionFormulaMap_openBaseChange a b f j h E M]
    infer_instance
  let : IsIso ((restrictFunctor j).map (projectionFormulaMap f E M) ≫ B) :=
    IsIso.of_isIso_comp_left A _
  exact IsIso.of_isIso_comp_right _ B
/-- The original ordinary projection formula holds for every finite locally free coefficient. -/
theorem isIso_projectionFormulaMap {X Y : Scheme.{u}} (f : X ⟶ Y)
    (E : Y.Modules) [IsFiniteLocallyFree Y E] (M : X.Modules) :
    IsIso (projectionFormulaMap f E M) := by
  apply isIso_of_restrict_openCover Y.affineBasisCover.X Y.affineBasisCover.f
    (fun y => ⟨Y.affineBasisCover.idx y, Y.affineBasisCover.covers y⟩)
  intro i
  let j := Y.affineBasisCover.f i
  let a := pullback.fst f j
  let b := pullback.snd f j
  let R := Y.affineBasisCoverRing i
  let : IsOpenImmersion j := inferInstanceAs (IsOpenImmersion (Y.affineBasisCover.f i))
  let : IsOpenImmersion a := inferInstanceAs (IsOpenImmersion (pullback.fst f j))
  let : IsFiniteLocallyFree (Spec R) (E.restrict j) := inferInstance
  let : IsIso (projectionFormulaMap b (E.restrict j) (M.restrict a)) :=
    isIso_projectionFormulaMap_affine R b (E.restrict j) (M.restrict a)
  exact isIso_projectionFormulaMap_restrict_of_isIso a b f j
    (IsPullback.of_hasPullback f j) E M
/-- The actual projection-formula isomorphism retains the original geometric unit
in its forward map. -/
def projectionFormulaIso {X Y : Scheme.{u}} (f : X ⟶ Y)
    (E : Y.Modules) [IsFiniteLocallyFree Y E] (M : X.Modules) :
    (moduleTensorLeftFunctor Y E).obj ((pushforward f).obj M) ≅
      (pushforward f).obj
        ((moduleTensorLeftFunctor X ((Scheme.Modules.pullback f).obj E)).obj M) := by
  let := isIso_projectionFormulaMap f E M
  exact asIso (projectionFormulaMap f E M)
/-- The comparison retains the literal original projection-formula arrow. -/
theorem projectionFormulaIso_hom {X Y : Scheme.{u}} (f : X ⟶ Y)
    (E : Y.Modules) [IsFiniteLocallyFree Y E] (M : X.Modules) :
    (projectionFormulaIso f E M).hom = projectionFormulaMap f E M := rfl

/-! The ordinary natural isomorphism is relocated from
`Aglib/AlgebraicGeometry/Cohomology/ProjectionFormula/Basic.lean` at Aglib451aeda, SHA-256
`875f049e57d37dc924b4ee57d71106bdb33da4d379fe9a63c55c36bdf6d6f8a4`. -/
variable {X Y : Scheme.{u}} (f : X ⟶ Y) (E : Y.Modules) [IsFiniteLocallyFree Y E]
/-- The original ordinary projection formula as an actual natural isomorphism. -/
def projectionFormulaNatIso :
    Scheme.Modules.pushforward f ⋙ moduleTensorLeftFunctor Y E ≅
      moduleTensorLeftFunctor X ((Scheme.Modules.pullback f).obj E) ⋙
        Scheme.Modules.pushforward f :=
  NatIso.ofComponents (projectionFormulaIso f E)
    (fun g => projectionFormulaMap_naturality f E g)
/-- Each forward component is literally the original ordinary projection-formula arrow. -/
theorem projectionFormulaNatIso_hom_app (M : X.Modules) :
    (projectionFormulaNatIso f E).hom.app M = projectionFormulaMap f E M := rfl

end AlgebraicGeometry.Scheme.Modules
end
