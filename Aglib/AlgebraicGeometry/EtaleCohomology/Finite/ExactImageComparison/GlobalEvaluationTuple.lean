/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import
  Aglib.AlgebraicGeometry.EtaleCohomology.Finite.ExactImageComparison.PointedEvaluationBaseChange

/-! # The original direct-image evaluation tuple over a geometric fibre -/

@[expose] public noncomputable section

open CategoryTheory

namespace AlgebraicGeometry.Scheme.EtaleCohomology

universe u

open CoefficientStalkBaseChange
attribute [local instance] hasSheafifyLarge

variable {X S : Scheme.{u}} {Ω : Type u} [Field Ω] [IsSepClosed Ω]
  (f : X ⟶ S) (s : Spec (.of Ω) ⟶ S) (F : AbelianSheaf.{u, u + 1} X)

/-- The tuple uses actual geometric points over the specified point, not
maximal ideals of a chosen affine presentation. -/
def directImageEvaluationTupleTarget : AddCommGrpCat.{u + 1} :=
  AddCommGrpCat.of (∀ x : {x : Spec (.of Ω) ⟶ X // x ≫ f = s},
    coefficientFiber x.val F)

/-- Each coordinate is the original stalk unit followed by the original
adjunction counit. No comparison isomorphism enters the definition. -/
def directImageEvaluationTuple :
    coefficientFiber s ((directImage f).obj F) ⟶ directImageEvaluationTupleTarget f s F :=
  AddCommGrpCat.ofHom (AddMonoidHom.pi fun x =>
    (pointedDirectImageEvaluation f x.val s x.property F).hom)

@[simp] theorem directImageEvaluationTuple_apply
    (a : coefficientFiber s ((directImage f).obj F))
    (x : {x : Spec (.of Ω) ⟶ X // x ≫ f = s}) :
    directImageEvaluationTuple f s F a x =
      pointedDirectImageEvaluation f x.val s x.property F a := rfl

end AlgebraicGeometry.Scheme.EtaleCohomology
