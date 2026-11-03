/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.Modules.InternalHom.BidualNaturalityRaw
public import Mathlib.CategoryTheory.Preadditive.AdditiveFunctor

/-! # Naturality of original bidual evaluation

The contravariant functor uses the existing internal-Hom map. Its objects
are the existing dual sheaves, and canonical biduality retains evaluation.
No second dual or evaluation construction is introduced.
-/

@[expose] public noncomputable section

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open CategoryTheory Opposite AlgebraicGeometry

namespace AlgebraicGeometry.Scheme.Modules.InternalHom

universe u v w

open _root_.AlgebraicGeometry.Scheme.Modules.Invertible

/-- Assemble the original evaluation family before specializing the category and dual functor. -/
def bidualEvaluationOfNaturality
    {C : Type v} [Category.{w} C] (D : Cᵒᵖ ⥤ C)
    (η : ∀ M : C, M ⟶ D.obj (op (D.obj (op M))))
    (hη : ∀ {M N : C} (f : M ⟶ N),
      f ≫ η N = η M ≫ D.map (D.map f.op).op) :
    𝟭 C ⟶ D.rightOp ⋙ D where
  app M := η M
  naturality _ _ f := hη f

variable (X : Scheme.{u})

/-- The original canonical evaluation commutes with every original module map. -/
@[reassoc] theorem bidualMap_naturality {M N : X.Modules} (f : M ⟶ N) :
    f ≫ bidualMap X N = bidualMap X M ≫
      (dualFunctor X).map ((dualFunctor X).map f.op).op := by
  have hinner := dualFunctor_map_eq X f.op
  have houter := dualFunctor_map_eq X ((dualFunctor X).map f.op).op
  have hmap := congrArg
    (fun a : dualSheaf X N ⟶ dualSheaf X M =>
      _root_.SheafOfModules.InternalHom.map X.sheaf a
        (𝟙 (SheafOfModules.unit X.ringCatSheaf))) hinner
  have hboth := houter.trans hmap
  exact (bidualMap_naturality_raw X f).trans
    (congrArg (fun a => bidualMap X M ≫ a) hboth.symm)

/-- The complete original section law follows from the same whole naturality square. -/
theorem bidualMap_naturality_app {M N : X.Modules} (f : M ⟶ N)
    (U : X.Opens) (m : M.val.obj (op U)) :
    (bidualMap X N).val.app (op U) (f.val.app (op U) m) =
      ((dualFunctor X).map ((dualFunctor X).map f.op).op).val.app (op U)
        ((bidualMap X M).val.app (op U) m) :=
  congrArg (fun k : M ⟶ dualSheaf X (dualSheaf X N) => k.val.app (op U) m)
    (bidualMap_naturality X f)

/-- Bidual evaluation is a natural transformation, with unchanged components. -/
def bidualEvaluation : 𝟭 X.Modules ⟶ (dualFunctor X).rightOp ⋙ dualFunctor X :=
  bidualEvaluationOfNaturality (dualFunctor X) (bidualMap X) (bidualMap_naturality X)

end AlgebraicGeometry.Scheme.Modules.InternalHom
