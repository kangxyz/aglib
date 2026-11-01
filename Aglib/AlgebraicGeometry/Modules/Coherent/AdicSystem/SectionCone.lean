/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.Modules.Coherent.AdicSystem.Completion

/-! # Original section cones of ideal-sheaf quotients

These are the existing quotient tower and its actual unit, evaluated at the
original top open. No completeness, properness or Noetherianity is assumed,
and no alternate completion object is introduced.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite

namespace AlgebraicGeometry.Scheme.Modules.Coherent

universe u

variable (X : Scheme.{u}) (K : X.IdealSheafData)

/-- Global sections of the original closed-thickening quotient diagram. -/
def idealSheafSectionDiagram (M : X.Modules) : ℕᵒᵖ ⥤ ModuleCat.{u} Γ(X, ⊤) :=
  idealSheafQuotientTower X K M ⋙ SheafOfModules.evaluation X.ringCatSheaf (op ⊤)

/-- The original quotient units, evaluated on the original top open. -/
def idealSheafSectionCone (M : X.Modules) : Cone (idealSheafSectionDiagram X K M) :=
  (SheafOfModules.evaluation X.ringCatSheaf (op ⊤)).mapCone
    ⟨M, idealSheafQuotientTowerUnit X K M⟩

/-- The cone vertex is the original section module. -/
theorem idealSheafSectionCone_pt (M : X.Modules) :
    (idealSheafSectionCone X K M).pt =
      (SheafOfModules.evaluation X.ringCatSheaf (op ⊤)).obj M := rfl

/-- Each projection is the original quotient unit on sections. -/
@[simp] theorem idealSheafSectionCone_π (M : X.Modules) (n : ℕᵒᵖ) :
    (idealSheafSectionCone X K M).π.app n =
      (SheafOfModules.evaluation X.ringCatSheaf (op ⊤)).map
        ((idealSheafQuotientUnit X (K ^ n.unop)).app M) := rfl

/-- Original coefficient maps induce maps of the same section diagrams. -/
def idealSheafSectionDiagramHom {M N : X.Modules} (f : M ⟶ N) :
    idealSheafSectionDiagram X K M ⟶ idealSheafSectionDiagram X K N :=
  Functor.whiskerRight (idealSheafQuotientTowerHom X K f)
    (SheafOfModules.evaluation X.ringCatSheaf (op ⊤))

/-- The complete cone square is the original unit naturality square. -/
theorem idealSheafSectionCone_naturality {M N : X.Modules} (f : M ⟶ N) :
    (Functor.const ℕᵒᵖ).map
        ((SheafOfModules.evaluation X.ringCatSheaf (op ⊤)).map f) ≫
      (idealSheafSectionCone X K N).π =
        (idealSheafSectionCone X K M).π ≫ idealSheafSectionDiagramHom X K f := by
  apply NatTrans.ext
  funext n
  change (SheafOfModules.evaluation X.ringCatSheaf (op ⊤)).map f ≫
      (SheafOfModules.evaluation X.ringCatSheaf (op ⊤)).map
        ((idealSheafQuotientUnit X (K ^ n.unop)).app N) =
    (SheafOfModules.evaluation X.ringCatSheaf (op ⊤)).map
        ((idealSheafQuotientUnit X (K ^ n.unop)).app M) ≫
      (SheafOfModules.evaluation X.ringCatSheaf (op ⊤)).map
        ((idealSheafQuotientFunctor X (K ^ n.unop)).map f)
  let E := SheafOfModules.evaluation X.ringCatSheaf (op ⊤)
  have h := congrArg E.map ((idealSheafQuotientUnit X (K ^ n.unop)).naturality f)
  exact (E.map_comp f ((idealSheafQuotientUnit X (K ^ n.unop)).app N)).symm.trans
    (h.trans (E.map_comp ((idealSheafQuotientUnit X (K ^ n.unop)).app M)
      ((idealSheafQuotientFunctor X (K ^ n.unop)).map f)))

end AlgebraicGeometry.Scheme.Modules.Coherent
