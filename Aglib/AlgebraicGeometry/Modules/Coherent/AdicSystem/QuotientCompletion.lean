/-
Copyright (c) 2026 algebraic-geometry contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.Modules.Coherent.AdicSystem.QuotientSystem

/-! # Independent quotients commute with the original coherent completion -/

@[expose] public noncomputable section

open CategoryTheory Opposite

namespace AlgebraicGeometry.Scheme.Modules.Coherent

universe u

variable (X : Scheme.{u}) (I K : X.IdealSheafData)

/-- Enlarging the second independent ideal commutes with original interchange. -/
@[reassoc]
theorem idealSheafQuotientInterchangeIso_second_ideal_naturality
    {L : X.IdealSheafData} (h : K ≤ L) (F : X.Modules) :
    idealSheafQuotientMap X K h ((idealSheafQuotientFunctor X I).obj F) ≫
        (idealSheafQuotientInterchangeIso X I L F).hom =
      (idealSheafQuotientInterchangeIso X I K F).hom ≫
        (idealSheafQuotientFunctor X I).map (idealSheafQuotientMap X K h F) := by
  apply (cancel_epi ((idealSheafQuotientUnit X K).app
    ((idealSheafQuotientFunctor X I).obj F))).mp
  apply (cancel_epi ((idealSheafQuotientUnit X I).app F)).mp
  dsimp only [Functor.comp_obj, Functor.id_obj]
  erw [idealSheafQuotientUnit_map_assoc X K h,
    idealSheafQuotientUnit_interchangeIso_hom X I L F,
    idealSheafQuotientUnit_interchangeIso_hom_assoc X I K F]
  erw [← (idealSheafQuotientUnit X I).naturality]
  simp only [Functor.id_map]
  erw [← Category.assoc, idealSheafQuotientUnit_map X K h F]
  rfl

/-- The original completion diagram of an independent quotient is the
independent termwise quotient of the original completion diagram. -/
def idealSheafQuotientCompletionDiagramIso (F : X.Modules) :
    idealSheafQuotientTower X I ((idealSheafQuotientFunctor X K).obj F) ≅
      idealSheafQuotientTower X I F ⋙ idealSheafQuotientFunctor X K :=
  NatIso.ofComponents
    (fun n => idealSheafQuotientInterchangeIso X K (I ^ n.unop) F)
    (by
      intro m n g
      exact idealSheafQuotientInterchangeIso_second_ideal_naturality X K (I ^ m.unop)
        (idealSheaf_pow_le X I (leOfHom g.unop)) F)

variable [IsLocallyNoetherian X]

/-- Completion and independent quotient commute in the original adic
category, not merely after replacement by isomorphic diagrams. -/
def idealSheafQuotientCompletionIso (F : X.CoherentSheaf) :
    (completionFunctor X I).obj
        ⟨(idealSheafQuotientFunctor X K).obj F.obj,
          idealSheafQuotient_coherent X K F.property⟩ ≅
      AdicSystem.quotient X I K ((completionFunctor X I).obj F) :=
  ObjectProperty.isoMk _ (idealSheafQuotientCompletionDiagramIso X I K F.obj)

/-- Each comparison component is the independently specified original
quotient interchange, including the zero stage. -/
@[simp]
theorem idealSheafQuotientCompletionIso_hom_app (F : X.CoherentSheaf) (n : ℕ) :
    (idealSheafQuotientCompletionIso X I K F).hom.hom.app (op n) =
      (idealSheafQuotientInterchangeIso X K (I ^ n) F.obj).hom := rfl

end AlgebraicGeometry.Scheme.Modules.Coherent
