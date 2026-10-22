/-
Copyright (c) 2026 algebraic-geometry contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.Modules.Coherent.AdicSystem.Quotient
public import Aglib.AlgebraicGeometry.Modules.ClosedImmersion.KilledQuotient

/-! # Interchange of the original quotients by independent ideal sheaves -/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry.Scheme.Modules.Coherent

universe u

variable (X : Scheme.{u}) (I K : X.IdealSheafData)

/-- Quotient by an independent ideal preserves existing annihilation. -/
theorem idealSheafQuotient_killed_of_killed {F : X.Modules}
    (hF : killedByIdealSheaf I F) :
    killedByIdealSheaf I ((idealSheafQuotientFunctor X K).obj F) :=
  killedByIdealSheaf_of_epi I ((idealSheafQuotientUnit X K).app F) hF

/-- The canonical map interchanging two independent original quotients. -/
def idealSheafQuotientInterchangeHom (F : X.Modules) :
    (idealSheafQuotientFunctor X K).obj ((idealSheafQuotientFunctor X I).obj F) ⟶
      (idealSheafQuotientFunctor X I).obj ((idealSheafQuotientFunctor X K).obj F) :=
  idealSheafQuotientDesc X K
    (idealSheafQuotientDesc X I
      ((idealSheafQuotientUnit X K).app F ≫
        (idealSheafQuotientUnit X I).app ((idealSheafQuotientFunctor X K).obj F))
      (idealSheafQuotient_killed X I _))
    (idealSheafQuotient_killed_of_killed X K I (idealSheafQuotient_killed X K F))

@[reassoc]
theorem idealSheafQuotientUnit_interchangeHom (F : X.Modules) :
    (idealSheafQuotientUnit X I).app F ≫
      (idealSheafQuotientUnit X K).app ((idealSheafQuotientFunctor X I).obj F) ≫
        idealSheafQuotientInterchangeHom X I K F =
    (idealSheafQuotientUnit X K).app F ≫
      (idealSheafQuotientUnit X I).app ((idealSheafQuotientFunctor X K).obj F) := by
  simp [idealSheafQuotientInterchangeHom]

/-- Independent quotients commute canonically on their composite original units. -/
def idealSheafQuotientInterchangeIso (F : X.Modules) :
    (idealSheafQuotientFunctor X K).obj ((idealSheafQuotientFunctor X I).obj F) ≅
      (idealSheafQuotientFunctor X I).obj ((idealSheafQuotientFunctor X K).obj F) where
  hom := idealSheafQuotientInterchangeHom X I K F
  inv := idealSheafQuotientInterchangeHom X K I F
  hom_inv_id := by
    apply (cancel_epi ((idealSheafQuotientUnit X K).app
      ((idealSheafQuotientFunctor X I).obj F))).mp
    apply (cancel_epi ((idealSheafQuotientUnit X I).app F)).mp
    simp only [Functor.id_obj, Functor.comp_obj,
      idealSheafQuotientUnit_interchangeHom_assoc, Category.comp_id]
    exact idealSheafQuotientUnit_interchangeHom X K I F
  inv_hom_id := by
    apply (cancel_epi ((idealSheafQuotientUnit X I).app
      ((idealSheafQuotientFunctor X K).obj F))).mp
    apply (cancel_epi ((idealSheafQuotientUnit X K).app F)).mp
    simp only [Functor.id_obj, Functor.comp_obj,
      idealSheafQuotientUnit_interchangeHom_assoc, Category.comp_id]
    exact idealSheafQuotientUnit_interchangeHom X I K F

@[reassoc]
theorem idealSheafQuotientUnit_interchangeIso_hom (F : X.Modules) :
    (idealSheafQuotientUnit X I).app F ≫
      (idealSheafQuotientUnit X K).app ((idealSheafQuotientFunctor X I).obj F) ≫
        (idealSheafQuotientInterchangeIso X I K F).hom =
    (idealSheafQuotientUnit X K).app F ≫
      (idealSheafQuotientUnit X I).app ((idealSheafQuotientFunctor X K).obj F) :=
  idealSheafQuotientUnit_interchangeHom X I K F

end AlgebraicGeometry.Scheme.Modules.Coherent
