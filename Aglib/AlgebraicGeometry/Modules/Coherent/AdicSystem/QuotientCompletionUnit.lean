/-
Copyright (c) 2026 algebraic-geometry contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.Modules.Coherent.AdicSystem.QuotientCompletion

/-! # The original coherent quotient unit under completion interchange -/

@[expose] public noncomputable section

open CategoryTheory Opposite

namespace AlgebraicGeometry.Scheme.Modules.Coherent

universe u

private theorem interchange_unit_aux {C : Type*} [Category C]
    (Q R : C ⥤ C) (η : 𝟭 C ⟶ Q) (θ : 𝟭 C ⟶ R) (F : C)
    (e : R.obj (Q.obj F) ⟶ Q.obj (R.obj F))
    (he : η.app F ≫ θ.app (Q.obj F) ≫ e = θ.app F ≫ η.app (R.obj F))
    [Epi (θ.app F)] : R.map (η.app F) ≫ e = η.app (R.obj F) := by
  apply (cancel_epi (θ.app F)).mp
  rw [← θ.naturality_assoc]
  simpa only [Functor.id_map] using he

variable (X : Scheme.{u}) (I K : X.IdealSheafData) [IsLocallyNoetherian X]

/-- The original quotient, regarded as a coherent coefficient. -/
abbrev idealSheafCoherentQuotient (F : X.CoherentSheaf) : X.CoherentSheaf :=
  ⟨(idealSheafQuotientFunctor X K).obj F.obj, idealSheafQuotient_coherent X K F.property⟩

/-- The original geometric quotient unit as a coherent morphism. -/
def idealSheafCoherentQuotientUnit (F : X.CoherentSheaf) :
    F ⟶ idealSheafCoherentQuotient X K F :=
  ObjectProperty.homMk ((idealSheafQuotientUnit X K).app F.obj)

/-- Completion interchange sends the completed original coherent quotient
unit to the actual termwise formal quotient unit. -/
@[reassoc (attr := simp)]
theorem completionQuotientUnit_interchange (F : X.CoherentSheaf) :
    (completionFunctor X I).map (idealSheafCoherentQuotientUnit X K F) ≫
      (idealSheafQuotientCompletionIso X I K F).hom =
      AdicSystem.quotientUnit X I K ((completionFunctor X I).obj F) := by
  apply ObjectProperty.hom_ext
  apply NatTrans.ext
  funext n
  exact interchange_unit_aux (idealSheafQuotientFunctor X K)
    (idealSheafQuotientFunctor X (I ^ n.unop)) (idealSheafQuotientUnit X K)
    (idealSheafQuotientUnit X (I ^ n.unop)) F.obj
    (idealSheafQuotientInterchangeIso X K (I ^ n.unop) F.obj).hom
    (idealSheafQuotientUnit_interchangeIso_hom X K (I ^ n.unop) F.obj)

end AlgebraicGeometry.Scheme.Modules.Coherent
