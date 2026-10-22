/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.Modules.Coherent.AdicSystem.Completion

/-! # Coherent completion on an empty scheme

This is the empty-scheme case of existence and the zero exponent of the
exceptional-ideal thickening tower. No positive-power induction hypothesis
is silently used at exponent zero.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits
open scoped ZeroObject

namespace AlgebraicGeometry.Scheme.Modules.Coherent

universe u
variable (X : Scheme.{u}) [IsEmpty X]

private theorem moduleIsZeroOfIsEmpty (M : X.Modules) : IsZero M := by
  apply (Scheme.Modules.isZero_iff_stalks M).mpr
  intro x
  exact isEmptyElim x

variable [IsLocallyNoetherian X]

/-- Every original coherent formal system on an empty scheme is effective. -/
theorem completionFunctorEssSurjOfIsEmpty (K : X.IdealSheafData) :
    (completionFunctor X K).EssSurj where
  mem_essImage F := by
    let C := completionFunctor X K
    let G : X.CoherentSheaf := 0
    let e : (C.obj G).obj ≅ F.obj := NatIso.ofComponents
      (fun n => (moduleIsZeroOfIsEmpty X ((C.obj G).obj.obj n)).isoZero ≪≫
        (moduleIsZeroOfIsEmpty X (F.obj.obj n)).isoZero.symm)
      (fun {j k} a => (moduleIsZeroOfIsEmpty X ((C.obj G).obj.obj j)).eq_of_src _ _)
    exact ⟨G, ⟨ObjectProperty.isoMk _ e⟩⟩

end AlgebraicGeometry.Scheme.Modules.Coherent
