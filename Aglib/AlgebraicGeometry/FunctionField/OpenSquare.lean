/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.FunctionField.AffineCharts
public import Mathlib.LinearAlgebra.Dimension.Finrank
public import Mathlib.RingTheory.Finiteness.Basic

/-!
# Original function fields across a commuting open square

Open immersions induce the existing function-field equivalences. The original
generic stalk maps form a commuting square, so the native equiv-equiv theorems
transport its finrank and finite-dimensionality. Only the hypotheses needed
to define these original maps are imposed on the square.
-/

@[expose] public noncomputable section

open CategoryTheory AlgebraicGeometry

universe u

namespace AlgebraicGeometry.Scheme.FunctionField

attribute [local instance] Scheme.isDominant_of_isOpenImmersion

variable {V U Y X : Scheme.{u}}
  [IsIntegral V] [IsIntegral U] [IsIntegral Y] [IsIntegral X]
  (p : Y ⟶ X) [IsDominant p] (f : V ⟶ U) [IsDominant f]
  (jU : U ⟶ X) [IsOpenImmersion jU] (jV : V ⟶ Y) [IsOpenImmersion jV]
  (h : f ≫ jU = jV ≫ p)

include h

/-- The whole original field maps commute with the original open field equivalences. -/
theorem map_open_square :
    (functionFieldMap f).comp (fieldEquiv jU).toRingHom =
      (fieldEquiv jV).toRingHom.comp (functionFieldMap p) := by
  change (functionFieldMap f).comp (functionFieldMap jU) =
    (functionFieldMap jV).comp (functionFieldMap p)
  rw [← functionFieldMap_comp, ← functionFieldMap_comp]
  congr 1

/-- Inverse transport of the same whole field square, with the same original fields. -/
theorem map_open_square_inv :
    (functionFieldMap p).comp (fieldEquiv jU).symm.toRingHom =
      (fieldEquiv jV).symm.toRingHom.comp (functionFieldMap f) := by
  apply RingHom.ext
  intro a
  apply (fieldEquiv jV).injective
  change fieldEquiv jV (functionFieldMap p ((fieldEquiv jU).symm a)) =
    fieldEquiv jV ((fieldEquiv jV).symm (functionFieldMap f a))
  rw [RingEquiv.apply_symm_apply]
  have hs := RingHom.congr_fun (map_open_square p f jU jV h) ((fieldEquiv jU).symm a)
  change functionFieldMap f (fieldEquiv jU ((fieldEquiv jU).symm a)) =
    fieldEquiv jV (functionFieldMap p ((fieldEquiv jU).symm a)) at hs
  rw [RingEquiv.apply_symm_apply] at hs
  exact hs.symm

/-- The two original function-field degrees, at their native finrank carriers,
are equal. No flatness or finiteness is needed for this comparison. -/
theorem finrank_open_square :
    letI := functionFieldMapAlgebra p
    letI := functionFieldMapAlgebra f
    Module.finrank X.functionField Y.functionField =
      Module.finrank U.functionField V.functionField := by
  let := functionFieldMapAlgebra p
  let := functionFieldMapAlgebra f
  exact Algebra.finrank_eq_of_equiv_equiv (fieldEquiv jU) (fieldEquiv jV)
    (map_open_square p f jU jV h)

/-- Finite-dimensionality on the actual open fields transfers to the original
completion fields through the proved square. -/
theorem finite_of_open_square
    (hfin : letI := functionFieldMapAlgebra f
      Module.Finite U.functionField V.functionField) :
    letI := functionFieldMapAlgebra p
    Module.Finite X.functionField Y.functionField := by
  let := functionFieldMapAlgebra p
  let := functionFieldMapAlgebra f
  let := hfin
  exact Module.Finite.of_equiv_equiv (fieldEquiv jU).symm (fieldEquiv jV).symm
    (map_open_square_inv p f jU jV h)

end AlgebraicGeometry.Scheme.FunctionField
