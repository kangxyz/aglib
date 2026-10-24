/-
Copyright (c) 2026 kangxyz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.FunctionField.AffineCharts
public import Mathlib.RingTheory.Trace.Basic

/-!
# Original field trace in a birational square

In a commuting square of dominant morphisms of integral schemes, if the
two vertical original function-field maps are isomorphisms, the horizontal
field traces agree through those same maps. The proof uses the native trace
transport theorem and the original generic-stalk functoriality.

The current consumer is the fixed original Gram matrix on finite diagrams
dominating normal surface modifications. No independently selected field
identification or trace-compatibility premise is used.
-/

@[expose] public noncomputable section

open CategoryTheory AlgebraicGeometry

namespace AlgebraicGeometry.Scheme

universe u

variable {S T X Y : Scheme.{u}}
  [IsIntegral S] [IsIntegral T] [IsIntegral X] [IsIntegral Y]
  (s : T ⟶ S) (a : X ⟶ S) (b : Y ⟶ T) (π : Y ⟶ X)
  [IsDominant s] [IsDominant a] [IsDominant b] [IsDominant π]

/-- The horizontal field trace commutes with the original vertical
birational field maps of the actual scheme square. -/
theorem functionFieldTrace_birational_square
    (ha : IsIso (CommRingCat.ofHom (functionFieldMap a)))
    (hb : IsIso (CommRingCat.ofHom (functionFieldMap b)))
    (hsq : π ≫ a = b ≫ s) (z : T.functionField) :
    letI := functionFieldMapAlgebra s
    letI := functionFieldMapAlgebra π
    functionFieldMap a (Algebra.trace S.functionField T.functionField z) =
      Algebra.trace X.functionField Y.functionField (functionFieldMap b z) := by
  let := functionFieldMapAlgebra s
  let := functionFieldMapAlgebra π
  let := ha
  let := hb
  let eA : S.functionField ≃+* X.functionField :=
    (asIso (CommRingCat.ofHom (functionFieldMap a))).commRingCatIsoToRingEquiv
  let eB : T.functionField ≃+* Y.functionField :=
    (asIso (CommRingCat.ofHom (functionFieldMap b))).commRingCatIsoToRingEquiv
  have he : (algebraMap X.functionField Y.functionField).comp eA.toRingHom =
      eB.toRingHom.comp (algebraMap S.functionField T.functionField) := by
    change (functionFieldMap π).comp (functionFieldMap a) =
      (functionFieldMap b).comp (functionFieldMap s)
    have hcongr {c d : Y ⟶ S} [IsDominant c] [IsDominant d] (hcd : c = d) :
        functionFieldMap c = functionFieldMap d := by
      subst d
      rfl
    exact (functionFieldMap_comp π a).symm.trans
      ((hcongr hsq).trans (functionFieldMap_comp b s))
  have ht := Algebra.trace_eq_of_equiv_equiv eA eB he z
  change eA (Algebra.trace S.functionField T.functionField z) =
    Algebra.trace X.functionField Y.functionField (eB z)
  simpa only [RingEquiv.apply_symm_apply] using congrArg eA ht

end AlgebraicGeometry.Scheme
