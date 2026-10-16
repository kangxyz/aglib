/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.Modules.PerfectComplexes.LocalTriangles

/-!
# Local perfectness under shifts and cones

Actual locally perfect complexes are closed under integer shifts and the
original mapping cone. Strict representatives are chosen only on actual
neighborhoods; no global strict representative or scheme finiteness
hypothesis is added.

Source: `Quillen/AlgebraicGeometry/PerfectComplexes/OpenFibration.lean`.
Frozen dirty Quillen:
`6db56ddd3fdb898ef5de29d5fe51a0c61f9ba116`.
Source SHA-256: `9d04e9fa3fbf700eeae24f9471c8f53aa079cfadd09bd3384cf134e9bbceccfe`.
Selected declaration ranges: 56–67.
Source: `Quillen/AlgebraicGeometry/PerfectComplexes/SplitFactorization.lean`.
Frozen dirty Quillen:
`6db56ddd3fdb898ef5de29d5fe51a0c61f9ba116`.
Source SHA-256: `3990a2566e2db66f3ca487142071b56253c3b3bb0bab101eb631bb110146fa3a`.
Selected declaration ranges: 47–65.
-/

@[expose] public section

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open CochainComplex

universe u

namespace AlgebraicGeometry.Scheme.Modules.Complex

attribute [local instance] AlgebraicGeometry.Scheme.Modules.standardHasDerivedCategory

/-- The native mapped-functor shift structure, registered only in this proof scope. -/
local instance restrictCommShift {U X : Scheme.{u}} (j : U ⟶ X) [IsOpenImmersion j] :
    (restrict j).CommShift ℤ := by
  unfold restrict
  infer_instance

theorem locallyPerfect_shift {X : Scheme.{u}} {K : CochainComplex X.Modules ℤ}
    (hK : locallyPerfect X K) (n : ℤ) :
    locallyPerfect X ((CategoryTheory.shiftFunctor (CochainComplex X.Modules ℤ) n).obj K) := by
  intro x
  obtain ⟨O, hx, P, ⟨eP⟩⟩ := hK x
  refine ⟨O, hx, ⟨(CategoryTheory.shiftFunctor (CochainComplex O.toScheme.Modules ℤ) n).obj P.obj,
    strictPerfect_shift P.property n⟩, ⟨?_⟩⟩
  exact (DerivedCategory.Q (C := O.toScheme.Modules)).mapIso
    (((restrict O.ι).commShiftIso n).app K) ≪≫
    ((DerivedCategory.Q (C := O.toScheme.Modules)).commShiftIso n).app ((restrict O.ι).obj K) ≪≫
    (CategoryTheory.shiftFunctor (DerivedCategory O.toScheme.Modules) n).mapIso eP ≪≫
    (((DerivedCategory.Q (C := O.toScheme.Modules)).commShiftIso n).app P.obj).symm

theorem locallyPerfect_mappingCone {X : Scheme.{u}} {K L : CochainComplex X.Modules ℤ}
    (hK : locallyPerfect X K) (hL : locallyPerfect X L) (f : K ⟶ L) :
    locallyPerfect X (mappingCone f) := by
  apply locallyPerfect_of_openImmersion_models
  intro x
  obtain ⟨U, hxU, ⟨P, ⟨eP⟩⟩, ⟨Q, ⟨eQ⟩⟩⟩ := exists_common_strictModels hK hL x
  let fU := (restrict U.ι).map f
  let T := (DerivedCategory.Q (C := U.toScheme.Modules)).mapTriangle.obj (mappingCone.triangle fU)
  obtain ⟨Y, j, hj, y, hy, h⟩ := exists_local_strictModel_of_triangle T
    (DerivedCategory.mappingCone_triangle_distinguished fU) P.property Q.property eP eQ (Iso.refl _)
      ⟨x, hxU⟩
  let := hj
  let e := mappingCone.mapHomologicalComplexIso f (Scheme.Modules.restrictFunctor U.ι)
  refine ⟨Y, j ≫ U.ι, inferInstance, y, ?_, ?_⟩
  · change U.ι (j y) = x
    rw [hy]
    rfl
  · exact (h.of_iso ((restrict j).mapIso e.symm)).of_iso
      ((restrictCompIso j U.ι).app (mappingCone f))

end AlgebraicGeometry.Scheme.Modules.Complex
