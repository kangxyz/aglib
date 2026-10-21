/-
Copyright (c) 2026 kangxyz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Mathlib.FieldTheory.TranscendentalSeparable

/-!
# Separating generation of an embedded finite-type field

An actual embedding into a generally separable ambient field transfers
separating generation to an essentially finite-type field extension. The
intermediate field used in the proof is the literal range of that embedding.
No separability of the ambient extension is manufactured by this result.
-/

@[expose] public section

namespace Algebra

variable {F E L : Type*} [Field F] [Field E] [Field L]
  [Algebra F E] [Algebra F L]

/-- An essentially finite-type field embedded over the same coefficient field
in a transcendental-separable extension is separably generated. -/
theorem isSeparablyGenerated_of_algHom
    [EssFiniteType F E] [IsTranscendentalSeparable F L] (e : E →ₐ[F] L) :
    IsSeparablyGenerated F E := by
  let : EssFiniteType F e.fieldRange :=
    (EssFiniteType.iff_of_algEquiv e.equivFieldRange).mp inferInstance
  let : IsSeparablyGenerated F e.fieldRange :=
    IsTranscendentalSeparable.forall_isSeparablyGenerated e.fieldRange inferInstance
  exact e.equivFieldRange.symm.isSeparablyGenerated

end Algebra
