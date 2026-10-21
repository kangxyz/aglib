/-
Copyright (c) 2026 kangxyz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.FieldTheory.SeparablyGenerated.EmbeddedField

/-!
# Restriction of general separability along a field embedding

An actual embedding over the base preserves general separability by applying
the embedded finite-type field theorem to each finite intermediate field.
-/

@[expose] public section

namespace Algebra

/-- General separability restricts along an actual embedding over the base field.
The source need not itself be essentially of finite type. -/
theorem isTranscendentalSeparable_of_algHom
    {F E L : Type*} [Field F] [Field E] [Field L]
    [Algebra F E] [Algebra F L] [IsTranscendentalSeparable F L]
    (e : E →ₐ[F] L) : IsTranscendentalSeparable F E := by
  refine ⟨fun K hK => ?_⟩
  let := hK
  exact isSeparablyGenerated_of_algHom (e.comp K.val)

end Algebra
