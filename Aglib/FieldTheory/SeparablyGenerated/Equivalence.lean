/-
Copyright (c) 2026 kangxyz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.FieldTheory.SeparablyGenerated.EmbeddedField

/-!
# General separability under compatible field equivalences

Both the coefficient field and the extension field may change by actual ring
equivalences, provided their algebra maps commute. Separating bases and their
adjoined subfields are transported explicitly. No algebraicity assumption on
the entire extension is imposed.
-/

@[expose] public noncomputable section

namespace Algebra

variable {F F' E E' : Type*} [Field F] [Field F'] [Field E] [Field E']

/-- A coefficient-field isomorphism transports a separating basis in the same extension field. -/
theorem isSeparablyGenerated_of_baseRingEquiv [Algebra F E] [Algebra F' E]
    (e : F ≃+* F') (h : (algebraMap F' E).comp e.toRingHom = algebraMap F E)
    [IsSeparablyGenerated F E] : IsSeparablyGenerated F' E := by
  obtain ⟨s, hs, hsep⟩ := (inferInstance : IsSeparablyGenerated F E)
  have hi (t : Set E) :
      AlgebraicIndependent F ((↑) : t → E) ↔ AlgebraicIndependent F' ((↑) : t → E) := by
    simpa only [RingHom.coe_id, Function.id_comp, RingHom.id_apply] using
      (algebraicIndependent_ringHom_iff_of_comp_eq e (RingHom.id E)
        (Function.injective_id) (by
          change (algebraMap F' E).comp e.toRingHom =
            (RingHom.id E).comp (algebraMap F E)
          simpa only [RingHom.id_comp] using h)).symm
  have ht : IsTranscendenceBasis F' ((↑) : s → E) := by
    refine ⟨(hi s).mp hs.1, ?_⟩
    intro t hti hst
    exact hs.2 t ((hi t).mpr hti) hst
  have hr : Set.range (algebraMap F E) = Set.range (algebraMap F' E) := by
    ext x
    constructor
    · rintro ⟨a, rfl⟩
      exact ⟨e a, DFunLike.congr_fun h a⟩
    · rintro ⟨a, rfl⟩
      obtain ⟨a, rfl⟩ := e.surjective a
      exact ⟨a, (DFunLike.congr_fun h a).symm⟩
  have hadjoin : (IntermediateField.adjoin F s).toSubfield =
      (IntermediateField.adjoin F' s).toSubfield := by
    simp only [IntermediateField.adjoin_toSubfield, hr]
  let ea : IntermediateField.adjoin F s ≃+* IntermediateField.adjoin F' s :=
    RingEquiv.subfieldCongr hadjoin
  let : Algebra.IsSeparable (IntermediateField.adjoin F s) E := hsep
  refine ⟨s, ht, ?_⟩
  exact Algebra.IsSeparable.of_equiv_equiv ea (RingEquiv.refl E) rfl

/-- General separability is unchanged by a compatible coefficient-field isomorphism. -/
theorem isTranscendentalSeparable_of_baseRingEquiv [Algebra F E] [Algebra F' E]
    (e : F ≃+* F') (h : (algebraMap F' E).comp e.toRingHom = algebraMap F E)
    [IsTranscendentalSeparable F E] : IsTranscendentalSeparable F' E := by
  let : Algebra F F' := e.toRingHom.toAlgebra
  let : IsScalarTower F F' E := IsScalarTower.of_algebraMap_eq fun x =>
    (DFunLike.congr_fun h x).symm
  let : FiniteType F F' := FiniteType.of_surjective (Algebra.ofId F F') e.surjective
  refine ⟨fun L hL => ?_⟩
  let : EssFiniteType F' L := hL
  let : EssFiniteType F L := EssFiniteType.comp F F' L
  let : IsSeparablyGenerated F L :=
    isSeparablyGenerated_of_algHom (L.val.restrictScalars F)
  apply isSeparablyGenerated_of_baseRingEquiv e
  apply RingHom.ext
  intro x
  exact (IsScalarTower.algebraMap_apply F F' L x).symm

/-- General separability is transported by an actual equivalence over the same base. -/
theorem isTranscendentalSeparable_of_algEquiv [Algebra F E] [Algebra F E']
    (e : E ≃ₐ[F] E') [IsTranscendentalSeparable F E] :
    IsTranscendentalSeparable F E' := by
  refine ⟨fun L hL => ?_⟩
  let : EssFiniteType F L := hL
  exact isSeparablyGenerated_of_algHom (e.symm.toAlgHom.comp L.val)

/-- General separability transfers across a proved square of field equivalences. -/
theorem isTranscendentalSeparable_of_ringEquivs [Algebra F E] [Algebra F' E']
    (eF : F ≃+* F') (eE : E ≃+* E')
    (h : (algebraMap F' E').comp eF.toRingHom = eE.toRingHom.comp (algebraMap F E))
    [IsTranscendentalSeparable F E] : IsTranscendentalSeparable F' E' := by
  let : Algebra F E' := ((algebraMap F' E').comp eF.toRingHom).toAlgebra
  let e : E ≃ₐ[F] E' :=
    { eE with
      commutes' := fun x => (DFunLike.congr_fun h x).symm }
  let : IsTranscendentalSeparable F E' := isTranscendentalSeparable_of_algEquiv e
  exact isTranscendentalSeparable_of_baseRingEquiv eF rfl

end Algebra
