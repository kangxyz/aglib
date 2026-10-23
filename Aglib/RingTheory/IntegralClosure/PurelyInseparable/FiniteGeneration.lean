/-
Copyright (c) 2026 kangxyz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.RingTheory.AdicCompletion.FiniteGeneration
public import Aglib.RingTheory.AdicCompletion.FrobeniusSeparated
public import Aglib.RingTheory.IntegralClosure.PurelyInseparable

/-!
# Finite generation of purely inseparable normalization from a scalar quotient

Over a normal base, the literal normalization in a finite purely inseparable
fraction-field extension inherits adic separatedness from the base. If the
base is also precomplete, finiteness of one scalar quotient inside the chosen
ideal implies finiteness of that same normalization over the original base.
No Noetherianity or completeness of the normalization is assumed.

The current consumer is the residue-layer argument for normal complete local
surfaces. The finite scalar-quotient premise remains an explicit obligation;
these results alone do not prove normalization finiteness in dimension two.
-/

@[expose] public section

open scoped Pointwise

namespace integralClosure

variable (R K E : Type*) [CommRing R] [IsDomain R] [IsIntegrallyClosed R]
  [Field K] [Algebra R K] [IsFractionRing R K]
  [Field E] [Algebra K E] [Algebra R E] [IsScalarTower R K E]
  [FiniteDimensional K E] [IsPurelyInseparable K E]

include K

/-- The actual normalization is separated for the original coefficient-ideal
action. Normality makes every element's fixed Frobenius power a coefficient. -/
theorem isHausdorff_of_isPurelyInseparable (I : Ideal R) [IsHausdorff I R] :
    IsHausdorff I (integralClosure R E) := by
  let S := integralClosure R E
  let p := ringExpChar K
  let : ExpChar E p := expChar_of_injective_algebraMap (algebraMap K E).injective p
  let : ExpChar S p := (integralClosure R E).val.expChar Subtype.val_injective p
  let : Module.IsTorsionFree R E := .trans_faithfulSMul R K E
  let : Module.IsTorsionFree R S := IsIntegralClosure.isTorsionFree R E
  obtain ⟨e, he⟩ := (inferInstance : IsPurelyInseparable.HasExponent K E).has_exponent
  apply IsHausdorff.of_frobenius_pow_mem_range I p e
    (FaithfulSMul.algebraMap_injective R S)
  intro s
  have hq : 0 < p ^ e := expChar_pow_pos E p e
  obtain ⟨r, hr⟩ := (mem_iff_pow_mem_range R K E s.val (p ^ e) hq (he s.val)).mp s.property
  refine ⟨r, ?_⟩
  apply Subtype.ext
  exact hr

/-- A finite scalar quotient suffices for finiteness of the literal purely
inseparable normalization over a separated precomplete normal base. The scalar
lies in the original ideal, and the normalization need not be Noetherian. -/
theorem finite_of_isPrecomplete_of_finite_scalar_quotient (I : Ideal R)
    [IsPrecomplete I R] [IsHausdorff I R] (x : R) (hx : x ∈ I)
    [Module.Finite R (QuotSMulTop x (integralClosure R E))] :
    Module.Finite R (integralClosure R E) := by
  let S := integralClosure R E
  let : IsHausdorff I S := isHausdorff_of_isPurelyInseparable R K E I
  have hquot : x • (⊤ : Submodule R S) ≤ I • (⊤ : Submodule R S) := by
    rw [← Submodule.ideal_span_singleton_smul]
    exact Submodule.smul_mono_left ((Ideal.span_singleton_le_iff_mem I).mpr hx)
  let : Module.Finite R (S ⧸ (I • (⊤ : Submodule R S))) :=
    Module.Finite.of_surjective (Submodule.factor hquot) (Submodule.factor_surjective hquot)
  exact Module.finite_of_isPrecomplete_of_isHausdorff I

end integralClosure
