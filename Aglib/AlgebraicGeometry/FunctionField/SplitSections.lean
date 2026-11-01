/-
Copyright (c) 2026 kangxyz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.FunctionField.HartogsSections

/-! # Split original scalar restrictions on a nonempty open

A retraction of the original scalar restriction is its inverse. The argument
uses the original generic stalk and its fraction denominators, without
normality, Noetherianity, or a replacement fraction-field model.
-/

@[expose] public noncomputable section

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open CategoryTheory

namespace AlgebraicGeometry.Scheme

universe u

variable (A : Type u) [CommRing A] [IsDomain A]
  (U : (Spec (.of A)).Opens) [Nonempty U]
  (ρ : Γ(Spec (.of A), U) →+* A)
  (hρ : ρ.comp (hartogsScalarMap A U) = RingHom.id A)

/-- The algebra structure of the affine function field over its coordinate ring. -/
local instance splitSectionsFunctionFieldAlgebra : Algebra A (Spec (.of A)).functionField :=
  AlgebraicGeometry.instAlgebraCarrierFunctionFieldSpec (.of A)

local instance : IsFractionRing A (Spec (.of A)).functionField :=
  functionField_isFractionRing_of_affine (.of A)

include hρ in
/-- A supplied original scalar retraction is also a right inverse, on every
actual section of the unchanged nonempty open. -/
theorem hartogsScalarMap_retraction_apply (s : Γ(Spec (.of A), U)) :
    hartogsScalarMap A U (ρ s) = s := by
  let β := hartogsScalarMap A U
  let γ := ((Spec (.of A)).germToFunctionField U).hom
  have hγβ (a : A) : γ (β a) = algebraMap A (Spec (.of A)).functionField a :=
    ConcreteCategory.congr_hom (hartogsScalarMap_generic A U) a
  have hρβ (a : A) : ρ (β a) = a := RingHom.congr_fun hρ a
  obtain ⟨a, b, hb, hv⟩ := IsFractionRing.div_surjective A (γ s)
  have hb0 : b ≠ 0 := mem_nonZeroDivisors_iff_ne_zero.mp hb
  have hbK : algebraMap A (Spec (.of A)).functionField b ≠ 0 := by
    intro h
    apply hb0
    apply IsFractionRing.injective A (Spec (.of A)).functionField
    simpa only [map_zero] using h
  have he : s * β b = β a := by
    apply (Spec (.of A)).germToFunctionField_injective U
    change γ (s * β b) = γ (β a)
    rw [map_mul, hγβ, hγβ]
    exact ((div_eq_iff hbK).mp hv).symm
  have hr : ρ s * b = a := by
    have h := congrArg ρ he
    simpa only [map_mul, hρβ] using h
  apply (Spec (.of A)).germToFunctionField_injective U
  change γ (β (ρ s)) = γ s
  apply mul_right_cancel₀ hbK
  calc
    γ (β (ρ s)) * algebraMap A (Spec (.of A)).functionField b =
        algebraMap A (Spec (.of A)).functionField (ρ s * b) := by
      rw [hγβ, map_mul]
    _ = algebraMap A (Spec (.of A)).functionField a := congrArg _ hr
    _ = γ s * algebraMap A (Spec (.of A)).functionField b :=
      (div_eq_iff hbK).mp hv

include hρ in
/-- The complete original scalar-ring composite is the identity. -/
theorem hartogsScalarMap_comp_retraction :
    (hartogsScalarMap A U).comp ρ = RingHom.id Γ(Spec (.of A), U) := by
  ext s
  exact hartogsScalarMap_retraction_apply A U ρ hρ s

include hρ in
/-- A split scalar restriction on an integral affine scheme is bijective. -/
theorem hartogsScalarMap_bijective_of_retraction :
    Function.Bijective (hartogsScalarMap A U) :=
  ⟨hartogsScalarMap_injective A U,
    fun s => ⟨ρ s, hartogsScalarMap_retraction_apply A U ρ hρ s⟩⟩

/-- The ring equivalence uses the supplied retraction itself as inverse. -/
def splitSectionsEquiv : A ≃+* Γ(Spec (.of A), U) where
  __ := hartogsScalarMap A U
  invFun := ρ
  left_inv a := RingHom.congr_fun hρ a
  right_inv s := hartogsScalarMap_retraction_apply A U ρ hρ s

@[simp] theorem splitSectionsEquiv_apply (a : A) :
    splitSectionsEquiv A U ρ hρ a = hartogsScalarMap A U a := rfl

@[simp] theorem splitSectionsEquiv_symm_apply (s : Γ(Spec (.of A), U)) :
    (splitSectionsEquiv A U ρ hρ).symm s = ρ s := rfl

end AlgebraicGeometry.Scheme
