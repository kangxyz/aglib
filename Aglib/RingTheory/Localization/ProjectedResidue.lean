/-
Copyright (c) 2026 kangxyz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.RingTheory.Localization.SeparatingParameters
public import Mathlib.RingTheory.Localization.Ideal
public import Mathlib.RingTheory.Ideal.Quotient.Operations

/-! # The actual quotient of the projected source

The source residue quotient and its parameter localization are compared by
actual maps. The source denominator-image identity is explicit here and is
supplied by polynomial residue lifting in the geometric application.
-/

@[expose] public noncomputable section

namespace SeparatingParameterLocalization

variable {k K ι B : Type*} [Field k] [Field K] [Algebra k K] [CommRing B]
variable (D : Subalgebra k K) (y : ι → D) (f : B →+* D) (M : Submonoid B)
variable (hM : M.map f = denominators D y)

/-- The source residue map induces the actual map of parameter localizations. -/
def localizedResidue : Localization M →+* Ring D y := by
  let : IsLocalization (M.map f) (Ring D y) := hM.symm ▸ inferInstance
  exact IsLocalization.map (M := M) (T := M.map f) (Ring D y) f M.le_comap_map

/-- The localized residue map preserves the original source residue map. -/
@[simp] theorem localizedResidue_algebraMap (b : B) :
    localizedResidue D y f M hM (algebraMap B (Localization M) b) =
      algebraMap D (Ring D y) (f b) := by
  let : IsLocalization (M.map f) (Ring D y) := hM.symm ▸ inferInstance
  exact IsLocalization.map_eq (M := M) (S := Localization M) (T := M.map f)
    (Q := Ring D y) (g := f) M.le_comap_map b

/-- An actual surjective source residue map remains surjective after localization. -/
theorem localizedResidue_surjective (hf : Function.Surjective f) :
    Function.Surjective (localizedResidue D y f M hM) := by
  let : IsLocalization (M.map f) (Ring D y) := hM.symm ▸ inferInstance
  exact IsLocalization.map_surjective_of_surjective
    (S := Localization M) (Q := Ring D y) (g := f) M hf

variable (hy : AlgebraicIndependent k (fun i => (y i : K)))

/-- The projected source point takes values in the actual original fraction field. -/
def projectedPoint : Localization M →+* K :=
  (point D y hy).comp (localizedResidue D y f M hM)

/-- The actual projected point agrees with the original residue quotient on source elements. -/
@[simp] theorem projectedPoint_algebraMap (b : B) :
    projectedPoint D y f M hM hy (algebraMap B (Localization M) b) = (f b : K) := by
  rw [projectedPoint, RingHom.comp_apply, localizedResidue_algebraMap, point_algebraMap]

/-- The kernel of the actual projected point is exactly the extended source residue kernel. -/
theorem ker_projectedPoint :
    RingHom.ker (projectedPoint D y f M hM hy) =
      (RingHom.ker f).map (algebraMap B (Localization M)) := by
  have hker : (RingHom.ker (projectedPoint D y f M hM hy)).under B = RingHom.ker f := by
    ext b
    change projectedPoint D y f M hM hy (algebraMap B (Localization M) b) = 0 ↔ f b = 0
    rw [projectedPoint_algebraMap]
    change ((f b : D) : K) = ((0 : D) : K) ↔ f b = 0
    exact Subtype.coe_inj
  rw [← hker]
  exact (IsLocalization.map_under M (Localization M)
    (RingHom.ker (projectedPoint D y f M hM hy))).symm

/-- Algebraicity over the actual parameter field makes the projected residue point surjective. -/
theorem projectedPoint_surjective [IsFractionRing D K] (hf : Function.Surjective f)
    (halg : letI := (fractionMap D y hy).toAlgebra
      Algebra.IsAlgebraic (FractionRing (MvPolynomial ι k)) K) :
    Function.Surjective (projectedPoint D y f M hM hy) :=
  (point_surjective D y hy halg).comp (localizedResidue_surjective D y f M hM hf)

/-- The quotient by the extended original centre is the actual original fraction field. -/
def projectedQuotientEquiv [IsFractionRing D K] (hf : Function.Surjective f)
    (halg : letI := (fractionMap D y hy).toAlgebra
      Algebra.IsAlgebraic (FractionRing (MvPolynomial ι k)) K) :
    (Localization M ⧸ (RingHom.ker f).map (algebraMap B (Localization M))) ≃+* K :=
  (Ideal.quotEquivOfEq (ker_projectedPoint D y f M hM hy).symm).trans
    (RingHom.quotientKerEquivOfSurjective (projectedPoint_surjective D y f M hM hy hf halg))

/-- The quotient identification retains the literal original source residue map. -/
@[simp] theorem projectedQuotientEquiv_mk_algebraMap [IsFractionRing D K]
    (hf : Function.Surjective f)
    (halg : letI := (fractionMap D y hy).toAlgebra
      Algebra.IsAlgebraic (FractionRing (MvPolynomial ι k)) K) (b : B) :
    projectedQuotientEquiv D y f M hM hy hf halg
      (algebraMap B
        (Localization M ⧸ (RingHom.ker f).map (algebraMap B (Localization M))) b) =
      (f b : K) := by
  change projectedQuotientEquiv D y f M hM hy hf halg
    (Ideal.Quotient.mk _ (algebraMap B (Localization M) b)) = _
  simp only [projectedQuotientEquiv, RingEquiv.trans_apply, Ideal.quotEquivOfEq_mk,
    RingHom.quotientKerEquivOfSurjective_apply_mk, projectedPoint_algebraMap]

end SeparatingParameterLocalization
