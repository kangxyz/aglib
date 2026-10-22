/-
Copyright (c) 2026 kangxyz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.RingTheory.DiscreteValuationRing.ParameterChart

/-! # The actual coefficient triangle for the parameter tensor chart -/

@[expose] public noncomputable section

open scoped TensorProduct

namespace ParameterLocalization

variable {R A ι : Type*} [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]
  [CommRing A] [Algebra R A] [Algebra (MvPolynomial ι R) A]
  [IsScalarTower R (MvPolynomial ι R) A]
variable (p : R) [Fact (Irreducible p)]

/-- The actual localized polynomial coefficient map. When the polynomial action is
`aeval b`, this is definitionally `ProjectedCentre.scalarMap p b`. -/
def chartScalarMap : Ring R ι p →+*
    Localization (Algebra.algebraMapSubmonoid A (parameterIdeal R ι p).primeCompl) :=
  IsLocalization.map (M := (parameterIdeal R ι p).primeCompl)
    (T := Algebra.algebraMapSubmonoid A (parameterIdeal R ι p).primeCompl)
    (Localization (Algebra.algebraMapSubmonoid A (parameterIdeal R ι p).primeCompl))
    (algebraMap (MvPolynomial ι R) A) (parameterIdeal R ι p).primeCompl.le_comap_map

omit [Algebra R A] [IsScalarTower R (MvPolynomial ι R) A] in
@[simp] theorem chartScalarMap_algebraMap (q : MvPolynomial ι R) :
    chartScalarMap (A := A) p (algebraMap (MvPolynomial ι R) (Ring R ι p) q) =
      algebraMap A
        (Localization (Algebra.algebraMapSubmonoid A (parameterIdeal R ι p).primeCompl))
        (algebraMap (MvPolynomial ι R) A q) :=
  IsLocalization.map_eq (M := (parameterIdeal R ι p).primeCompl)
    (S := Ring R ι p)
    (T := Algebra.algebraMapSubmonoid A (parameterIdeal R ι p).primeCompl)
    (Q := Localization (Algebra.algebraMapSubmonoid A (parameterIdeal R ι p).primeCompl))
    (g := algebraMap (MvPolynomial ι R) A)
    (parameterIdeal R ι p).primeCompl.le_comap_map q

omit [Algebra R A] [IsScalarTower R (MvPolynomial ι R) A] in
/-- The native chart equivalence preserves the actual new coefficient map.
This does not follow merely from its already-established original-source linearity. -/
theorem chartEquivLocalization_comp_algebraMap :
    (chartEquivLocalization (A := A) (α := ι) p).toRingHom.comp
      (algebraMap (Ring R ι p) (Chart (A := A) (α := ι) p)) = chartScalarMap (A := A) p := by
  apply IsLocalization.ringHom_ext (parameterIdeal R ι p).primeCompl
  apply RingHom.ext
  intro q
  simp only [RingHom.comp_apply, chartScalarMap_algebraMap]
  change chartEquivLocalization (A := A) (α := ι) p
    ((algebraMap (MvPolynomial ι R) (Ring R ι p) q) ⊗ₜ[MvPolynomial ι R] (1 : A)) = _
  rw [Algebra.TensorProduct.tmul_one_eq_one_tmul, chartEquivLocalization_one_tmul]

/-- The chart comparison is an equivalence over the actual new coefficient DVR. -/
def chartEquivLocalizationOverParameters :
    letI : Algebra (Ring R ι p)
        (Localization (Algebra.algebraMapSubmonoid A (parameterIdeal R ι p).primeCompl)) :=
      (chartScalarMap (A := A) p).toAlgebra
    Chart (A := A) (α := ι) p ≃ₐ[Ring R ι p]
      Localization (Algebra.algebraMapSubmonoid A (parameterIdeal R ι p).primeCompl) := by
  let : Algebra (Ring R ι p)
      (Localization (Algebra.algebraMapSubmonoid A (parameterIdeal R ι p).primeCompl)) :=
    (chartScalarMap (A := A) p).toAlgebra
  let : Algebra A (Chart (A := A) (α := ι) p) := Algebra.TensorProduct.rightAlgebra
  refine { (chartEquivLocalization (A := A) (α := ι) p).toRingEquiv with commutes' := ?_ }
  intro a
  exact RingHom.congr_fun (chartEquivLocalization_comp_algebraMap (A := A) p) a

end ParameterLocalization
