/-
Copyright (c) 2026 kangxyz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.RingTheory.DiscreteValuationRing.ParameterProjectedTarget
public import Aglib.RingTheory.NeronModification.EvaluatedFittingLocalization

/-! # Fitting transport on the actual projected parameter chart

These consumers use precisely `sourceDenominators`, `scalarMap`, and
`projectedTargetMap`. The first keeps the old projected index; the second
compares the SAME modification before and after the actual localization.
-/

@[expose] public noncomputable section

open IsLocalRing MvPolynomial Algebra.NeronModification

namespace ParameterLocalization.ProjectedCentre

variable {R S A K ι : Type*} [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]
  [CommRing S] [IsDomain S] [IsDiscreteValuationRing S] [Algebra R S]
  [IsLocalHom (algebraMap R S)] [CommRing A] [Algebra R A]
  [Field K] [Algebra (ResidueField R) K]
  (p : R) [Fact (Irreducible p)] (D : Subalgebra (ResidueField R) K)
  (f : A →+* D)
  (hf : f.comp (algebraMap R A) = (algebraMap (ResidueField R) D).comp (residue R))
  (b : ι → A)
  (hy : AlgebraicIndependent (ResidueField R) (fun i => (f (b i) : K)))
  (χ : A →ₐ[R] S) (e : K →ₐ[ResidueField R] ResidueField S)
  (hχ : ∀ a, e (f a) = residue S (χ a))

local notation "P" => MvPolynomial ι R
local notation "R₂" => Ring R ι p
local notation "A'" => Localization (sourceDenominators p b)

/-- Localization at the exact parameter denominators preserves the evaluated
old projected Fitting ideal. `k` is already the shifted index in this statement. -/
theorem map_fittingIdeal_projectedTargetMap [Algebra.FiniteType R A] (k : ℕ) :
    letI : Algebra P A := (aeval b).toRingHom.toAlgebra
    letI : Algebra R₂ A' := (scalarMap p b).toAlgebra
    (Module.fittingIdeal A' (KaehlerDifferential R₂ A') k).map
      (projectedTargetMap p D f hf b hy χ e hχ).toRingHom =
    (Module.fittingIdeal A (KaehlerDifferential P A) k).map χ.toRingHom := by
  let : Algebra P A := (aeval b).toRingHom.toAlgebra
  let : IsScalarTower R P A :=
    IsScalarTower.of_algebraMap_eq (R := R) (S := P) (A := A)
      fun r => ((aeval (R := R) b).commutes r).symm
  let : Algebra R₂ A' := (scalarMap p b).toAlgebra
  let : IsScalarTower P R₂ A' :=
    IsScalarTower.of_algebraMap_eq (R := P) (S := R₂) (A := A')
      fun q => (scalarMap_algebraMap p b q).symm
  let : Algebra.FiniteType P A := Algebra.FiniteType.of_restrictScalars_finiteType R P A
  let : IsLocalization (R := A) (Algebra.algebraMapSubmonoid A
      (parameterIdeal R ι p).primeCompl) A' := by
    change IsLocalization (R := A) (sourceDenominators p b) A'
    infer_instance
  have hpoint : (projectedTargetMap p D f hf b hy χ e hχ).toRingHom.comp
      (algebraMap A A') = (RingHom.id S).comp χ.toRingHom := by
    ext a
    exact projectedTargetMap_algebraMap p D f hf b hy χ e hχ a
  have h := KaehlerDifferential.map_fittingIdeal_of_isLocalizationSquare P R₂ A A'
    (parameterIdeal R ι p).primeCompl χ.toRingHom
    (projectedTargetMap p D f hf b hy χ e hχ).toRingHom (RingHom.id S) hpoint k
  simpa only [Ideal.map_id] using h

/-- The localized modification point is compared with the original modification
point using their actual source restrictions. The centre family is literally `g`
and its image; no domain assumption on `A` or its modification is needed.
The displayed nested image of `p` equals `algebraMap R A' p` by the scalar tower. -/
theorem map_fittingIdeal_projectedModification
    {ν : Type*} [Finite ν] [Algebra.FiniteType R A] (g : ν → A)
    (χM : Modification (algebraMap R A p) g →+* S)
    (χN : Modification (algebraMap A A' (algebraMap R A p))
      (fun j => algebraMap A A' (g j)) →+* S)
    (hχM : χM.comp (of (algebraMap R A p) g) = χ.toRingHom)
    (hχN : χN.comp (of (algebraMap A A' (algebraMap R A p))
      (fun j => algebraMap A A' (g j))) =
        (projectedTargetMap p D f hf b hy χ e hχ).toRingHom)
    (hpS : Irreducible (algebraMap R S p)) (k : ℕ) :
    letI : Algebra P A := (aeval b).toRingHom.toAlgebra
    letI : Algebra R₂ A' := (scalarMap p b).toAlgebra
    (Module.fittingIdeal _ (KaehlerDifferential R₂
      (Modification (algebraMap A A' (algebraMap R A p))
        (fun j => algebraMap A A' (g j)))) k).map χN =
    (Module.fittingIdeal _ (KaehlerDifferential P
      (Modification (algebraMap R A p) g)) k).map χM := by
  let : Algebra P A := (aeval b).toRingHom.toAlgebra
  let : IsScalarTower R P A :=
    IsScalarTower.of_algebraMap_eq (R := R) (S := P) (A := A)
      fun r => ((aeval (R := R) b).commutes r).symm
  let : Algebra R₂ A' := (scalarMap p b).toAlgebra
  let : IsScalarTower P R₂ A' :=
    IsScalarTower.of_algebraMap_eq (R := P) (S := R₂) (A := A')
      fun q => (scalarMap_algebraMap p b q).symm
  let : Algebra.FiniteType P A := Algebra.FiniteType.of_restrictScalars_finiteType R P A
  let : IsLocalization (R := A) (Algebra.algebraMapSubmonoid A
      (parameterIdeal R ι p).primeCompl) A' := by
    change IsLocalization (R := A) (sourceDenominators p b) A'
    infer_instance
  have hpoint : (projectedTargetMap p D f hf b hy χ e hχ).toRingHom.comp
      (algebraMap A A') = (RingHom.id S).comp χ.toRingHom := by
    ext a
    exact projectedTargetMap_algebraMap p D f hf b hy χ e hχ a
  have hregular : IsRegular ((RingHom.id S) (χ.toRingHom (algebraMap R A p))) := by
    change IsRegular (χ (algebraMap R A p))
    rw [χ.commutes]
    exact isRegular_iff_ne_zero.mpr hpS.ne_zero
  have h := map_fittingIdeal_baseChangeOriginal_of_isLocalizationSquare
    (R := P) (R' := R₂) (B' := A') (algebraMap R A p) g
    (parameterIdeal R ι p).primeCompl χ.toRingHom
    (projectedTargetMap p D f hf b hy χ e hχ).toRingHom
    (RingHom.id S) hpoint χM χN hχM hχN hregular k
  simpa only [Ideal.map_id] using h

end ParameterLocalization.ProjectedCentre
