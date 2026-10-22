/-
Copyright (c) 2026 kangxyz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.RingTheory.DiscreteValuationRing.ParameterCompletionFraction
public import Aglib.RingTheory.DiscreteValuationRing.SameUniformizerValuation
public import Aglib.RingTheory.Valuation.IntegerMap

/-! # Literal valuation-ring residue data of the actual completed parameter extension -/

@[expose] public noncomputable section

open IsLocalRing

universe u v

private theorem eq_symm_polynomialScalar {k E F : Type*} [Field k] [Field E] [Field F]
    (ι : Type*) [Algebra k F] [Algebra (MvPolynomial ι k) F]
    [IsScalarTower k (MvPolynomial ι k) F] (e : E ≃+* F) (a : E) (x : k)
    (h : e a = algebraMap k F x) :
    a = e.symm (algebraMap (MvPolynomial ι k) F (MvPolynomial.C x)) := by
  apply e.injective
  rw [RingEquiv.apply_symm_apply, h]
  exact IsScalarTower.algebraMap_apply k (MvPolynomial ι k) F x

namespace ParameterLocalization

variable (R : Type u) [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]
  (ι : Type v) [Finite ι] (p : R) [Fact (Irreducible p)]

attribute [local instance] isDiscreteValuationRing algebraMap_isLocalHom
  completionAlgebra completionAlgebra_isLocalHom

local notation "T" => Ring R ι p
local notation "A" => AdicCompletion (maximalIdeal R) R
local notation "B" => AdicCompletion (maximalIdeal T) T
local notation "K" => FractionRing A
local notation "L" => FractionRing B
local notation "vA" =>
  IsDedekindDomain.HeightOneSpectrum.valuation K (IsDiscreteValuationRing.maximalIdeal A)
local notation "vB" =>
  IsDedekindDomain.HeightOneSpectrum.valuation L (IsDiscreteValuationRing.maximalIdeal B)
local notation "VA" => Valuation.valuationSubring vA
local notation "VB" => Valuation.valuationSubring vB
local notation "kA" => ResidueField VA
local notation "kB" => ResidueField VB

/-- The actual coefficient fraction map preserves normalized valuations. -/
theorem completionFractionMap_valuation (x : K) :
    vB (completionFractionMap R ι p x) = vA x :=
  IsDiscreteValuationRing.valuation_map_of_map_irreducible
    (completionMap R ι p) (AdicCompletion.irreducible_algebraMap R p Fact.out)
    (irreducible_completionAlgebra_uniformizer R ι p) K L
    (completionFractionMap R ι p) (completionFractionMap_algebraMap R ι p) x

/-- The original uniformizer is normalized to additive value one. -/
theorem completionFractionMap_uniformizer_value :
    vA (algebraMap A K (algebraMap R A p)) = WithZero.exp (-1 : ℤ) := by
  rw [IsDedekindDomain.HeightOneSpectrum.valuation_of_algebraMap]
  exact (IsDiscreteValuationRing.maximalIdeal A).intValuation_singleton
    (AdicCompletion.irreducible_algebraMap R p Fact.out).ne_zero
    (AdicCompletion.irreducible_algebraMap R p Fact.out).maximalIdeal_eq

/-- The literal integral restriction required by the leading-residue argument. -/
abbrev completionIntegerMap : VA →+* VB :=
  Valuation.integerMap vA vB (completionFractionMap R ι p) (completionFractionMap_valuation R ι p)

/-- The native and literal integral maps agree as ring homomorphisms. -/
theorem completionIntegerMap_eq :
    completionIntegerMap R ι p =
      IsDiscreteValuationRing.sameUniformizerValuationSubringMap (completionMap R ι p) K L := by
  apply RingHom.ext
  intro x
  apply Subtype.ext
  exact (IsDiscreteValuationRing.coe_sameUniformizerValuationSubringMap
    (completionMap R ι p) K L (completionFractionMap R ι p)
    (completionFractionMap_algebraMap R ι p) x).symm

theorem completionIntegerMap_isLocalHom : IsLocalHom (completionIntegerMap R ι p) := by
  rw [completionIntegerMap_eq]
  exact IsDiscreteValuationRing.sameUniformizerValuationSubringMap_isLocalHom
    (completionMap R ι p) (AdicCompletion.irreducible_algebraMap R p Fact.out)
    (irreducible_completionAlgebra_uniformizer R ι p) K L

attribute [local instance] completionIntegerMap_isLocalHom

/-- Source valuation-ring residues, through the native completion, are the original residues. -/
def completedValuationResidueEquiv : kA ≃+* ResidueField R :=
  (IsDiscreteValuationRing.valuationResidueEquiv A K).trans
    (AdicCompletion.residueFieldEquiv R)

/-- Target valuation-ring residues are the original rational residues, via the native completion. -/
def parameterValuationResidueEquiv :
    kB ≃+* FractionRing (MvPolynomial ι (ResidueField R)) :=
  (IsDiscreteValuationRing.valuationResidueEquiv B L).trans
    (completionResidueEquiv R ι p)

/-- The literal integral restriction has the already-proved native residue scalar square. -/
theorem parameterValuationResidueEquiv_coeff (x : kA) :
    parameterValuationResidueEquiv R ι p
        (ResidueField.map (completionIntegerMap R ι p) x) =
      algebraMap (ResidueField R) (FractionRing (MvPolynomial ι (ResidueField R)))
        (completedValuationResidueEquiv R x) := by
  let : IsLocalHom (completionMap R ι p) := completionMap_isLocalHom R ι p
  let : IsLocalHom
      (IsDiscreteValuationRing.sameUniformizerValuationSubringMap (completionMap R ι p) K L) :=
    IsDiscreteValuationRing.sameUniformizerValuationSubringMap_isLocalHom
      (completionMap R ι p) (AdicCompletion.irreducible_algebraMap R p Fact.out)
      (irreducible_completionAlgebra_uniformizer R ι p) K L
  change completionResidueEquiv R ι p
    (IsDiscreteValuationRing.valuationResidueEquiv B L
      (ResidueField.map (completionIntegerMap R ι p) x)) = _
  simp only [completionIntegerMap_eq]
  rw [show IsDiscreteValuationRing.valuationResidueEquiv B L
      (ResidueField.map
        (IsDiscreteValuationRing.sameUniformizerValuationSubringMap (completionMap R ι p) K L) x) =
      ResidueField.map (completionMap R ι p)
        (IsDiscreteValuationRing.valuationResidueEquiv A K x) from
    IsDiscreteValuationRing.valuationResidueEquiv_map (completionMap R ι p)
      (AdicCompletion.irreducible_algebraMap R p Fact.out)
      (irreducible_completionAlgebra_uniformizer R ι p) K L x]
  exact completionResidueEquiv_coeff R ι p _

/-- Rational residue coordinates over the literal source valuation-ring residue field. -/
def valuationRationalResidueEquiv : kB ≃+* FractionRing (MvPolynomial ι kA) :=
  (parameterValuationResidueEquiv R ι p).trans
    (IsFractionRing.ringEquivOfRingEquiv
      (MvPolynomial.mapEquiv ι (completedValuationResidueEquiv R).symm))

/-- Coefficients in the rational-residue comparison are the literal integral residue map. -/
theorem valuationRationalResidueEquiv_coeff (x : kA) :
    valuationRationalResidueEquiv R ι p
        (ResidueField.map (completionIntegerMap R ι p) x) =
      algebraMap kA (FractionRing (MvPolynomial ι kA)) x := by
  change IsFractionRing.ringEquivOfRingEquiv
    (MvPolynomial.mapEquiv ι (completedValuationResidueEquiv R).symm)
      (parameterValuationResidueEquiv R ι p
        (ResidueField.map (completionIntegerMap R ι p) x)) = _
  rw [parameterValuationResidueEquiv_coeff,
    IsScalarTower.algebraMap_apply (ResidueField R)
      (MvPolynomial ι (ResidueField R)) (FractionRing (MvPolynomial ι (ResidueField R))),
    IsFractionRing.ringEquivOfRingEquiv_algebraMap]
  simp only [MvPolynomial.algebraMap_eq, MvPolynomial.mapEquiv_apply,
    MvPolynomial.map_C, RingEquiv.coe_toRingHom, RingEquiv.symm_apply_apply]
  exact (IsScalarTower.algebraMap_apply kA (MvPolynomial ι kA)
    (FractionRing (MvPolynomial ι kA)) x).symm

/-- The actual variables as elements of the literal target valuation ring. -/
def completedIntegerVariable (i : ι) : VB :=
  IsDiscreteValuationRing.equivValuationSubring («A» := B) («K» := L)
    (completedVariable R ι p i)

/-- The literal valuation-ring residue retains the original rational variable. -/
theorem valuationRationalResidueEquiv_variable (i : ι) :
    valuationRationalResidueEquiv R ι p (residue VB (completedIntegerVariable R ι p i)) =
      algebraMap (MvPolynomial ι kA) (FractionRing (MvPolynomial ι kA)) (MvPolynomial.X i) := by
  change IsFractionRing.ringEquivOfRingEquiv
    (MvPolynomial.mapEquiv ι (completedValuationResidueEquiv R).symm)
      (completionResidueEquiv R ι p
        (IsDiscreteValuationRing.valuationResidueEquiv B L
          (residue VB (IsDiscreteValuationRing.equivValuationSubring
            («A» := B) («K» := L) (completedVariable R ι p i))))) = _
  rw [IsDiscreteValuationRing.valuationResidueEquiv_residue,
    completionResidueEquiv_variable, IsFractionRing.ringEquivOfRingEquiv_algebraMap,
    MvPolynomial.mapEquiv_apply, MvPolynomial.map_X]

/-- Every original parameter has valuation one, not merely valuation at most one. -/
theorem completedIntegerVariable_value (i : ι) :
    vB (completedIntegerVariable R ι p i : L) = 1 := by
  rw [completedIntegerVariable, IsDiscreteValuationRing.coe_equivValuationSubring]
  apply (IsDedekindDomain.HeightOneSpectrum.valuation_eq_one_iff_notMem
    (IsDiscreteValuationRing.maximalIdeal B)).mpr
  change completedVariable R ι p i ∉ maximalIdeal B
  apply notMem_maximalIdeal.mpr
  apply (residue_ne_zero_iff_isUnit _).mp
  intro h
  have hz := congrArg (completionResidueEquiv R ι p) h
  rw [completionResidueEquiv_variable, map_zero] at hz
  apply MvPolynomial.X_ne_zero (R := ResidueField R) i
  apply IsFractionRing.injective (MvPolynomial ι (ResidueField R))
    (FractionRing (MvPolynomial ι (ResidueField R)))
  simpa only [map_zero] using hz

/-- The polynomial algebra structure is transported through the constructed residue equivalence. -/
abbrev valuationResiduePolynomialAlgebra : Algebra (MvPolynomial ι kA) kB :=
  ((valuationRationalResidueEquiv R ι p).symm.toRingHom.comp
    (algebraMap (MvPolynomial ι kA) (FractionRing (MvPolynomial ι kA)))).toAlgebra

attribute [local instance] valuationResiduePolynomialAlgebra

/-- The residue field is a genuine fraction ring for this exact polynomial action. -/
theorem valuationResidue_isFractionRing : IsFractionRing (MvPolynomial ι kA) kB := by
  let e : FractionRing (MvPolynomial ι kA) ≃ₐ[MvPolynomial ι kA] kB :=
    { (valuationRationalResidueEquiv R ι p).symm with commutes' := fun _ => rfl }
  exact IsFractionRing.of_algEquiv e

/-- The scalar square used by the leading-residue theorem, with its literal integerMap. -/
theorem residue_completionIntegerMap (x : VA) :
    residue VB (completionIntegerMap R ι p x) =
      algebraMap (MvPolynomial ι kA) kB (MvPolynomial.C (residue VA x)) := by
  have h : valuationRationalResidueEquiv R ι p
      (residue VB (completionIntegerMap R ι p x)) =
      algebraMap kA (FractionRing (MvPolynomial ι kA)) (residue VA x) :=
    (congrArg (valuationRationalResidueEquiv R ι p)
      (ResidueField.map_residue (completionIntegerMap R ι p) x).symm).trans
        (valuationRationalResidueEquiv_coeff R ι p (residue VA x))
  exact eq_symm_polynomialScalar ι (valuationRationalResidueEquiv R ι p)
    (residue VB (completionIntegerMap R ι p x)) (residue VA x) h


/-- The variable square for precisely the same polynomial fraction-ring action. -/
theorem residue_completedIntegerVariable (i : ι) :
    residue VB (completedIntegerVariable R ι p i) =
      algebraMap (MvPolynomial ι kA) kB (MvPolynomial.X i) := by
  apply (valuationRationalResidueEquiv R ι p).injective
  change valuationRationalResidueEquiv R ι p
      (residue VB (completedIntegerVariable R ι p i)) =
    valuationRationalResidueEquiv R ι p ((valuationRationalResidueEquiv R ι p).symm _)
  rw [valuationRationalResidueEquiv_variable, RingEquiv.apply_symm_apply]

end ParameterLocalization
