/-
Copyright (c) 2026 Motivic Cohomology contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Mathlib.RingTheory.LocalRing.ResidueField.Fiber
public import Mathlib.RingTheory.LocalRing.ResidueField.Instances
public import Mathlib.RingTheory.Artinian.Module
public import Mathlib.RingTheory.Length
public import Mathlib.RingTheory.TensorProduct.Finite

/-!
# The closed fiber of a finite algebra over a local ring

A module-finite algebra over a local ring has finitely many maximal ideals.
Each contracts to the base maximal ideal and has finite residue degree.
Only the actual special fiber is made Artinian; the algebra itself need not
be Artinian. These are the geometric finiteness hypotheses in Stacks 02M0.
-/

@[expose] public section

noncomputable section

open scoped TensorProduct

namespace Module

universe u v

variable (R : Type u) (S : Type v) [CommRing R] [IsLocalRing R]
  [CommRing S] [Algebra R S] [Module.Finite R S]

/-- Every maximal point of a finite algebra lies over the closed point of the local base. -/
theorem finiteAlgebra_maximal_under (p : MaximalSpectrum S) :
    p.asIdeal.under R = IsLocalRing.maximalIdeal R :=
  IsLocalRing.eq_maximalIdeal
    (Ideal.isMaximal_under_of_isIntegral_of_isMaximal p.asIdeal)

/-- The actual closed fiber is finite dimensional and hence Artinian. -/
theorem finiteAlgebra_specialFiber_artinian :
    IsArtinianRing ((IsLocalRing.maximalIdeal R).Fiber S) := by
  change IsArtinianRing ((IsLocalRing.maximalIdeal R).ResidueField ⊗[R] S)
  exact IsArtinianRing.of_finite (IsLocalRing.maximalIdeal R).ResidueField _

include R in
/-- A finite algebra over a local base has finitely many maximal points,
by injection into the prime spectrum of the actual special fiber. -/
theorem finiteAlgebra_maximalSpectrum_finite : Finite (MaximalSpectrum S) := by
  have := finiteAlgebra_specialFiber_artinian R S
  have : Finite ((IsLocalRing.maximalIdeal R).primesOver S) :=
    (PrimeSpectrum.primesOverOrderIsoFiber R S (IsLocalRing.maximalIdeal R)).finite_iff.mpr
      inferInstance
  let f : MaximalSpectrum S → (IsLocalRing.maximalIdeal R).primesOver S :=
    fun p => ⟨p.asIdeal, p.isMaximal.isPrime, ⟨(finiteAlgebra_maximal_under R S p).symm⟩⟩
  exact _root_.Finite.of_injective f fun p q h => MaximalSpectrum.ext (congrArg Subtype.val h)

attribute [local instance] Ideal.Quotient.field

/-- The maximal quotient used to compute the degree is canonically the
actual residue field of the prime localization, with its literal S-action. -/
def finiteAlgebraResidueQuotientEquiv (p : MaximalSpectrum S) :
    (S ⧸ p.asIdeal) ≃ₐ[S] p.asIdeal.ResidueField :=
  AlgEquiv.ofBijective (IsScalarTower.toAlgHom S (S ⧸ p.asIdeal) p.asIdeal.ResidueField)
    p.asIdeal.bijective_algebraMap_quotient_residueField

/-- The literal maximal quotient is a finite extension of the base residue field. -/
theorem finiteAlgebra_residue_finite (p : MaximalSpectrum S) :
    Module.Finite (IsLocalRing.ResidueField R) (S ⧸ p.asIdeal) := by
  have : Module.Finite R (S ⧸ p.asIdeal) := Module.Finite.trans S (S ⧸ p.asIdeal)
  infer_instance

/-- The degree used below is the dimension of the literal maximal quotient
over the residue field of the local base. -/
def finiteAlgebraResidueDegree (p : MaximalSpectrum S) : ℕ :=
  Module.finrank (IsLocalRing.ResidueField R) (S ⧸ p.asIdeal)

/-- A maximal quotient has base length equal to its finite residue degree. -/
theorem finiteAlgebra_residue_length (p : MaximalSpectrum S) :
    Module.length R (S ⧸ p.asIdeal) = (finiteAlgebraResidueDegree R S p : ℕ∞) := by
  have := finiteAlgebra_residue_finite R S p
  rw [Module.length_eq_of_surjective (IsLocalRing.residue_surjective (R := R)),
    Module.length_eq_finrank]
  rfl

end Module
