/-
Copyright (c) 2026 kangxyz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.RingTheory.DiscreteValuationRing.ParameterLocalization
public import Aglib.RingTheory.LocalRing.ResidueField.PolynomialCentre

/-! # Actual parameter points with independent residual coordinates

The point extends to the native parameter localization because its centre is
exactly the coefficient uniformizer prime. The resulting same-uniformizer map
is injective, so the original polynomial coordinates are algebraically independent.
-/

@[expose] public noncomputable section

open IsLocalRing MvPolynomial

namespace ParameterLocalization

variable {R S ι : Type*} [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]
variable [CommRing S] [IsDomain S] [IsDiscreteValuationRing S]
variable [Algebra R S] [IsLocalHom (algebraMap R S)]
variable (p : R) [Fact (Irreducible p)] (z : ι → S)
variable (hz : AlgebraicIndependent (ResidueField R) (fun i => residue S (z i)))

/-- Extend the actual parameter evaluation to its coefficient-uniformizer localization. -/
def point : Ring R ι p →ₐ[R] S :=
  IsLocalization.liftAlgHom (M := (parameterIdeal R ι p).primeCompl)
    (f := aeval z) (fun u => by
      by_contra h
      have hu : (aeval z : MvPolynomial ι R →ₐ[R] S)
          (u : MvPolynomial ι R) ∈ maximalIdeal S := h
      have hc := comap_maximalIdeal_aeval_eq_span_C p
        (Fact.out : Irreducible p).maximalIdeal_eq z hz
      have hm : (u : MvPolynomial ι R) ∈ parameterIdeal R ι p := by
        change (u : MvPolynomial ι R) ∈ Ideal.span {C p}
        rw [← hc]
        exact hu
      exact u.property hm)

/-- The extended point agrees with the original polynomial evaluation. -/
@[simp] theorem point_algebraMap (f : MvPolynomial ι R) :
    point p z hz (algebraMap (MvPolynomial ι R) (Ring R ι p) f) = aeval z f :=
  IsLocalization.lift_eq _ f

variable [Finite ι]

/-- The extended parameter point is injective when the original uniformizer stays a uniformizer. -/
theorem point_injective (hpS : Irreducible (algebraMap R S p)) :
    Function.Injective (point p z hz) := by
  let : IsDiscreteValuationRing (Ring R ι p) := isDiscreteValuationRing R ι p
  apply IsDiscreteValuationRing.injective_of_map_irreducible
    (point p z hz).toRingHom (uniformizer_irreducible R ι p)
  change Irreducible (point p z hz (algebraMap R (Ring R ι p) p))
  rw [AlgHom.commutes]
  exact hpS

include hz in
/-- Residually independent coordinates are already algebraically independent over the source DVR. -/
theorem algebraicIndependent_of_residue (hpS : Irreducible (algebraMap R S p)) :
    AlgebraicIndependent R z := by
  intro f g h
  apply FaithfulSMul.algebraMap_injective (MvPolynomial ι R) (Ring R ι p)
  apply point_injective p z hz hpS
  simpa only [point_algebraMap] using h

end ParameterLocalization
