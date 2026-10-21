/-
Copyright (c) 2026 kangxyz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.RingTheory.DiscreteValuationRing.ParameterResidue
public import Mathlib.RingTheory.AlgebraicIndependent.Defs

/-!
# Generic residue coordinates in the actual parameter localization

The residues of the original polynomial variables are algebraically independent.
Thus every prescribed finite collection of nonzero polynomial conditions holds
at these same actual coordinates, without assuming the original residue field
is infinite or has a common point satisfying the conditions.
-/

@[expose] public noncomputable section

open IsLocalRing

universe u v

namespace ParameterLocalization

variable (R : Type u) [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]
  (ι : Type v) (p : R) [Fact (Irreducible p)]

attribute [local instance] algebraMap_isLocalHom

/-- Residues of the original variables in the native parameter localization. -/
def genericResidue (i : ι) : ResidueField (Ring R ι p) :=
  residue (Ring R ι p) (algebraMap (MvPolynomial ι R) (Ring R ι p) (MvPolynomial.X i))

/-- The actual evaluation map becomes the native fraction-ring inclusion. -/
theorem residueFieldAlgEquiv_comp_aeval_genericResidue :
    (residueFieldAlgEquiv R ι p).toAlgHom.comp (MvPolynomial.aeval (genericResidue R ι p)) =
      IsScalarTower.toAlgHom (ResidueField R) (MvPolynomial ι (ResidueField R))
        (FractionRing (MvPolynomial ι (ResidueField R))) := by
  ext i
  change residueFieldAlgEquiv R ι p (MvPolynomial.aeval (genericResidue R ι p)
    (MvPolynomial.X i)) = _
  rw [MvPolynomial.aeval_X]
  exact residueFieldAlgEquiv_X R ι p i

/-- Evaluation at the actual coordinates agrees with polynomial inclusion under the comparison. -/
theorem residueFieldAlgEquiv_aeval_genericResidue (f : MvPolynomial ι (ResidueField R)) :
    residueFieldAlgEquiv R ι p (MvPolynomial.aeval (genericResidue R ι p) f) =
      algebraMap (MvPolynomial ι (ResidueField R))
        (FractionRing (MvPolynomial ι (ResidueField R))) f :=
  DFunLike.congr_fun (residueFieldAlgEquiv_comp_aeval_genericResidue R ι p) f

/-- The actual residue coordinates are algebraically independent over the original residue field. -/
theorem algebraicIndependent_genericResidue :
    AlgebraicIndependent (ResidueField R) (genericResidue R ι p) := by
  intro f g h
  apply FaithfulSMul.algebraMap_injective (MvPolynomial ι (ResidueField R))
    (FractionRing (MvPolynomial ι (ResidueField R)))
  have he := congrArg (residueFieldAlgEquiv R ι p) h
  simpa only [residueFieldAlgEquiv_aeval_genericResidue] using he

/-- Every nonzero polynomial stays nonzero at these actual residue coordinates. -/
theorem aeval_genericResidue_ne_zero (f : MvPolynomial ι (ResidueField R)) (hf : f ≠ 0) :
    MvPolynomial.aeval (genericResidue R ι p) f ≠ 0 := by
  intro h
  exact hf ((algebraicIndependent_genericResidue R ι p).eq_zero_of_aeval_eq_zero f h)

/-- All finitely many nonzero conditions hold simultaneously at the same coordinates. -/
theorem aeval_genericResidue_finset_ne_zero (s : Finset (MvPolynomial ι (ResidueField R)))
    (hs : ∀ f ∈ s, f ≠ 0) :
    ∀ f ∈ s, MvPolynomial.aeval (genericResidue R ι p) f ≠ 0 := by
  intro f hf
  exact aeval_genericResidue_ne_zero R ι p f (hs f hf)

end ParameterLocalization
