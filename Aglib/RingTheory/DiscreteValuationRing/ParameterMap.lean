/-
Copyright (c) 2026 kangxyz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.RingTheory.DiscreteValuationRing.ParameterPoint
public import Aglib.RingTheory.DiscreteValuationRing.ParameterGenericResidue
public import Mathlib.RingTheory.AlgebraicIndependent.Basic

/-!
# Compatible generic parameter extension of source and target DVRs

The source and target are the existing native parameter localizations. The map
extends the original coefficient map and preserves the same polynomial variables.
-/

@[expose] public noncomputable section

open IsLocalRing MvPolynomial

universe u v w

namespace ParameterLocalization

variable (R : Type u) (S : Type v) [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]
  [CommRing S] [IsDomain S] [IsDiscreteValuationRing S] [Algebra R S]
  (ι : Type w) (p : R) [Fact (Irreducible p)]
  [Fact (Irreducible (algebraMap R S p))]

include p in
theorem baseMap_isLocalHom : IsLocalHom (algebraMap R S) :=
  IsDiscreteValuationRing.isLocalHom_of_map_irreducible _
    (Fact.out : Irreducible p) (Fact.out : Irreducible (algebraMap R S p))

attribute [local instance] algebraMap_isLocalHom isDiscreteValuationRing

local notation "L" => Ring R ι p
local notation "M" => Ring S ι (algebraMap R S p)

/-- The actual composite coefficient map is local. -/
theorem targetCoefficientMap_isLocalHom : IsLocalHom (algebraMap R M) := by
  let : IsLocalHom (algebraMap R S) := baseMap_isLocalHom R S p
  rw [IsScalarTower.algebraMap_eq R S M]
  infer_instance

/-- The actual target variables have independent residues even over the source residue field. -/
theorem algebraicIndependent_targetGenericResidue :
    letI : IsLocalHom (algebraMap R S) := baseMap_isLocalHom R S p
    letI : IsLocalHom (algebraMap R M) := targetCoefficientMap_isLocalHom R S ι p
    AlgebraicIndependent (ResidueField R) (genericResidue S ι (algebraMap R S p)) := by
  let : IsLocalHom (algebraMap R S) := baseMap_isLocalHom R S p
  let : IsLocalHom (algebraMap R M) := targetCoefficientMap_isLocalHom R S ι p
  exact (algebraicIndependent_genericResidue S ι (algebraMap R S p)).restrictScalars
    (FaithfulSMul.algebraMap_injective (ResidueField R) (ResidueField S))

variable [Finite ι]

/-- The original coefficient map extended to the same generic variables on both sides. -/
def parameterMap : L →ₐ[R] M := by
  let : IsLocalHom (algebraMap R S) := baseMap_isLocalHom R S p
  let : IsLocalHom (algebraMap R M) := targetCoefficientMap_isLocalHom R S ι p
  exact point p (fun i : ι => algebraMap (MvPolynomial ι S) M (X i))
    (algebraicIndependent_targetGenericResidue R S ι p)

/-- The literal polynomial coefficient-change square. -/
@[simp] theorem parameterMap_polynomial (f : MvPolynomial ι R) :
    parameterMap R S ι p (algebraMap (MvPolynomial ι R) L f) =
      algebraMap (MvPolynomial ι S) M (MvPolynomial.map (algebraMap R S) f) := by
  let : IsLocalHom (algebraMap R S) := baseMap_isLocalHom R S p
  let : IsLocalHom (algebraMap R M) := targetCoefficientMap_isLocalHom R S ι p
  have hpoint : parameterMap R S ι p (algebraMap (MvPolynomial ι R) L f) =
      aeval (fun i : ι => algebraMap (MvPolynomial ι S) M (X i)) f :=
    point_algebraMap p (fun i : ι => algebraMap (MvPolynomial ι S) M (X i))
      (algebraicIndependent_targetGenericResidue R S ι p) f
  rw [hpoint]
  have he : (aeval (fun i : ι => algebraMap (MvPolynomial ι S) M (X i))).toRingHom =
      (algebraMap (MvPolynomial ι S) M).comp (MvPolynomial.map (algebraMap R S)) := by
    apply MvPolynomial.ringHom_ext
    · intro r
      change aeval (fun i : ι => algebraMap (MvPolynomial ι S) M (X i)) (C r) =
        algebraMap (MvPolynomial ι S) M (MvPolynomial.map (algebraMap R S) (C r))
      rw [aeval_C, MvPolynomial.map_C]
      exact (IsScalarTower.algebraMap_apply R S M r).trans
        (IsScalarTower.algebraMap_apply S (MvPolynomial ι S) M (algebraMap R S r))
    · intro i
      change aeval (fun i : ι => algebraMap (MvPolynomial ι S) M (X i)) (X i) =
        algebraMap (MvPolynomial ι S) M (MvPolynomial.map (algebraMap R S) (X i))
      rw [aeval_X, MvPolynomial.map_X]
  exact DFunLike.congr_fun he f

theorem parameterMap_X (i : ι) :
    parameterMap R S ι p (algebraMap (MvPolynomial ι R) L (X i)) =
      algebraMap (MvPolynomial ι S) M (X i) := by
  rw [parameterMap_polynomial, MvPolynomial.map_X]

/-- The original uniformizer maps to its original image, then to the target localization. -/
theorem parameterMap_uniformizer :
    parameterMap R S ι p (algebraMap R L p) =
      algebraMap S M (algebraMap R S p) := by
  rw [AlgHom.commutes, IsScalarTower.algebraMap_apply R S M]

/-- The actual extended map preserves the uniformizer and hence is injective. -/
theorem parameterMap_injective : Function.Injective (parameterMap R S ι p) := by
  apply IsDiscreteValuationRing.injective_of_map_irreducible
    (parameterMap R S ι p).toRingHom (uniformizer_irreducible R ι p)
  change Irreducible (parameterMap R S ι p (algebraMap R L p))
  rw [parameterMap_uniformizer]
  exact uniformizer_irreducible S ι (algebraMap R S p)

/-- The actual extended map is local, not merely a map between abstract isomorphic fields. -/
theorem parameterMap_isLocalHom : IsLocalHom (parameterMap R S ι p).toRingHom := by
  apply IsDiscreteValuationRing.isLocalHom_of_map_irreducible
    (parameterMap R S ι p).toRingHom (uniformizer_irreducible R ι p)
  change Irreducible (parameterMap R S ι p (algebraMap R L p))
  rw [parameterMap_uniformizer]
  exact uniformizer_irreducible S ι (algebraMap R S p)

/-- Reduction retains the same literal polynomial coefficient-change square. -/
theorem residue_parameterMap_polynomial (f : MvPolynomial ι R) :
    residue M (parameterMap R S ι p (algebraMap (MvPolynomial ι R) L f)) =
      residue M (algebraMap (MvPolynomial ι S) M (MvPolynomial.map (algebraMap R S) f)) := by
  rw [parameterMap_polynomial]

/-- The actual generic target residues come from the corresponding source parameters. -/
theorem residue_parameterMap_X (i : ι) :
    residue M (parameterMap R S ι p (algebraMap (MvPolynomial ι R) L (X i))) =
      genericResidue S ι (algebraMap R S p) i := by
  rw [parameterMap_X]
  rfl

end ParameterLocalization
