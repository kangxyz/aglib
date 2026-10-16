/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.Algebra.Homology.Coproduct.Homology
public import Aglib.Algebra.Homology.Simplex.Relative.Weights.Coproduct
public import Mathlib.Algebra.Category.ModuleCat.AB

/-!
# Original Laurent tuple homology decomposed into its actual weights

The original raw complex is the native coproduct of relative-simplex weight
complexes. Exactness of module coproducts therefore identifies its original
homology with the original coproduct of their homology objects. The equations
below retain the actual single-monomial maps and native summand inclusions.
-/

@[expose] public section

noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true

open CategoryTheory CategoryTheory.Limits HomologicalComplex AlgebraicTopology

universe u v

namespace MvPolynomial

variable {ι : Type v} [Finite ι] (R : Type u) [CommRing R]

/-- Original Laurent homology is the actual coproduct of the unchanged
relative-simplex weight homology objects, in independent scalar/vertex universes. -/
def coordinateLaurentTupleHomologyWeightsIso (d : ℤ) (n : ℕ) :
    (coordinateLaurentTupleComplex (ι := ι) R d).homology n ≅
      ∐ (fun e : coordinateLaurentWeight (ι := ι) d =>
        (RelativeSimplex.complex R (coordinateNegativeSupport e.val)).homology n) := by
  letI : AB4OfSize.{v} AddCommGrpCat.{max u v} := AB4OfSize_shrink.{v, u} _
  letI : HasExactColimitsOfShape (Discrete (coordinateLaurentWeight (ι := ι) d))
      (ModuleCat.{max u v} R) :=
    HasExactColimitsOfShape.domain_of_functor (Discrete (coordinateLaurentWeight (ι := ι) d))
      (forget₂ (ModuleCat.{max u v} R) AddCommGrpCat.{max u v})
  exact (homologyFunctor (ModuleCat.{max u v} R) (.up ℕ) n).mapIso
    (coordinateLaurentTupleComplexWeightsIso R d) ≪≫
      coproductHomologyIso (fun e : coordinateLaurentWeight (ι := ι) d =>
        RelativeSimplex.complex R (coordinateNegativeSupport e.val)) n

/-- The actual weight-homology comparison retains each original
single-monomial chain map and original summand inclusion. -/
@[reassoc (attr := simp)]
theorem coordinateLaurentWeightComplexMap_homology_weightsIso_hom (d : ℤ) (n : ℕ)
    (e : coordinateLaurentWeight (ι := ι) d) :
    homologyMap (coordinateLaurentWeightComplexMap R d e) n ≫
        (coordinateLaurentTupleHomologyWeightsIso R d n).hom =
      Sigma.ι (fun e : coordinateLaurentWeight (ι := ι) d =>
        (RelativeSimplex.complex R (coordinateNegativeSupport e.val)).homology n) e := by
  let : AB4OfSize.{v} AddCommGrpCat.{max u v} := AB4OfSize_shrink.{v, u} _
  let : HasExactColimitsOfShape (Discrete (coordinateLaurentWeight (ι := ι) d))
      (ModuleCat.{max u v} R) :=
    HasExactColimitsOfShape.domain_of_functor (Discrete (coordinateLaurentWeight (ι := ι) d))
      (forget₂ (ModuleCat.{max u v} R) AddCommGrpCat.{max u v})
  dsimp only [coordinateLaurentTupleHomologyWeightsIso, Iso.trans_hom, Functor.mapIso_hom,
    homologyFunctor]
  rw [← Category.assoc, ← homologyMap_comp,
    coordinateLaurentWeightComplexMap_weightsIso_hom]
  exact homologyMap_sigma_ι_coproductHomologyIso_hom _ e n

/-- The original raw Laurent homology, expressed as the native dependent
finitely supported sum of its unchanged weight homology modules. -/
def coordinateLaurentTupleHomologyWeightsEquiv (d : ℤ) (n : ℕ) :
    (coordinateLaurentTupleComplex (ι := ι) R d).homology n ≃ₗ[R]
      (Π₀ e : coordinateLaurentWeight (ι := ι) d,
        (RelativeSimplex.complex R (coordinateNegativeSupport e.val)).homology n) := by
  classical
  exact (coordinateLaurentTupleHomologyWeightsIso R d n ≪≫
    ModuleCat.coprodIsoDirectSum (fun e : coordinateLaurentWeight (ι := ι) d =>
      (RelativeSimplex.complex R (coordinateNegativeSupport e.val)).homology n)).toLinearEquiv

open Classical in
/-- The dependent-sum comparison sends the original monomial homology map to
the literal native single summand. -/
theorem coordinateLaurentTupleHomologyWeightsEquiv_homologyMap (d : ℤ) (n : ℕ)
    (e : coordinateLaurentWeight (ι := ι) d)
    (x : (RelativeSimplex.complex R (coordinateNegativeSupport e.val)).homology n) :
    coordinateLaurentTupleHomologyWeightsEquiv (ι := ι) R d n
        (homologyMap (coordinateLaurentWeightComplexMap R d e) n x) =
      DFinsupp.single e x := by
  classical
  change (homologyMap (coordinateLaurentWeightComplexMap R d e) n ≫
      (coordinateLaurentTupleHomologyWeightsIso R d n).hom ≫
      (ModuleCat.coprodIsoDirectSum _).hom) x = _
  rw [coordinateLaurentWeightComplexMap_homology_weightsIso_hom_assoc,
    ModuleCat.ι_coprodIsoDirectSum_hom]
  rfl

end MvPolynomial
