/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.Algebra.Homology.Simplex.Relative.Weights.Maps
public import Mathlib.Algebra.Category.ModuleCat.Products
public import Mathlib.Algebra.Category.ModuleCat.Colimits
public import Mathlib.Algebra.Homology.HomologicalComplexLimits
public import Mathlib.CategoryTheory.Limits.FunctorCategory.Basic
public import Mathlib.CategoryTheory.Limits.Preserves.Shapes.Products

/-!
# The original Laurent tuple complex as the actual coproduct of its weights

The native finite term exchange proves that the original single-weight maps
exhibit the raw Laurent cosimplicial object as the actual discrete coproduct
of the unchanged relative-simplex cosimplicial objects. The native alternating
coface-map functor preserves this coproduct, since its degree evaluations are
the original cosimplicial evaluations. This gives an actual complex isomorphism
to the categorical coproduct, normalized by the original single-monomial maps.
-/

@[expose] public section

noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true

open CategoryTheory CategoryTheory.Limits AlgebraicTopology
open scoped Simplicial

universe u v

namespace MvPolynomial

variable {ι : Type v} (R : Type u) [CommRing R]

/-- The original single-weight cosimplicial maps form a cofan on the raw object. -/
def coordinateLaurentWeightCofan (d : ℤ) :
    Cofan (fun e : coordinateLaurentWeight (ι := ι) d =>
      RelativeSimplex.cosimplicial R (coordinateNegativeSupport e.val)) :=
  Cofan.mk (coordinateLaurentTupleCosimplicial (ι := ι) R d)
    (coordinateLaurentWeightCosimplicialMap R d)

/-- The native finite weight exchange proves the actual raw cosimplicial
cofan is colimiting. -/
def coordinateLaurentWeightCofanIsColimit [Finite ι] (d : ℤ) :
    IsColimit (coordinateLaurentWeightCofan (ι := ι) R d) := by
  classical
  apply evaluationJointlyReflectsColimits
  intro n
  let Z := fun e : coordinateLaurentWeight (ι := ι) d =>
    ModuleCat.of R (RelativeSimplex.Cochains R (coordinateNegativeSupport e.val) n.len)
  let E := (coordinateLaurentTupleWeightsEquiv (ι := ι) R d n.len).toModuleIso
  have hc : IsColimit (Cofan.mk
      (ModuleCat.of R (coordinateLaurentTupleCochains (ι := ι) R d n.len))
      (fun e => ModuleCat.ofHom (coordinateLaurentTupleWeightInjection R d e n.len))) := by
    have ec : Cofan.mk
        (ModuleCat.of R (coordinateLaurentTupleCochains (ι := ι) R d n.len))
        (fun e => ModuleCat.ofHom (coordinateLaurentTupleWeightInjection R d e n.len)) ≅
          ModuleCat.coproductCocone Z := by
      refine Cocone.ext E ?_
      rintro ⟨e⟩
      apply ModuleCat.hom_ext
      apply LinearMap.ext
      intro x
      exact coordinateLaurentTupleWeightsEquiv_injection R d e n.len x
    exact (ModuleCat.coproductCoconeIsColimit Z).ofIsoColimit ec.symm
  exact (isColimitMapCoconeCofanMkEquiv
    ((evaluation SimplexCategory (ModuleCat.{max u v} R)).obj n)
    (fun e : coordinateLaurentWeight (ι := ι) d =>
      RelativeSimplex.cosimplicial R (coordinateNegativeSupport e.val))
    (coordinateLaurentWeightCosimplicialMap R d)).symm hc

/-- Original single-weight chain maps, as a cofan on the unchanged raw complex. -/
def coordinateLaurentWeightComplexCofan (d : ℤ) :
    Cofan (fun e : coordinateLaurentWeight (ι := ι) d =>
      RelativeSimplex.complex R (coordinateNegativeSupport e.val)) :=
  Cofan.mk (coordinateLaurentTupleComplex (ι := ι) R d) (coordinateLaurentWeightComplexMap R d)

/-- The original Laurent complex is the actual coproduct of the original
relative-simplex weight complexes. -/
def coordinateLaurentWeightComplexCofanIsColimit [Finite ι] (d : ℤ) :
    IsColimit (coordinateLaurentWeightComplexCofan (ι := ι) R d) := by
  have : PreservesColimitsOfShape (Discrete (coordinateLaurentWeight (ι := ι) d))
      (alternatingCofaceMapComplex (ModuleCat.{max u v} R)) := by
    apply HomologicalComplex.preservesColimitsOfShape_of_eval
    intro n
    exact inferInstanceAs (PreservesColimitsOfShape
      (Discrete (coordinateLaurentWeight (ι := ι) d))
      ((evaluation SimplexCategory (ModuleCat.{max u v} R)).obj ⦋n⦌))
  exact isColimitCofanMkObjOfIsColimit (alternatingCofaceMapComplex (ModuleCat.{max u v} R))
    (fun e : coordinateLaurentWeight (ι := ι) d =>
      RelativeSimplex.cosimplicial R (coordinateNegativeSupport e.val))
    (coordinateLaurentWeightCosimplicialMap R d) (coordinateLaurentWeightCofanIsColimit R d)

/-- The canonical actual chain isomorphism from the raw Laurent tuple complex
to the categorical coproduct of its unchanged relative-simplex weights. -/
def coordinateLaurentTupleComplexWeightsIso [Finite ι] (d : ℤ) :
    coordinateLaurentTupleComplex (ι := ι) R d ≅
      ∐ (fun e : coordinateLaurentWeight (ι := ι) d =>
        RelativeSimplex.complex R (coordinateNegativeSupport e.val)) :=
  (coordinateLaurentWeightComplexCofanIsColimit R d).coconePointUniqueUpToIso
    (colimit.isColimit _)

/-- The canonical weight decomposition is normalized by the original native
single-monomial chain maps, with no replacement comparison premise. -/
@[reassoc (attr := simp)]
theorem coordinateLaurentWeightComplexMap_weightsIso_hom [Finite ι] (d : ℤ)
    (e : coordinateLaurentWeight (ι := ι) d) :
    coordinateLaurentWeightComplexMap R d e ≫ (coordinateLaurentTupleComplexWeightsIso R d).hom =
      Sigma.ι (fun e : coordinateLaurentWeight (ι := ι) d =>
        RelativeSimplex.complex R (coordinateNegativeSupport e.val)) e :=
  (coordinateLaurentWeightComplexCofanIsColimit R d).comp_coconePointUniqueUpToIso_hom
    (colimit.isColimit _) (Discrete.mk e)

end MvPolynomial
