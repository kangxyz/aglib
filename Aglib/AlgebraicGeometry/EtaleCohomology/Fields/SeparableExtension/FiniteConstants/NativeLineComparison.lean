/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.EtaleCohomology.Fields.SeparableExtension.FiniteConstants.BoundedComparison
public import Aglib.CategoryTheory.Abelian.Ext.OriginalComparison

/-! # Bounded field comparison on the original native projective-line map

The native line over-base-change isomorphism identifies the categorical field
base change with `P1_K`. Original cohomological composition retains the actual
inverse-image coefficient isomorphism in this change of presentation.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry.Scheme.EtaleCohomology.Proper

universe u

attribute [local instance] hasSheafifyLarge HasExt.standard

/-- Keep the original composition comparison at variable schemes before
specializing the native projective-line base-change isomorphism. -/
private theorem cohomologyPullback_bijective_of_iso_factor
    {X S T : Scheme.{u}} (g : S ⟶ X) (e : T ≅ S) (f : T ⟶ X)
    (he : e.hom ≫ g = f) (F : AbelianSheaf.{u, u + 1} X) (q : ℕ)
    (hg : Function.Bijective (cohomologyPullback.{u, u + 2, u + 2} g F q)) :
    Function.Bijective (cohomologyPullback.{u, u + 2, u + 2} f F q) :=
  by
  subst f
  exact Functor.extPrecompMap_bijective_of_equivalence_factor (inverseImage g)
    (inverseImage e.hom) (inverseImage (e.hom ≫ g)) (inverseImageComp g e.hom)
    ((inverseImageConstantIso g).inv.app (AddCommGrpCat.of (ULift.{u + 1} ℤ)))
    ((inverseImageConstantIso e.hom).inv.app (AddCommGrpCat.of (ULift.{u + 1} ℤ)))
    ((inverseImageConstantIso (e.hom ≫ g)).inv.app (AddCommGrpCat.of (ULift.{u + 1} ℤ)))
    (inverseImageComp_constant_inv g e.hom _) F q hg

variable (k K : Type u) [Field k] [Field K] [IsSepClosed k] [IsSepClosed K]
  [Algebra k K]

/-- The actual original native `P1_K → P1_k` map has bijective original
cohomology pullback for every bounded abelian coefficient, in every degree. -/
theorem projectiveLine_fieldMap_cohomologyPullback_bijective_of_killed
    (n : ℕ) (hn : n ≠ 0)
    (F : AbelianSheaf.{u, u + 1} (ProjectiveLine.projectiveP1 k))
    (hF : n • 𝟙 F = 0) (q : ℕ) :
    Function.Bijective (cohomologyPullback.{u, u + 2, u + 2}
      (AlgebraicGeometry.ProjectiveSpace.BinaryFormProduct.lineBaseChangeMap
        (algebraMap k K)) F q) := by
  let g : pullback (ProjectiveLine.structureMap k) (Spec.algebraMap k K) ⟶
      ProjectiveLine.projectiveP1 k :=
    pullback.fst (ProjectiveLine.structureMap k) (Spec.algebraMap k K)
  let e : ProjectiveLine.projectiveP1 K ≅
      pullback (ProjectiveLine.structureMap k) (Spec.algebraMap k K) :=
    (Over.forget (Spec (.of K))).mapIso
    (AlgebraicGeometry.ProjectiveSpace.BinaryFormProduct.lineOverBaseChangeIso (algebraMap k K))
  have he : e.hom ≫ g =
      AlgebraicGeometry.ProjectiveSpace.BinaryFormProduct.lineBaseChangeMap (algebraMap k K) :=
    AlgebraicGeometry.ProjectiveSpace.BinaryFormProduct.lineOverBaseChangeIso_hom_fst
      (algebraMap k K)
  have hg : Function.Bijective (cohomologyPullback.{u, u + 2, u + 2} g F q) :=
    projectiveLine_fieldExtension_cohomologyPullback_bijective_of_killed k K n hn F hF q
  exact cohomologyPullback_bijective_of_iso_factor g e
    (AlgebraicGeometry.ProjectiveSpace.BinaryFormProduct.lineBaseChangeMap (algebraMap k K))
    he F q hg

end AlgebraicGeometry.Scheme.EtaleCohomology.Proper
