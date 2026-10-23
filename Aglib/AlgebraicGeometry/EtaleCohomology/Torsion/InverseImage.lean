/-
Copyright (c) 2026 kangxyz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.EtaleCohomology.Torsion.Basic
public import Aglib.AlgebraicGeometry.EtaleCohomology.GeometricPoints.InverseImage

/-!
# Inverse image preserves actual torsion coefficients

The original all-coefficient stalk-unit isomorphism transfers stalkwise
torsion along every scheme morphism. Original geometric stalks detect the
internal local condition, with no finiteness or cohomological premise.
-/

@[expose] public noncomputable section

open CategoryTheory

namespace AlgebraicGeometry.Scheme.EtaleCohomology

universe u

attribute [local instance] hasSheafifyLarge

/-- Inverse image along every scheme morphism preserves internally torsion abelian sheaves. -/
theorem IsTorsion.inverseImage {X S : Scheme.{u}} (f : S ⟶ X)
    {F : AbelianSheaf.{u, u + 1} X} (hF : IsTorsion X F) :
    IsTorsion S ((inverseImage f).obj F) := by
  apply isTorsion_of_geometricStalks
  intro Ω _ _ η
  let e := (StalkInverseImage.stalkUnitNatIso f η).app F
  apply IsAddTorsion.of_surjective (f := e.hom.hom) ?_ (hF.geometricStalk (η ≫ f))
  intro z
  refine ⟨e.inv z, ?_⟩
  exact ConcreteCategory.congr_hom e.inv_hom_id z

end AlgebraicGeometry.Scheme.EtaleCohomology
