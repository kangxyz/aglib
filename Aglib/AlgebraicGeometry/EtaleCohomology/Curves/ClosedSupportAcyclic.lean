/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.EtaleCohomology.Curves.PointSupportedClosedUnit
public import Aglib.AlgebraicGeometry.EtaleCohomology.Curves.FiniteClosedSupport
public import Aglib.AlgebraicGeometry.EtaleCohomology.Finite.HigherVanishing
public import Aglib.AlgebraicGeometry.EtaleCohomology.Finite.ExactImageComparison.Cohomology

/-! # Acyclicity of the actual finite closed support subobjects -/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits CategoryTheory.Abelian

namespace AlgebraicGeometry.Scheme.EtaleCohomology.Curves

universe u w

attribute [local instance] hasSheafifyLarge

variable {X : Scheme.{u}} [HasExt.{w} (AbelianSheaf.{u, u + 1} X)]

/-- Every actual finite closed support subobject is acyclic when the corresponding
original residue fields are separably closed. The base Ext universe is arbitrary. -/
theorem pointSupportedSubobject_subsingleton_H (F : AbelianSheaf.{u, u + 1} X)
    (Z : Set X) (hfin : Z.Finite) (hclosed : ∀ x ∈ Z, IsClosed ({x} : Set X))
    (hsep : ∀ x : Z, IsSepClosed (X.residueField x.val)) (q : ℕ) (hq : 0 < q) :
    Subsingleton (Sheaf.H.{w}
      (pointSupportedSubobject F Z : AbelianSheaf.{u, u + 1} X) q) := by
  let S := FiniteClosedSupport.pointScheme X Z
  let i : S ⟶ X := FiniteClosedSupport.inclusion X Z
  let : IsClosedImmersion i := FiniteClosedSupport.inclusion_isClosedImmersion X Z hfin hclosed
  let A : AbelianSheaf.{u, u + 1} X := pointSupportedSubobject F Z
  let : HasExt.{u + 2} (AbelianSheaf.{u, u + 1} S) := HasExt.standard _
  let : IsIso ((inverseImageAdjunction i).unit.app A) := by
    apply pointSupportedSubobject_unit_isIso i F Z
    intro x hx
    apply (FiniteClosedSupport.exists_lift_iff X Z (FibrewiseClosed.geometricPoint x)).mpr
    exact (FibrewiseClosed.geometricPoint_apply x _).symm ▸ hx
  let : Subsingleton (Sheaf.H.{u + 2} ((inverseImage i).obj A) q) :=
    FiniteClosedSupport.subsingleton_H X Z hfin hsep ((inverseImage i).obj A) q hq
  let : Subsingleton (Sheaf.H.{w} ((directImage i).obj ((inverseImage i).obj A)) q) :=
    (cohomologyDirectImageAddEquiv.{u, u + 2, w} i
      ((inverseImage i).obj A) q).injective.subsingleton
  let H := (Sheaf.functorH X.smallEtaleTopology q :
    AbelianSheaf.{u, u + 1} X ⥤ AddCommGrpCat.{w})
  let : Subsingleton (H.obj ((inverseImage i ⋙ directImage i).obj A)) :=
    inferInstanceAs (Subsingleton
      (Sheaf.H.{w} ((directImage i).obj ((inverseImage i).obj A)) q))
  exact ((ConcreteCategory.isIso_iff_bijective
    (H.map ((inverseImageAdjunction i).unit.app A))).mp inferInstance).injective.subsingleton

end AlgebraicGeometry.Scheme.EtaleCohomology.Curves
