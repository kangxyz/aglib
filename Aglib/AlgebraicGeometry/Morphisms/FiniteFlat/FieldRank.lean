/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.Morphisms.FiniteFlat.RankOne
public import Aglib.AlgebraicGeometry.Morphisms.FiniteFlat.Degree
public import Aglib.AlgebraicGeometry.Modules.BaseChange.Affine

/-!
# Structural rank of the original finite scheme over a field

The native locally free rank agrees with the dimension of the original
coordinate algebra for its structural field action. This uses the existing
module-base-change map and native residual rank, with no reducedness or
etaleness assumption.
-/

@[expose] public noncomputable section

open CategoryTheory AlgebraicGeometry Scheme.OverField

universe u

namespace AlgebraicGeometry.Scheme.Hom

attribute [local instance] coordinateAlgebra

/-- Constant locally free rank of a finite field scheme is its original
structural degree, including nonreduced and empty schemes. -/
theorem hasLocallyFreeRank_iff_finiteSchemeDegree_eq
    {k : Type u} [Field k] (X : FScheme k) [IsFinite X.hom] (n : ℕ) :
    HasLocallyFreeRank X.hom n ↔ finiteSchemeDegree k X.hom = n := by
  let : Flat X.hom := inferInstance
  let : LocallyOfFinitePresentation X.hom := inferInstance
  have hfree : FiniteLocallyFree X.hom :=
    finiteFlatPresentationLocallyFree X.left (Spec (.of k)) X.hom
      inferInstance inferInstance inferInstance
  rw [hasLocallyFreeRank_iff_rank_eq X.hom hfree n]
  constructor
  · intro h
    change Module.finrank k Γ(X.left, ⊤) = n
    exact (FiniteFlat.nativeRank_field k X default).symm.trans
      ((FiniteFlat.nativeRank_eq_locallyFreeRank X.hom
        Scheme.Modules.affineModuleBaseChange default).trans (h default))
  · intro h y
    exact (FiniteFlat.nativeRank_eq_locallyFreeRank X.hom
      Scheme.Modules.affineModuleBaseChange y).symm.trans
        ((FiniteFlat.nativeRank_field k X y).trans h)

end AlgebraicGeometry.Scheme.Hom
