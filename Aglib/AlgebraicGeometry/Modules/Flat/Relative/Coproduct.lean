/-
Copyright (c) 2026 algebraic-geometry contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.Modules.Flat.Relative
public import Mathlib.Algebra.Category.ModuleCat.Products
public import Mathlib.RingTheory.Flat.Basic

/-!
# Relative flatness of coproducts

A coproduct of relatively flat modules is relatively flat (`relativeFlat_coproduct`): the stalk
functor followed by restriction of scalars to the base local ring is a left adjoint, so it sends
the coproduct to the direct sum of the restricted stalks, and a direct sum of flat modules is
flat.
-/

@[expose] public section

noncomputable section

open CategoryTheory CategoryTheory.Limits

universe u

namespace AlgebraicGeometry.Scheme.Modules

/-- **Coproducts of relatively flat modules are relatively flat.** -/
theorem relativeFlat_coproduct {X Y : Scheme.{u}} (f : X ⟶ Y) {I : Type u}
    (g : I → X.Modules) (hg : ∀ i, relativeFlat f (g i)) : relativeFlat f (∐ g) := by
  classical
  intro x
  let G : X.Modules ⥤ ModuleCat.{u} (Y.presheaf.stalk (f x)) :=
    moduleStalk X x ⋙ ModuleCat.restrictScalars (f.stalkMap x).hom
  have : PreservesColimitsOfShape (Discrete I) G := by
    dsimp only [G]
    infer_instance
  let e : G.obj (∐ g) ≅ ModuleCat.of _ (DirectSum I fun i => G.obj (g i)) :=
    PreservesCoproduct.iso G g ≪≫ ModuleCat.coprodIsoDirectSum (fun i => G.obj (g i))
  have hflat (i : I) : Module.Flat (Y.presheaf.stalk (f x)) (G.obj (g i)) := hg i x
  exact Module.Flat.of_linearEquiv e.toLinearEquiv

end AlgebraicGeometry.Scheme.Modules
