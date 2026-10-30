/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.Morphisms.Proper.ProductRigidity

/-! Whole original-map rigidity retains the integral-product hypothesis and arbitrary separated target. -/

@[expose] public noncomputable section

open CategoryTheory MonoidalCategory CartesianMonoidalCategory AlgebraicGeometry

universe u

attribute [local instance] Over.cartesianMonoidalCategory

example {k : Type u} [Field k] [IsAlgClosed k]
    (V W Y : Over (Spec (.of k)))
    [LocallyOfFiniteType V.hom] [IsProper W.hom]
    [IsSeparated Y.hom] [LocallyOfFiniteType Y.hom] [IsIntegral (V ⊗ W).left]
    (v : 𝟙_ (Over (Spec (.of k))) ⟶ V)
    (w : 𝟙_ (Over (Spec (.of k))) ⟶ W)
    (y : 𝟙_ (Over (Spec (.of k))) ⟶ Y)
    (f : V ⊗ W ⟶ Y) (hf : (v ▷ W) ≫ f = toUnit _ ≫ y) :
    f = fst V W ≫ (ρ_ V).inv ≫ V ◁ w ≫ f :=
  Scheme.OverField.eq_fst_comp_of_isProper_of_integral_tensor V W Y v w y f hf

end

/--
info: 'AlgebraicGeometry.Scheme.OverField.eq_fst_comp_of_isProper_of_integral_tensor' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms AlgebraicGeometry.Scheme.OverField.eq_fst_comp_of_isProper_of_integral_tensor
