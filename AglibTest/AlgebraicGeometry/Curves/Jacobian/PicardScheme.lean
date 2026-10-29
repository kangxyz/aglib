/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.Curves.Jacobian.PicardScheme

/-!
# Consumer checks for `Aglib.AlgebraicGeometry.Curves.Jacobian.PicardScheme`

From `Curve.Properties X` alone: dimension one, flatness, a closed projective embedding and the
Picard scheme of `X` with its basic and field properties; axiom guards.
-/

@[expose] public section

noncomputable section

open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory Opposite
open AlgebraicGeometry AlgebraicGeometry.Scheme AlgebraicGeometry.Scheme.OverField
open AlgebraicGeometry.Scheme.Modules.Invertible AlgebraicGeometry.Scheme.RelativePicard
open AlgebraicGeometry.Scheme.Group AlgebraicGeometry.Scheme.OverField.Curve

universe u

namespace AglibTest.CurvesJacobianPicardScheme

variable {k : Type u} [Field k] {X : FScheme k}

/-- Dimension one and flatness from the curve hypothesis only. -/
example (hX : Curve.Properties X) : topologicalKrullDim X.left = 1 ∧ Flat X.hom :=
  ⟨hX.topologicalKrullDim_eq_one, hX.flat⟩

/-- A closed embedding into projective space over `k`, commuting with the structure morphism. -/
example (hX : Curve.Properties X) :
    ∃ (N : ℕ) (i : X.left ⟶ ProjectiveSpace k (ULift.{u} (Fin (N + 1)))),
      IsClosedImmersion i ∧ i ≫ ProjectiveSpace.toSpec k (ULift.{u} (Fin (N + 1))) = X.hom :=
  hX.exists_closedImmersion_projectiveSpace

/-- The Picard scheme: a separated scheme locally of finite type representing the fppf Picard
sheaf of `X.hom`, whose identity component is open and closed and geometrically irreducible. -/
example (hX : Curve.Properties X) :
    ∃ (P : LocallyNoetherianOver (Spec (.of k)))
      (R : ((locallyNoetherianOverInclusion (Spec (.of k))).op ⋙ (fppfPicardSheaf X.hom).obj ⋙
        CategoryTheory.forget AddCommGrpCat.{u + 1}).RepresentableBy P)
      (_ : LocallyOfFiniteType P.obj.hom),
      IsSeparated P.obj.hom ∧
        (letI := picardCommGrpObj X.hom P R;
          IsClopen (identityComponent P.obj : Set P.obj.left) ∧
            GeometricallyIrreducible (identityComponentOver P.obj).hom) := by
  obtain ⟨P, R, h, hsep, -, -, -, -, -, -, ⟨-, hJ, -, -, -, hirr⟩, -⟩ :=
    exists_representableBy_fppfPicardSheaf_properties hX
  exact ⟨P, R, h, hsep, hJ, hirr⟩

/--
info: 'AlgebraicGeometry.Scheme.OverField.Curve.Properties.topologicalKrullDim_eq_one' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms AlgebraicGeometry.Scheme.OverField.Curve.Properties.topologicalKrullDim_eq_one

/--
info: 'AlgebraicGeometry.Scheme.OverField.Curve.Properties.flat' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms AlgebraicGeometry.Scheme.OverField.Curve.Properties.flat

/--
info: 'AlgebraicGeometry.Scheme.OverField.Curve.Properties.exists_closedImmersion_projectiveSpace' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms AlgebraicGeometry.Scheme.OverField.Curve.Properties.exists_closedImmersion_projectiveSpace

/--
info: 'AlgebraicGeometry.Scheme.OverField.Curve.exists_representableBy_fppfPicardSheaf_properties' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms AlgebraicGeometry.Scheme.OverField.Curve.exists_representableBy_fppfPicardSheaf_properties

end AglibTest.CurvesJacobianPicardScheme

