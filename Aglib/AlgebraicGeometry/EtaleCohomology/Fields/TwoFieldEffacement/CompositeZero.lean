/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.EtaleCohomology.Fields.AlgebraicExtension.FiniteConstantDescent

/-! # Finite-stage zero for a class pulled to an actual source cover

The source class is the literal restriction of the original target class along
the supplied morphism. Native algebraic field zero descent is applied to this
unchanged class, and the final equation is restored along the original composite.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite

namespace AlgebraicGeometry.Scheme.EtaleCohomology.TwoFieldEffacement

universe u

attribute [local instance] hasSheafifyLarge HasExt.standard

/-- If the original composite restriction becomes zero over an algebraic
extension, the same original composite becomes zero at a finite field stage. -/
theorem exists_finiteField_composite_zero
    (k Ω : Type u) [Field k] [Field Ω] [Algebra k Ω] [Algebra.IsAlgebraic k Ω]
    {Y T : Scheme.{u}} [CompactSpace Y] [QuasiSeparatedSpace Y]
    (p : Y ⟶ Spec (.of k)) (f : Y ⟶ T)
    (A : Type u) [AddCommGroup A] (q : ℕ)
    (c : Sheaf.H.{u + 2} (ConstantFinite.coefficient A T) q)
    (hc : Curves.constantRestriction.{u, u + 2, u + 2} A
      (pullback.fst p (Spec.algebraMap k Ω) ≫ f) q c = 0) :
    ∃ s : Finset Ω, Curves.constantRestriction.{u, u + 2, u + 2} A
      (((FiniteEtale.FieldLimit.schemeDiagram k Ω p).obj (op s)).hom ≫ f) q c = 0 := by
  have hzero : Curves.constantRestriction.{u, u + 2, u + 2} A
      (pullback.fst p (Spec.algebraMap k Ω)) q
      (Curves.constantRestriction.{u, u + 2, u + 2} A f q c) = 0 :=
    (Curves.constantRestriction_comp A f (pullback.fst p (Spec.algebraMap k Ω)) q c).symm.trans hc
  obtain ⟨s, hs⟩ :=
    ConstantFinite.AlgebraicExtension.exists_finiteField_constantRestriction_eq_zero
      k Ω p A q (Curves.constantRestriction A f q c) hzero
  exact ⟨s, (Curves.constantRestriction_comp A f
    ((FiniteEtale.FieldLimit.schemeDiagram k Ω p).obj (op s)).hom q c).trans hs⟩

end AlgebraicGeometry.Scheme.EtaleCohomology.TwoFieldEffacement
