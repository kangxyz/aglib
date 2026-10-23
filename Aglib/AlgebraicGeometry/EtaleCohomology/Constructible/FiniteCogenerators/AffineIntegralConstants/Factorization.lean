/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.EtaleCohomology.Constructible.FiniteCogenerators.AffineIntegralConstants.SheafColimit
public import Mathlib.CategoryTheory.Presentable.Finite

/-! # Actual finite-stage factorization of maps into finite-constant direct images

Ambient finite presentability factors a given original coefficient map through
the actual finite-generated subalgebra diagram. For an integral algebra each
selected stage is finite over the original base. No finiteness of the integral
algebra, Noetherianity or constructibility-to-presentability implication is used.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite

namespace AlgebraicGeometry.Scheme.EtaleCohomology.Constructible.AffineIntegralConstants

universe u

attribute [local instance] hasSheafifyLarge Cardinal.fact_isRegular_aleph0

variable (R A : Type u) [CommRing R] [CommRing A] [Algebra R A]
  (B : Type u) [AddCommGroup B] [Finite B]

/-- Every actual stage is the literal constant pushforward from its original
finite-generated subalgebra, with its original base map. -/
theorem constantPushforwardDiagram_obj (s : Finset A) :
    (constantPushforwardDiagram R A B).obj (op (op s)) =
      (directImage (Spec.algebraMap R (Algebra.FiniteTypeSubalgebraLimit.stage R A s))).obj
        (ConstantFinite.coefficient B
          (Spec (.of (Algebra.FiniteTypeSubalgebraLimit.stage R A s)))) := rfl

/-- A given original map from an ambient finitely presentable coefficient
factors through an actual finite-generated subalgebra stage. -/
theorem exists_constantPushforward_stage_factorization
    (F : AbelianSheaf.{u, u + 1} (Spec (.of R))) [IsFinitelyPresentable.{u + 1} F]
    (a : F ⟶ (directImage (Spec.algebraMap R A)).obj
      (ConstantFinite.coefficient B (Spec (.of A)))) :
    ∃ (s : Finset A)
      (b : F ⟶ (constantPushforwardDiagram R A B).obj (op (op s))),
      b ≫ (constantPushforwardCocone R A B).ι.app (op (op s)) = a := by
  have : PreservesFilteredColimitsOfSize.{u, u} (coyoneda.obj (op F)) :=
    preservesFilteredColimitsOfSize_of_univLE.{u + 1, u + 1, u, u} _
  have : IsFinitelyPresentable.{u} F :=
    isFinitelyPresentable_iff_preservesFilteredColimitsOfSize.mpr inferInstance
  obtain ⟨i, b, hb⟩ := IsFinitelyPresentable.exists_hom_of_isColimit
    (constantPushforwardCoconeIsColimit R A B) a
  exact ⟨i.unop.unop, b, hb⟩

/-- If the original algebra is integral, the actual factorization stage is
finite over the original base; no finite-normalization premise is needed. -/
theorem exists_finite_constantPushforward_stage_factorization [Algebra.IsIntegral R A]
    (F : AbelianSheaf.{u, u + 1} (Spec (.of R))) [IsFinitelyPresentable.{u + 1} F]
    (a : F ⟶ (directImage (Spec.algebraMap R A)).obj
      (ConstantFinite.coefficient B (Spec (.of A)))) :
    ∃ s : Finset A,
      IsFinite ((Scheme.FiniteTypeSubalgebraLimit.baseDiagram R A).obj (op s)).hom ∧
      ∃ b : F ⟶ (constantPushforwardDiagram R A B).obj (op (op s)),
        b ≫ (constantPushforwardCocone R A B).ι.app (op (op s)) = a := by
  obtain ⟨s, b, hb⟩ := exists_constantPushforward_stage_factorization R A B F a
  exact ⟨s, constantPushforwardStage_isFinite R A s, b, hb⟩

end AlgebraicGeometry.Scheme.EtaleCohomology.Constructible.AffineIntegralConstants
