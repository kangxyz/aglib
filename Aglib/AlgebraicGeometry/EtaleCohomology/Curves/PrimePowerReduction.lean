/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.EtaleCohomology.Curves.SplitCoefficients
public import Mathlib.GroupTheory.FiniteAbelian.Basic

/-!
# Reduction to prime-power constant coefficients

The native structure theorem gives an actual finite direct-sum decomposition.
Its inclusions and projections, lifted to the original coefficient universe,
satisfy the split identity used by the original cohomological restriction.
Exponent zero is retained, so the statement includes the zero cyclic group.
-/

@[expose] public noncomputable section

universe u v w w'

open CategoryTheory
open scoped BigOperators DirectSum

namespace AlgebraicGeometry.Scheme.EtaleCohomology.Curves

attribute [local instance] hasSheafifyLarge

variable {X S : Scheme.{u}} (f : S ⟶ X)
  [HasExt.{w} (AbelianSheaf.{u, u + 1} X)]
  [HasExt.{w'} (AbelianSheaf.{u, u + 1} S)]

/-- An actual finite cyclic direct-sum decomposition supplies the original
coefficient inclusions, projections and split identity. This is the common
construction used by both unrestricted and annihilator-bounded reductions. -/
theorem constantRestriction_surjective_of_zmod_directSum_equiv (q : ℕ)
    {A : Type u} [AddCommGroup A] {ι : Type v} [Finite ι]
    (m : ι → ℕ) (e : A ≃+ ⨁ i, ZMod (m i))
    (h : ∀ i, Function.Surjective (constantRestriction (ULift.{u} (ZMod (m i))) f q)) :
    Function.Surjective (constantRestriction A f q) := by
  classical
  let : Fintype ι := Fintype.ofFinite ι
  let B : ι → Type u := fun i => ULift.{u} (ZMod (m i))
  let liftA : ULift.{u + 1} A ≃+ A := AddEquiv.ulift
  let liftB (i : ι) : ULift.{u + 1} (B i) ≃+ ZMod (m i) :=
    AddEquiv.ulift.trans AddEquiv.ulift
  let s : ∀ i, ConstantFinite.value (B i) ⟶ ConstantFinite.value A := fun i =>
    AddCommGrpCat.ofHom (liftA.symm.toAddMonoidHom.comp
      (e.symm.toAddMonoidHom.comp
        ((DirectSum.of (fun j => ZMod (m j)) i).comp (liftB i).toAddMonoidHom)))
  let r : ∀ i, ConstantFinite.value A ⟶ ConstantFinite.value (B i) := fun i =>
    AddCommGrpCat.ofHom ((liftB i).symm.toAddMonoidHom.comp
      ((DFinsupp.evalAddMonoidHom i).comp (e.toAddMonoidHom.comp liftA.toAddMonoidHom)))
  have hs : ∑ i, r i ≫ s i = 𝟙 _ := by
    apply AddCommGrpCat.homAddEquiv.injective
    apply AddMonoidHom.ext
    intro x
    change (AddCommGrpCat.homAddEquiv (∑ i, r i ≫ s i)) x = x
    rw [map_sum, AddMonoidHom.finsetSum_apply]
    apply liftA.injective
    rw [map_sum]
    change (∑ i, e.symm (DirectSum.of (fun j => ZMod (m j)) i
      ((e (liftA x)) i))) = liftA x
    rw [← map_sum, DirectSum.sum_univ_of, e.symm_apply_apply]
  exact constantRestriction_surjective_of_split_family B f s r hs q
    h

/-- Actual finite-abelian reduction, using split prime-power factors rather than extensions. -/
theorem constantRestriction_surjective_of_prime_powers (q : ℕ)
    (h : ∀ (p : ℕ), p.Prime → ∀ r : ℕ,
      Function.Surjective (constantRestriction (ULift.{u} (ZMod (p ^ r))) f q))
    (A : Type u) [AddCommGroup A] [Finite A] :
    Function.Surjective (constantRestriction A f q) := by
  classical
  obtain ⟨ι, hι, p, hp, n, ⟨e⟩⟩ := AddCommGroup.equiv_directSum_zmod_of_finite A
  let := hι
  exact constantRestriction_surjective_of_zmod_directSum_equiv f q
    (fun i => p i ^ n i) e (fun i => h (p i) (hp i) (n i))

end AlgebraicGeometry.Scheme.EtaleCohomology.Curves
