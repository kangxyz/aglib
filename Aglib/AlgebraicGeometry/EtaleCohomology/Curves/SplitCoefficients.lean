/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.EtaleCohomology.Curves.CoefficientNaturality

/-!
# Finite split coefficient reduction

Surjectivity is preserved by a finite split presentation of the actual constant
coefficient value. The proof lifts each projected class and adds the resulting
classes using the original restriction map. No extension-surjectivity principle
or exactness assertion for an arbitrary short exact sequence is used.
-/

@[expose] public noncomputable section

universe u v w w'

open CategoryTheory
open scoped BigOperators

namespace AlgebraicGeometry.Scheme.EtaleCohomology.Curves

attribute [local instance] hasSheafifyLarge

variable {A : Type u} [AddCommGroup A] {ι : Type v} [Fintype ι]
  (B : ι → Type u) [∀ i, AddCommGroup (B i)]
  {X S : Scheme.{u}} (f : S ⟶ X)
  [HasExt.{w} (AbelianSheaf.{u, u + 1} X)]
  [HasExt.{w'} (AbelianSheaf.{u, u + 1} S)]

/-- Finite split coefficient reduction for the literal original restriction map. -/
theorem constantRestriction_surjective_of_split_family
    (s : ∀ i, ConstantFinite.value (B i) ⟶ ConstantFinite.value A)
    (r : ∀ i, ConstantFinite.value A ⟶ ConstantFinite.value (B i))
    (hs : ∑ i, r i ≫ s i = 𝟙 _) (q : ℕ)
    (hB : ∀ i, Function.Surjective (constantRestriction (B i) f q)) :
    Function.Surjective (constantRestriction A f q) := by
  classical
  let C := constantSheaf (Scheme.smallEtaleTopology S) AddCommGrpCat.{u + 1}
  let D := constantSheaf (Scheme.smallEtaleTopology X) AddCommGrpCat.{u + 1}
  intro x
  choose y hy using fun i => hB i (Sheaf.H.map (C.map (r i)) q x)
  refine ⟨∑ i, Sheaf.H.map (D.map (s i)) q (y i), ?_⟩
  have hsum : ∑ i, Sheaf.H.map (C.map (r i ≫ s i)) q x = x := by
    let T := C ⋙ Sheaf.functorH.{w', u + 1, u, u + 1} (Scheme.smallEtaleTopology S) q
    have hmaps : ∑ i, T.map (r i ≫ s i) = 𝟙 _ := by
      rw [← T.map_sum, hs, T.map_id]
    let ev : (T.obj (ConstantFinite.value A) ⟶ T.obj (ConstantFinite.value A)) →+
        T.obj (ConstantFinite.value A) :=
      (AddMonoidHom.eval x).comp AddCommGrpCat.homAddEquiv.toAddMonoidHom
    have hvalue := congrArg ev hmaps
    rw [map_sum] at hvalue
    exact hvalue
  calc
    constantRestriction A f q (∑ i, Sheaf.H.map (D.map (s i)) q (y i)) =
        ∑ i, Sheaf.H.map (C.map (s i)) q
          (constantRestriction (B i) f q (y i)) := by
      rw [map_sum]
      apply Finset.sum_congr rfl
      intro i _
      exact constantRestriction_coefficientMap f (s i) q (y i)
    _ = ∑ i, Sheaf.H.map (C.map (r i ≫ s i)) q x := by
      apply Finset.sum_congr rfl
      intro i _
      rw [hy i, CategoryTheory.Functor.map_comp, Sheaf.H.map_comp_apply]
    _ = x := hsum

end AlgebraicGeometry.Scheme.EtaleCohomology.Curves
