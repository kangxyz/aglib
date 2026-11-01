/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.Curves.Picard.OpenDivisibility
public import Aglib.AlgebraicGeometry.EtaleCohomology.Kummer.UnitsQuotient
public import Aglib.AlgebraicGeometry.EtaleCohomology.Curves.PrimeToCharacteristicVanishing

/-!
# Vanishing of root cohomology on an open curve

For an open subscheme of a smooth proper geometrically connected curve over an algebraically
closed field, missing a closed point, `H^q(U, μ_n) = 0` for `q ≥ 2` and invertible `n`.
The proof combines geometric Picard divisibility and the existing Kummer and broad-curve
vanishing suppliers (Stacks, Tag 03RR; Milne, Lectures on Étale Cohomology v2.21,
Proposition 14.12, p. 97). The general units/Picard exact sequence is imported from its owner.
-/

@[expose] public noncomputable section

open CategoryTheory AlgebraicGeometry
open AlgebraicGeometry.Scheme AlgebraicGeometry.Scheme.Modules.Invertible
open GroupCohomology.Kummer.Coefficients

universe u w

namespace AlgebraicGeometry.Scheme.EtaleCohomology.Curves

attribute [local instance] hasSheafifyLarge

open Scheme.OverField

section Complement

variable {k : Type u} [Field k] [IsAlgClosed k] {X : FScheme k} (hX : Curve.Properties X)
  {U : Scheme.{u}} (j : U ⟶ X.left) [IsOpenImmersion j] [HasExt.{w} (AbelianSheaf.{u, u + 1} U)]

include hX in
/-- **`H^2(U, μ_n) = 0`** for an open subscheme `U` of the curve whose image misses a closed
point and `n` invertible in `k`: `H^2(U, μ_n) = Pic(U)/n` and `Pic(U)` is `n`-divisible
(Milne, *Lectures on Étale Cohomology* v2.21, proof of Prop. 14.12, p. 97). -/
theorem roots_subsingleton_H_two_of_isOpenImmersion
    (hx : ∃ x : X.left, IsClosed ({x} : Set X.left) ∧ x ∉ Set.range j) (n : ℕ)
    (hunit : IsUnit (n : k)) : Subsingleton (Sheaf.H.{w} (mu U n) 2) := by
  have hn : 0 < n := Nat.pos_of_ne_zero (by rintro rfl; simp at hunit)
  have hk : IsUnit (n : Γ(Spec (.of k), ⊤)) := by
    simpa only [map_natCast] using hunit.map (Scheme.ΓSpecIso (.of k)).inv.hom
  have hinv : IsUnit (n : Γ(U, ⊤)) :=
    GroupCohomology.Kummer.CoefficientBaseChange.levelInvertible (j ≫ X.hom) n hk
  have := Curve.curveProperties_locallyOfFiniteType hX
  have := Curve.isNoetherian_of_isOpenImmersion hX j
  have hsurj := picardBoundary_surjective_of_curve k U (j ≫ X.hom)
    (Curve.topologicalKrullDim_le_one_of_isOpenImmersion hX j) n hn hunit hinv
  refine subsingleton_of_forall_eq 0 fun a => ?_
  obtain ⟨c, rfl⟩ := hsurj a
  obtain ⟨b, hb⟩ := Curve.exists_nsmul_eq_of_isOpenImmersion hX j n hunit hx c
  exact (Picard.picardBoundary_eq_zero_iff U n hn hinv c).mpr ⟨b, hb⟩

include hX in
/-- **`H^q(U, μ_n) = 0` for `q ≥ 2`** for an open subscheme `U` of the curve whose image misses a
closed point and `n` invertible in `k` (Stacks, Étale Cohomology, Lemma 69.3 (3), Tag 03RR;
Milne, *Lectures on Étale Cohomology* v2.21, Prop. 14.12, p. 97). -/
theorem roots_subsingleton_H_of_isOpenImmersion
    (hx : ∃ x : X.left, IsClosed ({x} : Set X.left) ∧ x ∉ Set.range j) (n : ℕ)
    (hunit : IsUnit (n : k)) (q : ℕ) (hq : 2 ≤ q) : Subsingleton (Sheaf.H.{w} (mu U n) q) := by
  rcases hq.eq_or_lt with rfl | hq
  · exact roots_subsingleton_H_two_of_isOpenImmersion hX j hx n hunit
  have hn : 0 < n := Nat.pos_of_ne_zero (by rintro rfl; simp at hunit)
  have hk : IsUnit (n : Γ(Spec (.of k), ⊤)) := by
    simpa only [map_natCast] using hunit.map (Scheme.ΓSpecIso (.of k)).inv.hom
  have := Curve.curveProperties_locallyOfFiniteType hX
  have := Curve.isNoetherian_of_isOpenImmersion hX j
  exact roots_subsingleton_H_of_curve k U (j ≫ X.hom)
    (Curve.topologicalKrullDim_le_one_of_isOpenImmersion hX j) n hn hunit
    (GroupCohomology.Kummer.CoefficientBaseChange.levelInvertible (j ≫ X.hom) n hk) q hq

include hX in
/-- **`H^q(X − D, μ_n) = 0` for `q ≥ 2`** when `D` is a nonempty set of closed points, `U = X − D`
with its open immersion `j` (`Set.range j = Dᶜ`) and `n` is invertible in `k` (Stacks, Étale
Cohomology, Lemma 69.3 (3), Tag 03RR; Milne, *Lectures on Étale Cohomology* v2.21, Prop. 14.12,
p. 97). -/
theorem roots_subsingleton_H_of_range_eq_compl (D : Set X.left) (hDne : D.Nonempty)
    (hclosed : ∀ x ∈ D, IsClosed ({x} : Set X.left)) (hD : Set.range j = Dᶜ) (n : ℕ)
    (hunit : IsUnit (n : k)) (q : ℕ) (hq : 2 ≤ q) : Subsingleton (Sheaf.H.{w} (mu U n) q) := by
  obtain ⟨x, hxD⟩ := hDne
  exact roots_subsingleton_H_of_isOpenImmersion hX j
    ⟨x, hclosed x hxD, by rw [hD]; exact fun h => h hxD⟩ n hunit q hq

end Complement

end AlgebraicGeometry.Scheme.EtaleCohomology.Curves
