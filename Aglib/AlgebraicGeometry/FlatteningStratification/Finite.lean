/-
Copyright (c) 2026 algebraic-geometry contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.FlatteningStratification.Coproduct
public import Aglib.CategoryTheory.Limits.Shapes.WidePullbacks
public import Mathlib.CategoryTheory.Limits.Shapes.FiniteLimits

/-!
# Joint rank strata of finitely many sheaves

Let `E_j`, `j ∈ J` with `J` finite, be finitely presented quasi-coherent `𝒪_S`-modules. The wide
pullback over `S` of the rank-strata immersions `rankStratumι (E j) _ (e j)` is the joint stratum
`W_e` of Nitsure, *Construction of Hilbert and Quot schemes*, arXiv:math/0504590v1, proof of
Theorem 4.3, pp. 21–22 (there for `E_i = π_* F(N + i)`, `0 ≤ i ≤ n`, built by iterating the case
`n = 0`): a morphism `g : T ⟶ S` factors through `W_e` if and only if every `g^* E_j` is finite
locally free of constant rank `e j`. The wide pullback of the morphisms `rankStrataι (E j) _` is a
monomorphism into `S` representing the morphisms along which every `E_j` becomes finite locally
free.

The wide-pullback inputs `CategoryTheory.Limits.WidePullback.exists_lift_base_iff` and
`CategoryTheory.Limits.WidePullback.mono_base` live in `CategoryTheory/Limits/Shapes/WidePullbacks`.

* `jointRankStratumι`, `exists_lift_jointRankStratumι_iff`: the joint stratum of prescribed ranks;
* `jointRankStrataι`, `jointRankStrataι_mono`, `exists_lift_jointRankStrataι_iff`: the joint
  flattening monomorphism.
-/

@[expose] public section

noncomputable section

universe u

open CategoryTheory Limits Opposite TopologicalSpace

namespace AlgebraicGeometry.Scheme.Modules

variable {S T : Scheme.{u}} {J : Type} [Finite J] (E : J → S.Modules)
  (hE : ∀ j, QuasiCoherent.affineLocallyFiniteType S (E j))

/-- The joint rank stratum `W_e` of the family `E` for the ranks `e`: the wide pullback over `S` of
the rank-`e j` strata of the `E j`. -/
abbrev jointRankStratum (e : J → ℕ) : Scheme.{u} :=
  widePullback S (fun j => rankStratum (E j) (hE j) (e j))
    (fun j => rankStratumι (E j) (hE j) (e j))

/-- The morphism from the joint rank stratum to `S`. -/
def jointRankStratumι (e : J → ℕ) : jointRankStratum E hE e ⟶ S :=
  WidePullback.base _

instance (e : J → ℕ) : Mono (jointRankStratumι E hE e) :=
  WidePullback.mono_base _

/-- **Universal property of the joint rank stratum** (Nitsure, arXiv:math/0504590v1, proof of
Theorem 4.3, p. 22, the strata `W_{e_0, …, e_n}`): for finitely presented `E j`, a morphism
`g : T ⟶ S` factors through `W_e` if and only if every `g^* E_j` is finite locally free of constant
rank `e j`. -/
theorem exists_lift_jointRankStratumι_iff [∀ j, (E j).IsFinitePresentation] (e : J → ℕ)
    (g : T ⟶ S) :
    (∃ h : T ⟶ jointRankStratum E hE e, h ≫ jointRankStratumι E hE e = g) ↔
      ∀ j, SheafHasRank ((pullback g).obj (E j)) (e j) := by
  rw [jointRankStratumι, WidePullback.exists_lift_base_iff]
  exact forall_congr' fun j => exists_lift_rankStratumι_iff_sheafHasRank (E j) (hE j) g (e j)

/-- The wide pullback over `S` of the disjoint unions of the rank strata of the `E j`. -/
abbrev jointRankStrata : Scheme.{u} :=
  widePullback S (fun j => rankStrata (E j) (hE j)) (fun j => rankStrataι (E j) (hE j))

/-- The morphism from the joint flattening stratification to `S`. -/
def jointRankStrataι : jointRankStrata E hE ⟶ S :=
  WidePullback.base _

/-- The joint flattening stratification of finitely presented sheaves is a monomorphism. -/
instance jointRankStrataι_mono [∀ j, (E j).IsFinitePresentation] : Mono (jointRankStrataι E hE) :=
  have := fun j => rankStrataι_mono (E j) (hE j)
  WidePullback.mono_base _

/-- **Universal property of the joint flattening stratification**: for finitely presented `E j`, a
morphism `g : T ⟶ S` factors through `jointRankStrataι E hE` if and only if every `g^* E_j` is
finite locally free. -/
theorem exists_lift_jointRankStrataι_iff [∀ j, (E j).IsFinitePresentation] (g : T ⟶ S) :
    (∃ h : T ⟶ jointRankStrata E hE, h ≫ jointRankStrataι E hE = g) ↔
      ∀ j, IsFiniteLocallyFree T ((pullback g).obj (E j)) := by
  rw [jointRankStrataι, WidePullback.exists_lift_base_iff]
  exact forall_congr' fun j => exists_lift_rankStrataι_iff (E j) (hE j) g

end AlgebraicGeometry.Scheme.Modules
