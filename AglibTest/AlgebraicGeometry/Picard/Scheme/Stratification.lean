/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.Picard.Scheme.Stratification

/-!
# Consumer checks for the stratification of the Picard scheme

The strata `Pic^φ` (open and closed, disjoint, covering), the levels `Pic^φ_m` (increasing, with
union `Pic^φ`, H-quasi-projective over a Noetherian base under the finiteness of the ranks), the
refinement `Pic^{φ,ψ}_m` by the ranks, and the functorial meaning of the open loci (Kleiman,
*The Picard scheme*, arXiv:math/0504020v1, Thm 4.8 and its proof, pp. 27–30), with axiom guards.
-/

@[expose] public section

noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite
open AlgebraicGeometry AlgebraicGeometry.ProjectiveSpace
open AlgebraicGeometry.Scheme.RelativePicard AlgebraicGeometry.Scheme.RelativePicard.Strata

universe u

namespace AglibTest.PicardSchemeStratification

variable {A : Type u} [CommRing A] {ι : Type u} {X : Scheme.{u}}
  {i : X ⟶ ProjectiveSpace A ι} [IsClosedImmersion i] [Flat (i ≫ toSpec A ι)]
  [GeometricallyIntegral (i ≫ toSpec A ι)] {N : ℕ} {e : ι ≃ Fin (N + 1)}
  (h : FineStrataRepresentableByHQuasiProjective i N e)

/-- The strata `Pic^φ` are open and closed, pairwise disjoint, and cover the Picard scheme. -/
example (φ : Polynomial ℚ) :
    IsClopen (picardStratumOpens h φ : Set (picardScheme h).obj.left) ∧
      Pairwise (Function.onFun Disjoint (picardStratumOpens h)) ∧
      ⨆ φ', picardStratumOpens h φ' = ⊤ :=
  ⟨isClopen_picardStratumOpens h φ, pairwise_disjoint_picardStratumOpens h,
    iSup_picardStratumOpens h⟩

/-- The levels `Pic^φ_m` increase with `m`, with union `Pic^φ`. -/
example (φ : Polynomial ℚ) :
    Monotone (picardLevelOpens h φ) ∧ ⨆ m, picardLevelOpens h φ m = picardStratumOpens h φ :=
  ⟨monotone_picardLevelOpens h φ, iSup_picardLevelOpens h φ⟩

/-- `Pic^{φ,ψ}_m` is the disjoint union of the chart images of the ranks `k + 1`. -/
example (φ ψ : Polynomial ℚ) (m : ℤ) :
    ⨆ k : ℕ, (fineCondition i N e φ ψ m (k + 1)).opens (picardUniversalSection h) =
        picardBaseLevelOpens h φ ψ m ∧
      Pairwise (Function.onFun Disjoint fun k : ℕ =>
        (fineCondition i N e φ ψ m (k + 1)).opens (picardUniversalSection h)) :=
  ⟨iSup_fineCondition_opens_eq_picardBaseLevelOpens h φ ψ m,
    pairwise_disjoint_fineCondition_opens h φ ψ m⟩

/-- A morphism `a : T ⟶ P` lands in `Pic^φ` (resp. `Pic^φ_m`) exactly when its section of
`Pic_{X/S,(fppf)}` lies in the subsheaf `Pic^φ` (resp. `Pic^φ_m`). -/
example (φ : Polynomial ℚ) (m : ℤ) {T : Scheme.LocallyNoetherianOver (Spec (.of A))}
    (a : T ⟶ picardScheme h) :
    ((picardSchemeRepresentableBy h).homEquiv a ∈
        (eulerCondition i N e φ).subfunctor.obj (op T.obj) ↔
      a.hom.left ⁻¹ᵁ picardStratumOpens h φ = ⊤) ∧
    ((picardSchemeRepresentableBy h).homEquiv a ∈
        (coarseCondition i N e φ m).subfunctor.obj (op T.obj) ↔
      a.hom.left ⁻¹ᵁ picardLevelOpens h φ m = ⊤) :=
  ⟨picardSchemeRepresentableBy_homEquiv_mem_eulerCondition_iff h φ a,
    picardSchemeRepresentableBy_homEquiv_mem_coarseCondition_iff h φ m a⟩

/-- Over a Noetherian ring, with finitely many ranks on the fine strata at level `0`, each
`Pic^φ_m` is H-quasi-projective over `Spec A`. -/
example [IsNoetherianRing A] (hrank : FiniteFineStrataRanks i N e) (φ : Polynomial ℚ) (m : ℤ) :
    IsHQuasiProjective ((picardLevelOpens h φ m).ι ≫ (picardScheme h).obj.hom) :=
  isHQuasiProjective_picardLevelOpens_of_finiteFineStrataRanks h hrank φ m

/-- The finiteness premise is the pointwise statement on the ranks. -/
example (hrank : ∀ φ₀ ψ : Polynomial ℚ, {k : ℕ | ∃ (T : Over (Spec (.of A)))
      (a : (familyPicardFunctor (i ≫ toSpec A ι)).obj (op T)) (t : T.left),
        (fineCondition i N e φ₀ ψ 0 (k + 1)).Holds T a t}.Finite) :
    FiniteFineStrataRanks i N e :=
  hrank

/--
info: 'AlgebraicGeometry.Scheme.RelativePicard.isHQuasiProjective_picardLevelOpens_of_finiteFineStrataRanks' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms isHQuasiProjective_picardLevelOpens_of_finiteFineStrataRanks

/--
info: 'AlgebraicGeometry.Scheme.RelativePicard.finite_setOf_fineCondition_holds_of_finiteFineStrataRanks' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms finite_setOf_fineCondition_holds_of_finiteFineStrataRanks

/--
info: 'AlgebraicGeometry.Scheme.RelativePicard.iSup_picardLevelOpens' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms iSup_picardLevelOpens

/--
info: 'AlgebraicGeometry.Scheme.RelativePicard.isClopen_picardStratumOpens' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms isClopen_picardStratumOpens

/--
info: 'AlgebraicGeometry.Scheme.RelativePicard.picardSchemeRepresentableBy_homEquiv_mem_iff' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms picardSchemeRepresentableBy_homEquiv_mem_iff

end AglibTest.PicardSchemeStratification
