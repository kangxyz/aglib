/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Aglib.AlgebraicGeometry.Cohomology.Cech.Comparison
public import Mathlib.Topology.Sheaves.MayerVietoris

/-!
# The sharp finite affine-cover cohomological bound

The unchanged open-Ext cohomology of quasicoherent module coefficients on a
union of `n + 1` affine opens of a separated scheme vanishes in degrees greater
than `n`. The proof uses the native Mayer--Vietoris long exact sequence and
actual affine acyclicity. At the whole space the native open-Ext comparison
gives the same bound for the original `Sheaf.H`.
-/

@[expose] public section

noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry TopologicalSpace

universe u

namespace AlgebraicGeometry.Scheme.Cohomology

variable {X : Scheme.{u}}

/-- The native Mayer--Vietoris sequence detects vanishing on the union from
vanishing in the same degree on the two opens and in the previous degree on
their intersection. -/
theorem subsingleton_sheafHPrime_sup
    (F : Sheaf (Opens.grothendieckTopology X) AddCommGrpCat.{u})
    (U V : X.Opens) (n : ℕ)
    [Subsingleton (Sheaf.H'.{u + 1} F n (U ⊓ V))]
    [Subsingleton (Sheaf.H'.{u + 1} F (n + 1) U)]
    [Subsingleton (Sheaf.H'.{u + 1} F (n + 1) V)] :
    Subsingleton (Sheaf.H'.{u + 1} F (n + 1) (U ⊔ V)) := by
  have h := (Opens.mayerVietorisSquare U V).sequence_exact.{u + 1} F n (n + 1) rfl
  apply AddCommGrpCat.subsingleton_of_isZero
  refine (h.exact 2).isZero_of_both_isZero ?_ ?_
  · change IsZero (Sheaf.H'.{u + 1} F n (U ⊓ V))
    exact AddCommGrpCat.isZero_of_subsingleton _
  · change IsZero (Sheaf.H'.{u + 1} F (n + 1) U ⊞ Sheaf.H'.{u + 1} F (n + 1) V)
    exact (biprod_isZero_iff _ _).2
      ⟨AddCommGrpCat.isZero_of_subsingleton _, AddCommGrpCat.isZero_of_subsingleton _⟩

variable [X.IsSeparated]

/-- Sharp vanishing on a union of `n + 1` affine opens, for the actual native
open-Ext cohomology of quasicoherent coefficients. -/
theorem subsingleton_sheafHPrime_iSup_of_isAffineOpen
    (M : X.Modules) [M.IsQuasicoherent]
    (n : ℕ) (U : Fin (n + 1) → X.Opens) (hU : ∀ i, IsAffineOpen (U i))
    (q : ℕ) (hq : n < q) :
    Subsingleton (Sheaf.H'.{u + 1} (moduleAddSheaf X M) q (iSup U)) := by
  induction n generalizing q with
  | zero =>
    have hsup : iSup U = U 0 := by
      apply le_antisymm
      · apply iSup_le
        intro i
        rw [Fin.eq_zero i]
      · exact le_iSup U 0
    rw [hsup]
    obtain ⟨q, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : q ≠ 0)
    exact subsingleton_sheafHPrime_of_isAffineOpen M (U 0) (hU 0) q
  | succ n ih =>
    let V : Fin (n + 1) → X.Opens := fun i => U i.succ
    have hsup : iSup U = U 0 ⊔ iSup V := by
      apply le_antisymm
      · apply iSup_le
        intro i
        refine Fin.cases ?_ (fun j => ?_) i
        · exact le_sup_left
        · exact (le_iSup V j).trans le_sup_right
      · exact sup_le (le_iSup U 0) (iSup_le fun i => le_iSup U i.succ)
    obtain ⟨q, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : q ≠ 0)
    let : Subsingleton (Sheaf.H'.{u + 1} (moduleAddSheaf X M) (q + 1) (U 0)) :=
      subsingleton_sheafHPrime_of_isAffineOpen M (U 0) (hU 0) q
    let : Subsingleton (Sheaf.H'.{u + 1} (moduleAddSheaf X M) (q + 1) (iSup V)) :=
      ih V (fun i => hU i.succ) (q + 1) (by omega)
    let : Subsingleton (Sheaf.H'.{u + 1} (moduleAddSheaf X M) q (U 0 ⊓ iSup V)) := by
      rw [inf_iSup_eq]
      exact ih (fun i : Fin (n + 1) => U 0 ⊓ V i)
        (fun i => (hU 0).inf (hU i.succ)) q (by omega)
    rw [hsup]
    exact subsingleton_sheafHPrime_sup (moduleAddSheaf X M) (U 0) (iSup V) q

/-- A cover by `n + 1` affine opens gives the sharp upper bound `n` for the
original `Sheaf.H`, with no Noetherian or module-finiteness premise. -/
theorem subsingleton_sheafH_of_finite_affine_cover
    (M : X.Modules) [M.IsQuasicoherent]
    (n : ℕ) (U : Fin (n + 1) → X.Opens) (hU : ∀ i, IsAffineOpen (U i))
    (hcover : iSup U = ⊤) (q : ℕ) (hq : n < q) :
    Subsingleton (Sheaf.H.{u + 1} (moduleAddSheaf X M) q) := by
  have : Subsingleton (Sheaf.H'.{u + 1} (moduleAddSheaf X M) q ⊤) := by
    rw [← hcover]
    exact subsingleton_sheafHPrime_iSup_of_isAffineOpen M n U hU q hq
  exact (sheafHPrimeTopAddEquiv X (moduleAddSheaf X M) q).symm.injective.subsingleton

end AlgebraicGeometry.Scheme.Cohomology
