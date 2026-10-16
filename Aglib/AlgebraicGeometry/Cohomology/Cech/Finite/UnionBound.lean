/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.Topology.Sheaves.MayerVietorisSections
public import Mathlib.AlgebraicGeometry.Morphisms.Affine
public import Mathlib.AlgebraicGeometry.Morphisms.Separated

/-!
# Sharp finite affine-union bounds for actual section complexes

If a termwise flasque sheaf complex is cohomologically at most zero on every
affine open of a separated scheme, its section complex on a union of `n + 1`
affine opens is cohomologically at most `n`. The proof repeatedly uses the
original Mayer--Vietoris restriction sequence. No replacement cohomology object,
Noetherian condition, or finiteness of section modules is introduced.
-/

@[expose] public section

noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry TopologicalSpace

universe u v

namespace AlgebraicGeometry.Scheme.Cohomology

variable {X : Scheme.{u}} [X.IsSeparated]
  {A : Type v} [Category.{u} A] [Abelian A]
  [HasSheafify (Opens.grothendieckTopology X.toTopCat) A]

/-- The actual section complex on a union of `n + 1` affine opens has the
sharp bound `n`, when the displayed complex is acyclic above zero on affines. -/
theorem sectionsComplex_isLE_iSup_of_isAffineOpen
    (K : CochainComplex (TopCat.Sheaf A X.toTopCat) ℤ)
    [∀ i, TopCat.Presheaf.IsFlasque (K.X i).obj]
    (haffine : ∀ U : X.Opens, IsAffineOpen U →
      CochainComplex.IsLE (TopCat.Sheaf.sectionsComplex K U) 0)
    (n : ℕ) (U : Fin (n + 1) → X.Opens) (hU : ∀ i, IsAffineOpen (U i)) :
    CochainComplex.IsLE (TopCat.Sheaf.sectionsComplex K (iSup U)) (n : ℤ) := by
  induction n with
  | zero =>
    have hsup : iSup U = U 0 := by
      apply le_antisymm
      · apply iSup_le
        intro i
        have hi : i = 0 := Fin.eq_zero i
        subst i
        exact le_rfl
      · exact le_iSup U 0
    rw [hsup]
    exact haffine (U 0) (hU 0)
  | succ n ih =>
    let V : Fin (n + 1) → X.Opens := fun i => U i.succ
    have hV := ih V (fun i => hU i.succ)
    have hW := ih (fun i : Fin (n + 1) => U 0 ⊓ V i)
      (fun i => (hU 0).inf (hU i.succ))
    have hsup : iSup U = U 0 ⊔ iSup V := by
      apply le_antisymm
      · apply iSup_le
        intro i
        refine Fin.cases ?_ (fun j => ?_) i
        · exact le_sup_left
        · exact (le_iSup V j).trans le_sup_right
      · exact sup_le (le_iSup U 0) (iSup_le fun i => le_iSup U i.succ)
    have : CochainComplex.IsLE (TopCat.Sheaf.sectionsComplex K (U 0))
        ((n + 1 : ℕ) : ℤ) := by
      have := haffine (U 0) (hU 0)
      exact CochainComplex.isLE_of_le _ 0 _ (by omega)
    have : CochainComplex.IsLE (TopCat.Sheaf.sectionsComplex K (iSup V))
        ((n + 1 : ℕ) : ℤ) :=
      CochainComplex.isLE_of_le _ (n : ℤ) _ (by omega)
    have : CochainComplex.IsLE (TopCat.Sheaf.sectionsComplex K (U 0 ⊓ iSup V))
        (((n + 1 : ℕ) : ℤ) - 1) := by
      have hcast : (((n + 1 : ℕ) : ℤ) - 1) = (n : ℤ) := by omega
      rw [hcast, inf_iSup_eq]
      exact hW
    rw [hsup]
    exact TopCat.Sheaf.sectionsComplex_isLE_sup K (U 0) (iSup V) ((n + 1 : ℕ) : ℤ)

end AlgebraicGeometry.Scheme.Cohomology
