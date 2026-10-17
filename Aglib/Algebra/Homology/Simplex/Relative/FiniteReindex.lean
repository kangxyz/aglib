/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.Algebra.Homology.Simplex.Relative.Trace

/-!
# Native simplex reindexing to a small finite vertex type

When the ring and original vertices share a universe, relabeling the vertices
by a small type gives an isomorphism in the same native module category. This
compares arbitrary finite geometric coordinate types with `Fin (n + 1)` and
transports the original full-support homology calculation without lowering
the scalar universe or replacing its coefficient module.
-/

@[expose] public section

noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true

open CategoryTheory CategoryTheory.Limits HomologicalComplex

universe u

namespace AlgebraicTopology.RelativeSimplex

variable {ι : Type u} {κ : Type} {R : Type u} [Ring R] {n : ℕ}

/-- Original cochain relabeling across the vertex-universe boundary, with the
same scalar ring and native module universe. -/
def cochainReindexSmallEquiv (e : ι ≃ κ) (n : ℕ) :
    Cochains R (Set.univ : Set ι) n ≃ₗ[R] Cochains R (Set.univ : Set κ) n where
  toFun x a := x (tupleReindex e.symm a)
  invFun x a := x (tupleReindex e a)
  left_inv x := by
    funext a
    exact congrArg x (tupleReindex_symm e a)
  right_inv x := by
    funext a
    exact congrArg x (tupleReindex_symm e.symm a)
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

/-- The small-target relabeling retains the original zero extension. -/
theorem extendByZero_cochainReindexSmallEquiv (e : ι ≃ κ)
    (x : Cochains R (Set.univ : Set ι) n) (a : Fin (n + 1) → κ) :
    extendByZero (cochainReindexSmallEquiv e n x) a =
      extendByZero x (e.symm ∘ a) := by
  classical
  by_cases ha : Set.univ ⊆ Set.range a
  · have he := (equiv_supported_iff e.symm a).mpr ha
    simp only [extendByZero, dite_eq_left ha, dite_eq_left he, cochainReindexSmallEquiv,
      LinearEquiv.coe_mk, tupleReindex]
    rfl
  · have he : ¬ Set.univ ⊆ Set.range (e.symm ∘ a) :=
      fun h => ha ((equiv_supported_iff e.symm a).mp h)
    simp only [extendByZero, dite_eq_right ha, dite_eq_right he]

/-- The original full-support cosimplicial objects are isomorphic after
small-target vertex relabeling in their shared native module category. -/
def cosimplicialReindexSmallIso (e : ι ≃ κ) :
    cosimplicial R (Set.univ : Set ι) ≅ cosimplicial R (Set.univ : Set κ) :=
  NatIso.ofComponents (fun n => (cochainReindexSmallEquiv (R := R) e n.len).toModuleIso) (by
    intro a b f
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro x
    funext t
    change extendByZero x ((e.symm ∘ t.val) ∘ f.toOrderHom) =
      extendByZero (cochainReindexSmallEquiv e _ x) (t.val ∘ f.toOrderHom)
    rw [extendByZero_cochainReindexSmallEquiv]
    rfl)

/-- The native original full-support complexes are isomorphic across the
vertex-universe boundary, retaining the actual relabeling maps. -/
def complexReindexSmallIso (e : ι ≃ κ) :
    complex R (Set.univ : Set ι) ≅ complex R (Set.univ : Set κ) :=
  (alternatingCofaceMapComplex _).mapIso (cosimplicialReindexSmallIso e)

theorem complexReindexSmallIso_hom_f_apply (e : ι ≃ κ) (n : ℕ)
    (x : Cochains R (Set.univ : Set ι) n) (a : Tuple (Set.univ : Set κ) n) :
    (complexReindexSmallIso (R := R) e).hom.f n x a = x (tupleReindex e.symm a) := rfl

/-- Canonical coercion form of `complexReindexSmallIso_hom_f_apply`
for simplification. -/
@[simp]
private theorem complexReindexSmallIso_hom_f_apply' (e : ι ≃ κ) (n : ℕ)
    (x : Cochains R (Set.univ : Set ι) n) (a : Tuple (Set.univ : Set κ) n) :
    (show Cochains R (Set.univ : Set ι) n →ₗ[R] Cochains R (Set.univ : Set κ) n from
      ((complexReindexSmallIso (R := R) e).hom.f n).hom) x a = x (tupleReindex e.symm a) := by
  exact complexReindexSmallIso_hom_f_apply (R := R) e n x a

/-- The native top scalar comparison for any geometric coordinate type
equivalent to the `n + 1` small vertices, without lowering the ring universe. -/
def fullSupportTopLinearEquivOfEquivFin (n : ℕ) (e : ι ≃ Fin (n + 1)) :
    (complex R (Set.univ : Set ι)).homology n ≃ₗ[R] R :=
  ((homologyFunctor (ModuleCat.{u} R) (.up ℕ) n).mapIso
    (complexReindexSmallIso e)).toLinearEquiv.trans (fullSupportTopLinearEquiv R n)

/-- Native full-support homology vanishes away from the top degree, for any
geometric coordinate type with the displayed finite enumeration. -/
theorem fullSupport_isZero_homology_of_ne_of_equivFin (n : ℕ) (e : ι ≃ Fin (n + 1))
    (q : ℕ) (hq : q ≠ n) : IsZero ((complex R (Set.univ : Set ι)).homology q) :=
  (fullSupport_isZero_homology_of_ne (R := R) n q hq).of_iso
    ((homologyFunctor (ModuleCat.{u} R) (.up ℕ) q).mapIso (complexReindexSmallIso e))

/-- The finite-coordinate top comparison retains the original cycles quotient
and evaluation on the chosen enumeration, with the original positive sign. -/
theorem fullSupportTopLinearEquivOfEquivFin_homologyπ (n : ℕ) (e : ι ≃ Fin (n + 1))
    (c : (complex R (Set.univ : Set ι)).cycles n) :
    fullSupportTopLinearEquivOfEquivFin n e ((complex R (Set.univ : Set ι)).homologyπ n c) =
      (complex R (Set.univ : Set ι)).iCycles n c
        ⟨e.symm, fun i _ => ⟨e i, e.symm_apply_apply i⟩⟩ := by
  change fullSupportTopLinearEquiv R n
    (homologyMap (complexReindexSmallIso (R := R) e).hom n
      ((complex R (Set.univ : Set ι)).homologyπ n c)) = _
  have hπ := ConcreteCategory.congr_hom
    (homologyπ_naturality (complexReindexSmallIso (R := R) e).hom n) c
  change homologyMap (complexReindexSmallIso (R := R) e).hom n
      ((complex R (Set.univ : Set ι)).homologyπ n c) =
    (complex R (Set.univ : Set (Fin (n + 1)))).homologyπ n
      (cyclesMap (complexReindexSmallIso (R := R) e).hom n c) at hπ
  rw [hπ, fullSupportTopLinearEquiv_homologyπ]
  have hi := ConcreteCategory.congr_hom
    (cyclesMap_i (complexReindexSmallIso (R := R) e).hom n) c
  change (complex R (Set.univ : Set (Fin (n + 1)))).iCycles n
      (cyclesMap (complexReindexSmallIso (R := R) e).hom n c) =
    (complexReindexSmallIso (R := R) e).hom.f n ((complex R (Set.univ : Set ι)).iCycles n c) at hi
  rw [hi]
  rfl

/-- The same original comparison for an actual required support proved equal
to full support, retaining the original weight homology object. -/
def topHomologyLinearEquivOfEqUnivOfEquivFin (n : ℕ) (e : ι ≃ Fin (n + 1))
    (S : Set ι) (hS : S = Set.univ) : (complex R S).homology n ≃ₗ[R] R := by
  subst S
  exact fullSupportTopLinearEquivOfEquivFin n e

/-- Support equality transport preserves the original enumerated-tuple
evaluation and actual cycles quotient. -/
theorem topHomologyLinearEquivOfEqUnivOfEquivFin_homologyπ
    (n : ℕ) (e : ι ≃ Fin (n + 1)) (S : Set ι) (hS : S = Set.univ)
    (c : (complex R S).cycles n) :
    topHomologyLinearEquivOfEqUnivOfEquivFin n e S hS ((complex R S).homologyπ n c) =
      (complex R S).iCycles n c ⟨e.symm, fun i _ => ⟨e i, e.symm_apply_apply i⟩⟩ := by
  subst S
  exact fullSupportTopLinearEquivOfEquivFin_homologyπ n e c

end AlgebraicTopology.RelativeSimplex
