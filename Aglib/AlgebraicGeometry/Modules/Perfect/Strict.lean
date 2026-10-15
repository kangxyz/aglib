/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.Modules.LocallyFree.Exact
public import Aglib.CategoryTheory.ExactCategory.Abelian
public import Mathlib.Algebra.Homology.HomologicalComplexAbelian
public import Mathlib.Algebra.Homology.Single

/-! # Strict perfect complexes of scheme modules

Strict perfectness means global bounds on the TERMS and finite local freeness
in each degree. The full subcategory retains actual chain maps. Extension
closure uses locally split short exact sequences of vector bundles; no global
projectivity or geometric finiteness hypothesis is added.

Source: `Quillen/AlgebraicGeometry/PerfectComplexes/Strict.lean`,
archive SHA-256
`16c127c5b7a5874cb4d841e1161b436190c35aeb08802b89cb19fd8c76ad1d48`,
source SHA-256 `93b391540dcb92c7d58bda3d9357e16f9327ea7dfc1f13c12976f7f084c2981d`.
Admitted subset: term bounds, strict-perfect predicate/full chain category,
  zero/isomorphism/extension closure, degree-zero vector-bundle inclusion.
-/

@[expose] public section

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open CategoryTheory.ExactCategory
open scoped ZeroObject

universe u

attribute [local instance] Abelian.hasFiniteBiproducts

namespace AlgebraicGeometry.Scheme.Modules.Complex

/-- Strict boundedness concerns the terms, not merely the cohomology. -/
def IsBounded {X : Scheme.{u}} (K : CochainComplex X.Modules ℤ) : Prop :=
  ∃ (a b : ℤ), ∀ (n : ℤ), n < a ∨ b < n → IsZero (K.X n)

/-- Globally bounded complexes of finite locally free sheaves. -/
def strictPerfect (X : Scheme.{u}) : ObjectProperty (CochainComplex X.Modules ℤ) := fun K ↦
  IsBounded K ∧ ∀ n : ℤ, IsFiniteLocallyFree X (K.X n)

/-- The full category of strict perfect complexes. -/
abbrev StrictPerfect (X : Scheme.{u}) := (strictPerfect X).FullSubcategory

variable {X : Scheme.{u}}

/-- Every zero complex is strict perfect. -/
theorem strictPerfect_of_isZero {K : CochainComplex X.Modules ℤ} (hK : IsZero K) : strictPerfect X
  K := by
  have h (n : ℤ) : IsZero (K.X n) :=
    (HomologicalComplex.eval X.Modules (ComplexShape.up ℤ) n).map_isZero hK
  exact ⟨⟨0, 0, fun n _ ↦ h n⟩, fun n ↦ finiteLocallyFree_of_isZero (h n)⟩

instance strictPerfect_containsZero : (strictPerfect X).ContainsZero where
  exists_zero := ⟨0, isZero_zero _, strictPerfect_of_isZero (isZero_zero _)⟩

/-- Strict perfectness is invariant under actual chain isomorphism. -/
theorem strictPerfect_of_iso {K L : CochainComplex X.Modules ℤ} (e : K ≅ L)
    (hK : strictPerfect X K) : strictPerfect X L := by
  obtain ⟨⟨a, b, hb⟩, hv⟩ := hK
  let en (n : ℤ) := (HomologicalComplex.eval X.Modules (ComplexShape.up ℤ) n).mapIso e
  refine ⟨⟨a, b, fun n hn ↦ (hb n hn).of_iso (en n).symm⟩, ?_⟩
  intro n
  exact (finiteLocallyFree_iff_of_iso (en n)).1 (hv n)

instance strictPerfect_closedUnderIsomorphisms : (strictPerfect X).IsClosedUnderIsomorphisms where
  of_iso e hK := strictPerfect_of_iso e hK

/-- A short exact extension of strict perfect complexes is strict perfect. -/
theorem strictPerfect_of_shortExact {S : ShortComplex (CochainComplex X.Modules ℤ)}
    (hS : S.ShortExact) (h₁ : strictPerfect X S.X₁) (h₃ : strictPerfect X S.X₃) :
    strictPerfect X S.X₂ := by
  obtain ⟨⟨a, b, hb₁⟩, hv₁⟩ := h₁
  obtain ⟨⟨c, d, hb₃⟩, hv₃⟩ := h₃
  have hs (n : ℤ) := (HomologicalComplex.shortExact_iff_degreewise_shortExact S).1 hS n
  constructor
  · refine ⟨min a c, max b d, fun n hn ↦ ?_⟩
    have h₁ : IsZero (S.X₁.X n) := hb₁ n (hn.elim
      (fun h ↦ Or.inl (lt_of_lt_of_le h (min_le_left _ _)))
      (fun h ↦ Or.inr (lt_of_le_of_lt (le_max_left _ _) h)))
    have h₃ : IsZero (S.X₃.X n) := hb₃ n (hn.elim
      (fun h ↦ Or.inl (lt_of_lt_of_le h (min_le_right _ _)))
      (fun h ↦ Or.inr (lt_of_le_of_lt (le_max_right _ _) h)))
    exact (hs n).exact.isZero_X₂ (h₁.eq_of_src _ _) (h₃.eq_of_tgt _ _)
  · intro n
    exact @finiteLocallyFree_of_shortExact X _ (hs n) (hv₁ n) (hv₃ n)

instance strictPerfect_extensionClosed :
    (abelianExactStructure (CochainComplex X.Modules ℤ)).IsExtensionClosed (strictPerfect X) where
  prop_middle := strictPerfect_of_shortExact

instance strictPerfect_closedUnderFiniteProducts :
    (strictPerfect X).IsClosedUnderFiniteProducts :=
  (abelianExactStructure (CochainComplex X.Modules ℤ)).extensionClosed_finiteProducts
    (strictPerfect X)

/-- A vector bundle, placed in degree zero, is a strict perfect complex. -/
theorem single_strictPerfect (M : X.Modules) [IsFiniteLocallyFree X M] :
    strictPerfect X ((HomologicalComplex.single X.Modules (ComplexShape.up ℤ) 0).obj M) := by
  constructor
  · refine ⟨0, 0, fun n hn ↦ ?_⟩
    exact HomologicalComplex.isZero_single_obj_X _ _ _ _ (by omega)
  · intro n
    by_cases hn : n = 0
    · subst n
      simpa only [HomologicalComplex.single_obj_X_self] using
        (inferInstance : IsFiniteLocallyFree X M)
    · exact finiteLocallyFree_of_isZero
        (HomologicalComplex.isZero_single_obj_X _ _ _ _ hn)

/-- The canonical degree-zero inclusion of vector bundles into strict perfect
complexes. -/
def vectorBundleInclusion (X : Scheme.{u}) : FiniteLocallyFree X ⥤ StrictPerfect X :=
  (strictPerfect X).lift
    ((finiteLocallyFree X).ι ⋙
      HomologicalComplex.single X.Modules (ComplexShape.up ℤ) 0)
    (fun M ↦ single_strictPerfect M.obj)

end AlgebraicGeometry.Scheme.Modules.Complex
