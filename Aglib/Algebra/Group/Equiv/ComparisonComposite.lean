/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Mathlib.Algebra.Group.Equiv.Basic

/-! # Whole comparison composites of original additive equivalences

The component construction and its map square are proved before any concrete
carrier is substituted. The affine higher-image comparison is a consumer.
-/

@[expose] public section

namespace AddEquiv

variable {A B C D E A' B' C' D' E' : Type*}
  [AddCommGroup A] [AddCommGroup B] [AddCommGroup C] [AddCommGroup D] [AddCommGroup E]
  [AddCommGroup A'] [AddCommGroup B'] [AddCommGroup C'] [AddCommGroup D'] [AddCommGroup E']

/-- The complete square on supplied original additive equivalences and maps.
Keeping this proposition intact lets consumers share its exact data before
specializing a concrete carrier. -/
def MapSquare (e : A ≃+ B) (e' : A' ≃+ B')
    (a : A → A') (b : B → B') (x : A) : Prop := e' (a x) = b (e x)

/-- Compose the original source, central, inverse target and output comparisons. -/
def comparisonComposite (l : A ≃+ B) (e : B ≃+ C) (r : D ≃+ C) (s : D ≃+ E) : A ≃+ E :=
  l.trans (e.trans (r.symm.trans s))

/-- The whole original component square follows from its four original map laws. -/
theorem comparisonComposite_map
    (l : A ≃+ B) (e : B ≃+ C) (r : D ≃+ C) (s : D ≃+ E)
    (l' : A' ≃+ B') (e' : B' ≃+ C') (r' : D' ≃+ C') (s' : D' ≃+ E')
    (a : A →+ A') (b : B →+ B') (c : C →+ C') (d : D →+ D') (k : E →+ E')
    (hl : ∀ x, l' (a x) = b (l x))
    (he : ∀ x, e' (b x) = c (e x))
    (hr : ∀ x, r' (d x) = c (r x))
    (hs : ∀ x, s' (d x) = k (s x)) (x : A) :
    comparisonComposite l' e' r' s' (a x) = k (comparisonComposite l e r s x) := by
  change s' (r'.symm (e' (l' (a x)))) = k (s (r.symm (e (l x))))
  rw [hl, he]
  have h := hr (r.symm (e (l x)))
  rw [apply_symm_apply] at h
  rw [← h, symm_apply_apply]
  exact hs _

end AddEquiv
