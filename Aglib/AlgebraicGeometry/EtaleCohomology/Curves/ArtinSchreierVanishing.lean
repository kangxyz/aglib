/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.EtaleCohomology.ArtinSchreier.ShortExact
public import Aglib.CategoryTheory.Sites.SheafCohomology.Vanishing.ExactSequence

/-!
# The original Artin–Schreier vanishing reduction

This is the exact-sequence step for the characteristic-primary curve argument.
It uses the principal's actual additive structure sheaf and original AS map.
The geometric comparison and finite-dimensional Frobenius argument must still
supply the stated coherent-cohomology hypotheses; this is not the final curve theorem.
-/

@[expose] public noncomputable section

universe u w

open CategoryTheory

namespace AlgebraicGeometry.Scheme.EtaleCohomology.Curves

variable (X : Scheme.{u}) [HasExt.{w} (AbelianSheaf.{u, u + 1} X)]

/-- The actual AS sequence kills prime-field cohomology above degree one once
its genuine structure-cohomology inputs have been supplied. -/
theorem primeField_vanishing_of_structure_cohomology
    (p : ℕ) (hp : p.Prime) (hX : (p : Γ(X, ⊤)) = 0)
    (hsurj : Function.Surjective (Sheaf.H.map (artinSchreierMap X p hp hX) 1))
    (hvanish : ∀ q : ℕ, 1 < q → Subsingleton (Sheaf.H.{w} (additiveStructureSheaf X) q))
    (m : ℕ) : Subsingleton (Sheaf.H.{w} (primeFieldSheaf X p) (m + 2)) := by
  let : Subsingleton (Sheaf.H.{w} (artinSchreierComplex X p hp hX).X₂ (m + 2)) :=
    hvanish (m + 2) (by omega)
  apply Sheaf.H.subsingleton_left_of_surjective
    (artinSchreierComplex_shortExact X p hp hX) (m + 1) (m + 2) (by omega)
  cases m with
  | zero => exact hsurj
  | succ m =>
      let : Subsingleton (Sheaf.H.{w} (artinSchreierComplex X p hp hX).X₃ (m + 1 + 1)) :=
        hvanish (m + 1 + 1) (by omega)
      intro x
      exact ⟨0, Subsingleton.elim _ _⟩

end AlgebraicGeometry.Scheme.EtaleCohomology.Curves
