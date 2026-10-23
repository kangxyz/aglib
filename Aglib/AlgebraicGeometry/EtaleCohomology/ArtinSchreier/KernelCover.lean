/-
Copyright (c) 2026 kangxyz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.RingTheory.Etale.ArtinSchreier.Kernel.Idempotents
public import Mathlib.AlgebraicGeometry.Restrict
public import Mathlib.RingTheory.LocalRing.Basic

/-!
# Basic-open residue components of an Artin--Schreier root

The basic opens of the canonical root idempotents cover any scheme. On each
one, the original restriction of the original root is the indicated literal
residue constant. No affineness, Noetherianity or nonemptiness is assumed.
-/

@[expose] public noncomputable section

open CategoryTheory
open Algebra.ArtinSchreier

namespace AlgebraicGeometry.Scheme.ArtinSchreier

universe u

private theorem map_eq_natCast_of_unit_factor {A B : Type*} [CommRing A] [CommRing B]
    (f : A →+* B) (e a : A) (n : ℕ) (he : IsUnit (f e))
    (h : e * a = (n : A) * e) : f a = (n : B) := by
  apply he.mul_left_cancel
  simpa only [map_mul, map_natCast, mul_comm] using congrArg f h

variable {X : Scheme.{u}} (p : ℕ) [Fact p.Prime]
  (hX : (p : Γ(X, ⊤)) = 0) (b : Γ(X, ⊤)) (hb : b ^ p - b = 0)

/-- The actual basic open of the canonical idempotent attached to a residue constant. -/
def rootOpen (i : ZMod p) : X.Opens :=
  X.basicOpen (rootIdempotent p hX b hb i)

/-- Every point lies in one of the original idempotent basic opens. -/
theorem exists_mem_rootOpen (x : X) : ∃ i : ZMod p, x ∈ rootOpen p hX b hb i := by
  let g := (X.presheaf.germ ⊤ x (by trivial)).hom
  have hsum : ∑ i : ZMod p, g (rootIdempotent p hX b hb i) = 1 := by
    rw [← map_sum, sum_rootIdempotent, map_one]
  obtain ⟨i, _, hi⟩ := IsLocalRing.exists_of_isUnit_sum
    (R := X.presheaf.stalk x) (s := Finset.univ)
    (f := fun i : ZMod p => g (rootIdempotent p hX b hb i))
    (by rw [hsum]; exact isUnit_one)
  exact ⟨i, (X.mem_basicOpen_top _ x).mpr hi⟩

/-- The literal supremum of the canonical residue opens is the whole scheme. -/
theorem iSup_rootOpen : (⨆ i : ZMod p, rootOpen p hX b hb i) = ⊤ := by
  apply top_unique
  intro x _
  exact TopologicalSpace.Opens.mem_iSup.mpr (exists_mem_rootOpen p hX b hb x)

/-- The original restricted idempotent is a unit on its actual basic open. -/
theorem isUnit_rootOpen_appTop_idempotent (i : ZMod p) :
    IsUnit ((rootOpen p hX b hb i).ι.appTop.hom (rootIdempotent p hX b hb i)) := by
  let U := rootOpen p hX b hb i
  let e := rootIdempotent p hX b hb i
  have hopen : U.toScheme.basicOpen (U.ι.appTop e) = ⊤ := by
    rw [← Scheme.preimage_basicOpen_top U.ι e]
    change U.ι ⁻¹ᵁ U = ⊤
    exact U.ι_preimage_self
  apply U.toScheme.toRingedSpace.isUnit_of_isUnit_germ ⊤ (U.ι.appTop e)
  intro x hx
  apply (U.toScheme.mem_basicOpen _ x hx).mp
  rw [hopen]
  trivial

/-- The exact original pullback of the root is its literal residue constant
on the corresponding canonical basic open. -/
theorem rootOpen_appTop_root (i : ZMod p) :
    (rootOpen p hX b hb i).ι.appTop.hom b =
      (i.val : Γ((rootOpen p hX b hb i).toScheme, ⊤)) :=
  map_eq_natCast_of_unit_factor
    (A := Γ(X, ⊤)) (B := Γ((rootOpen p hX b hb i).toScheme, ⊤))
    (rootOpen p hX b hb i).ι.appTop.hom (rootIdempotent p hX b hb i) b i.val
    (isUnit_rootOpen_appTop_idempotent p hX b hb i)
    (rootIdempotent_mul_root p hX b hb i)

end AlgebraicGeometry.Scheme.ArtinSchreier
