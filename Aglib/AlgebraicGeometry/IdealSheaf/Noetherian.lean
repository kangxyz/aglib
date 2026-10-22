/-
Copyright (c) 2026 kangxyz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Mathlib.AlgebraicGeometry.Noetherian
public import Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion
public import Mathlib.AlgebraicGeometry.IdealSheaf.Subscheme

/-!
# Noetherian induction on ideal sheaves

Quasi-coherent ideal sheaves on a Noetherian scheme satisfy the ascending chain
condition, including their nilpotent structure. A finite affine cover reduces
this to ring-ideal ACC with one common stabilization index. Strict closed
subschemes of a closed subscheme give strict increases of the original ideal.
-/

@[expose] public section

open CategoryTheory

namespace AlgebraicGeometry.Scheme.IdealSheafData

universe u
variable {X : Scheme.{u}}

/-- Ring-ideal ACC on a finite affine cover implies ideal-sheaf ACC. -/
theorem wellFoundedGT_of_finite_affine_cover {ι : Type*} [Finite ι]
    (U : ι → X.affineOpens) (hU : ⨆ i, (U i).1 = ⊤)
    [∀ i, IsNoetherianRing Γ(X, U i)] : WellFoundedGT X.IdealSheafData := by
  classical
  let := Fintype.ofFinite ι
  rw [wellFoundedGT_iff_monotone_chain_condition]
  intro a
  have h (i : ι) : ∃ n, ∀ m, n ≤ m → (a n).ideal (U i) = (a m).ideal (U i) :=
    WellFoundedGT.monotone_chain_condition
      ⟨fun n ↦ (a n).ideal (U i), fun _ _ h ↦ a.monotone h (U i)⟩
  choose n hn using h
  refine ⟨Finset.univ.sup n, fun m hm ↦ ext_of_iSup_eq_top U hU fun i ↦ ?_⟩
  have hi : n i ≤ Finset.univ.sup n := Finset.le_sup (Finset.mem_univ i)
  exact (hn i _ hi).symm.trans (hn i _ (hi.trans hm))

/-- Ideal-sheaf Noetherian induction retains nilpotent information; no dimension
or reducedness hypothesis is needed. -/
instance [IsNoetherian X] : WellFoundedGT X.IdealSheafData := by
  let 𝒰 := X.affineCover.finiteSubcover
  have (i : 𝒰.I₀) : IsAffine (𝒰.X i) := by
    change IsAffine (X.affineCover.X (X.affineCover.idx i.1))
    infer_instance
  let U (i : 𝒰.I₀) : X.affineOpens :=
    ⟨(𝒰.f i).opensRange, isAffineOpen_opensRange _⟩
  have (i : 𝒰.I₀) : IsNoetherianRing Γ(X, U i) :=
    IsLocallyNoetherian.component_noetherian (U i)
  exact wellFoundedGT_of_finite_affine_cover U 𝒰.iSup_opensRange

/-- A nonzero ideal on a closed subscheme gives a strictly larger ideal on the
original scheme, via the kernel of the original composite immersion. -/
lemma lt_ker_subschemeι_comp (I : X.IdealSheafData)
    (J : I.subscheme.IdealSheafData) (hJ : J ≠ ⊥) :
    I < (J.subschemeι ≫ I.subschemeι).ker := by
  refine lt_of_le_of_ne ?_ ?_
  · simpa using J.subschemeι.le_ker_comp I.subschemeι
  · intro h
    have : IsIso J.subschemeι :=
      IsClosedImmersion.isIso_of_ker_eq (J.subschemeι ≫ I.subschemeι)
        I.subschemeι J.subschemeι rfl (by simpa using h.symm)
    exact hJ ((isIso_subschemeι_iff_eq_bot J).mp inferInstance)

/-- A proper support, unlike merely a nonzero ideal, ensures that every positive
power is nonzero even on nonreduced schemes. -/
lemma pow_ne_bot_of_support_ne_top (I : X.IdealSheafData)
    (hI : I.support ≠ ⊤) (n : ℕ) (hn : n ≠ 0) : I ^ n ≠ ⊥ := by
  intro h
  apply hI
  rw [← support_pow I n hn, h, support_bot]

/-- In particular the exceptional ideal of a nonempty open complement has
nonzero positive powers. -/
lemma pow_ne_bot_of_nonempty_compl_support (I : X.IdealSheafData)
    (hI : (I.support : Set X)ᶜ.Nonempty) (n : ℕ) (hn : n ≠ 0) : I ^ n ≠ ⊥ := by
  apply pow_ne_bot_of_support_ne_top I _ n hn
  intro h
  simp [h] at hI

/-- A dense open complement on a nonempty scheme supplies the nonvanishing
needed for ideal-sheaf induction. -/
lemma pow_ne_bot_of_dense_compl_support [Nonempty X] (I : X.IdealSheafData)
    (hI : Dense (I.support : Set X)ᶜ) (n : ℕ) (hn : n ≠ 0) : I ^ n ≠ ⊥ :=
  pow_ne_bot_of_nonempty_compl_support I hI.nonempty n hn

end AlgebraicGeometry.Scheme.IdealSheafData
