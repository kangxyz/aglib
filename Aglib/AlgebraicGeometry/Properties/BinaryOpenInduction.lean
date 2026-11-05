/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.Properties.FiniteCoverOpenInduction

/-! # Binary source-cover induction without a finite-descent premise

Affine input and the original binary union/overlap gluing rule suffice on
compact opens of a quasi-separated scheme. The separated pass strengthens
induction by intersections with every affine open; the qcqs pass uses compact
separated overlaps inside the added affine. Intersections on a general qcqs
scheme are never asserted affine.
-/

@[expose] public noncomputable section

open CategoryTheory Limits TopologicalSpace

universe u

namespace AlgebraicGeometry.Scheme

variable {X : Scheme.{u}} (P : X.Opens → Prop)
  (hAffine : ∀ U : X.Opens, IsAffineOpen U → P U)
  (hSup : ∀ U V : X.Opens, P U → P V → P (U ⊓ V) → P (U ⊔ V))

include hAffine hSup

/-- On a separated source, strengthen the finite affine-cover induction by
all affine intersections, rather than assuming finite descent. -/
theorem of_compact_open_of_binary_of_separated [X.IsSeparated]
    (U : X.Opens) (hU : IsCompact (U : Set X)) : P U := by
  let Q : X.Opens → Prop := fun W => P W ∧ ∀ V, IsAffineOpen V → P (W ⊓ V)
  have hb : Q ⊥ := by
    constructor
    · exact hAffine _ (isAffineOpen_bot X)
    · intro V hV
      simpa only [bot_inf_eq] using hAffine _ (isAffineOpen_bot X)
  have hs (W : X.Opens) (_hW : IsCompact (W : Set X)) (V : X.affineOpens)
      (ih : Q W) : Q (W ⊔ V.val) := by
    refine ⟨hSup W V.val ih.1 (hAffine _ V.property) (ih.2 _ V.property), ?_⟩
    intro T hT
    rw [inf_sup_right]
    apply hSup _ _ (ih.2 _ hT) (hAffine _ (V.property.inf hT))
    simpa only [inf_assoc, inf_left_comm, inf_idem] using
      ih.2 (V.val ⊓ T) (V.property.inf hT)
  have h : Q U := compact_open_induction_on U hU hb hs
  exact h.1

/-- A compact separated open is handled inside its own original scheme,
then its actual open images are returned to the unchanged ambient scheme. -/
theorem of_compact_separated_open_of_binary (U : X.Opens)
    [U.toScheme.IsSeparated] (hU : IsCompact (U : Set X)) : P U := by
  let : CompactSpace U.toScheme := isCompact_iff_compactSpace.mp hU
  let Q : U.toScheme.Opens → Prop := fun V => P (U.ι ''ᵁ V)
  have ha : ∀ V : U.toScheme.Opens, IsAffineOpen V → Q V :=
    fun V hV => hAffine _ (hV.image_of_isOpenImmersion U.ι)
  have hs : ∀ V W : U.toScheme.Opens, Q V → Q W → Q (V ⊓ W) → Q (V ⊔ W) := by
    intro V W hV hW hVW
    have hi : U.ι ''ᵁ (V ⊓ W) = (U.ι ''ᵁ V) ⊓ (U.ι ''ᵁ W) := by
      apply Opens.ext
      exact Set.image_inter U.ι.isOpenEmbedding.injective
    have hu : U.ι ''ᵁ (V ⊔ W) = (U.ι ''ᵁ V) ⊔ (U.ι ''ᵁ W) := by
      apply Opens.ext
      exact Set.image_union _ _ _
    change P (U.ι ''ᵁ (V ⊔ W))
    rw [hu]
    exact hSup _ _ hV hW (by simpa only [Q, hi] using hVW)
  have ht := of_compact_open_of_binary_of_separated Q ha hs ⊤ isCompact_univ
  simpa only [Q, U.ι.image_top_eq_opensRange, Opens.opensRange_ι] using ht

/-- The second source-cover pass uses compact separated overlaps inside an
affine chart, not a false affine-intersection claim on arbitrary qcqs sources. -/
theorem of_compact_open_of_binary [QuasiSeparatedSpace X]
    (U : X.Opens) (hU : IsCompact (U : Set X)) : P U := by
  refine compact_open_induction_on U hU (hAffine _ (isAffineOpen_bot X)) ?_
  intro W hW V ih
  let : IsAffine V.val.toScheme := V.property
  let i : (W ⊓ V.val).toScheme ⟶ V.val.toScheme := X.homOfLE inf_le_right
  let : (W ⊓ V.val).toScheme.IsSeparated := ⟨by
    rw [← terminal.comp_from i]
    infer_instance⟩
  have hWV : IsCompact ((W ⊓ V.val : X.Opens) : Set X) :=
    hW.inter_of_isOpen V.property.isCompact W.isOpen V.val.isOpen
  exact hSup W V.val ih (hAffine _ V.property)
    (of_compact_separated_open_of_binary P hAffine hSup _ hWV)

end AlgebraicGeometry.Scheme
