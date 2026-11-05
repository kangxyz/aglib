/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.Morphisms.Proper.BirationalLocus
public import Aglib.AlgebraicGeometry.Dimension.OpenComplementCodimension

/-! # Codimension-two boundary of a proper birational morphism

The actual target isomorphism locus of a proper birational morphism onto an
integral normal locally Noetherian scheme contains all points of codimension
at most one. Its native closed complement therefore has dimension at most `d`
when the target has dimension at most `d + 2`. The original map and open
restriction are retained; no chosen replacement modification is introduced.
-/

@[expose] public noncomputable section

open CategoryTheory TopologicalSpace

namespace AlgebraicGeometry.Scheme

universe u

/-- A proper birational morphism onto a normal integral locally Noetherian
scheme has an actual isomorphism open with a two-dimensional dimension drop
on its produced closed complement. -/
theorem Hom.exists_closedBoundary_dimension_le_of_isProper_birational
    {Y X : Scheme.{u}} [IsIntegral Y] [IsIntegral X] [IsLocallyNoetherian X]
    (b : Y ⟶ X) [IsProper b] [IsDominant b]
    (hff : IsIso (CommRingCat.ofHom (functionFieldMap b)))
    (hX : NormalStalks X) (d : ℕ)
    (hdim : topologicalKrullDim X ≤ (d + 2 : ℕ)) :
    ∃ (U : X.Opens) (Z : Scheme.{u}) (i : Z ⟶ X),
      IsIso (b ∣_ U) ∧ IsClosedImmersion i ∧
      Set.range U.ι = (Set.range i)ᶜ ∧ topologicalKrullDim Z ≤ (d : ℕ) := by
  have hcodim (x : X) (hx : x ∉ Set.range b.targetIsomorphismLocus.ι) :
      (2 : WithBot ℕ∞) ≤ ringKrullDim (X.presheaf.stalk x) := by
    rw [ringKrullDim_stalk_eq_coheight]
    apply WithBot.coe_le_coe.mpr
    apply (ENat.add_one_le_iff (by simp : (1 : ℕ∞) ≠ ⊤)).mpr
    apply lt_of_not_ge
    intro hxone
    obtain ⟨U, hxU, hU⟩ :=
      exists_isIso_restrict_of_isProper_birational_at_coheight_le_one b hff hX x hxone
    apply hx
    exact ⟨⟨x, b.le_targetIsomorphismLocus U hU hxU⟩, rfl⟩
  obtain ⟨Z, i, hi, hcomp, hdimZ⟩ :=
    b.targetIsomorphismLocus.ι.exists_closedComplement_topologicalKrullDim_le_of_codimension
      d 2 hdim hcodim
  exact ⟨b.targetIsomorphismLocus, Z, i,
    b.isIso_restrict_targetIsomorphismLocus, hi, hcomp, hdimZ⟩

end AlgebraicGeometry.Scheme
