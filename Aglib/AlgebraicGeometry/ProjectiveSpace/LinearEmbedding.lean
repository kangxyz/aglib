/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.ProjectiveSpace.Structure
public import Aglib.AlgebraicGeometry.ProjectiveSpectrum.ClosedImmersion

/-!
# Linear closed immersions of projective spaces

For an injective map of coordinate types `j : ι → κ`, Mathlib's `R`-algebra map
`MvPolynomial.killCompl hj : R[κ] → R[ι]` sends `X (j i)` to `X i` and every other variable to
`0`. It preserves the total-degree grading and is surjective in every degree, with the renaming
`rename j` as a degreewise section (`MvPolynomial.gradedKillCompl`,
`MvPolynomial.gradedKillCompl_degreewise_surjective`). Its native `Proj.map` is the **linear
embedding** `ProjectiveSpace.linearEmbedding R hj : P(ι)_R ⟶ P(κ)_R`, the inclusion of the
coordinate linear subspace on which the coordinates outside `j(ι)` vanish. It is a closed immersion
(`ProjectiveSpace.isClosedImmersion_linearEmbedding`, from
`Proj.map_isClosedImmersion_of_degreewise_surjective`) and lies over `Spec R`
(`ProjectiveSpace.linearEmbedding_toSpec`).

Source: a graded ring map `ψ : A → B` with `A_d → B_d` surjective for `d ≫ 0` induces a closed
immersion `Proj B ⟶ Proj A` (Stacks, Lemma 27.11.3, Tag 01N0; the morphism is that of
Lemma 27.11.1, Tag 01MY), applied to `killCompl hj`, which is surjective in every degree. For
`ι = Fin (n + 1)` and `κ = Fin (m + 1)` this is the inclusion of a coordinate linear subspace
`P^n_R ⊆ P^m_R`; the Stacks Project states no separate lemma for it. No finiteness of `ι` or `κ`
and no hypothesis on the commutative ring `R` are needed. Consumer: finite disjoint unions of
H-quasi-projective schemes, `Aglib.AlgebraicGeometry.ProjectiveSpace.QuasiProjective.Coproduct`
(Picard plan task HQ3).
-/

@[expose] public section

noncomputable section

-- File-wide, following the other `ProjectiveSpace` leaves.
set_option backward.isDefEq.respectTransparency false

open CategoryTheory

universe u v w

attribute [local instance] MvPolynomial.gradedAlgebra

namespace MvPolynomial

variable (R : Type u) [CommRing R] {ι : Type v} {κ : Type w} {j : ι → κ}
  (hj : Function.Injective j)

open scoped Classical in
/-- Mathlib's `killCompl hj : R[κ] → R[ι]`, which sends `X (j i)` to `X i` and the variables
outside the range of `j` to `0`, as a map of total-degree graded rings. -/
def gradedKillCompl : homogeneousSubmodule κ R →+*ᵍ homogeneousSubmodule ι R where
  __ := (killCompl hj).toRingHom
  map_mem {n} {p} hp := by
    have h := IsHomogeneous.aeval (S := R) (n := 1) ((mem_homogeneousSubmodule n p).mp hp)
      (fun k => if h : k ∈ Set.range j then X ((Equiv.ofInjective j hj).symm ⟨k, h⟩) else 0)
      (fun k => by
        split_ifs
        · exact isHomogeneous_X R _
        · exact isHomogeneous_zero _ _ _)
    rw [one_mul] at h
    exact (mem_homogeneousSubmodule n _).mpr h

@[simp]
theorem gradedKillCompl_apply (p : MvPolynomial κ R) :
    gradedKillCompl R hj p = killCompl hj p := rfl

/-- The graded `killCompl` is surjective in every degree: `rename j` is a degreewise section. -/
theorem gradedKillCompl_degreewise_surjective (n : ℕ) :
    Function.Surjective ((gradedKillCompl R hj).gradedAddHom n) := by
  intro q
  refine ⟨⟨rename j (q : MvPolynomial ι R), (mem_homogeneousSubmodule n _).mpr
    ((mem_homogeneousSubmodule n _).mp q.property).rename_isHomogeneous⟩, Subtype.ext ?_⟩
  exact killCompl_rename_app hj _

/-- The graded `killCompl` maps the irrelevant ideal onto the irrelevant ideal; in particular it
satisfies the hypothesis of `Proj.map`. -/
theorem irrelevant_le_map_gradedKillCompl :
    HomogeneousIdeal.irrelevant (homogeneousSubmodule ι R) ≤
      (HomogeneousIdeal.irrelevant (homogeneousSubmodule κ R)).map (gradedKillCompl R hj) := by
  apply toIdeal_le_toIdeal_iff.mp
  rw [HomogeneousIdeal.toIdeal_irrelevant_le]
  intro n hn p hp
  obtain ⟨a, ha⟩ := gradedKillCompl_degreewise_surjective R hj n ⟨p, hp⟩
  have he : gradedKillCompl R hj (a : MvPolynomial κ R) = p := congrArg Subtype.val ha
  rw [← he]
  exact Ideal.mem_map_of_mem _ (HomogeneousIdeal.mem_irrelevant_of_mem _ hn a.property)

end MvPolynomial

namespace AlgebraicGeometry.ProjectiveSpace

variable (R : Type u) [CommRing R] {ι κ : Type u} {j : ι → κ} (hj : Function.Injective j)

/-- The **linear embedding** `P(ι)_R ⟶ P(κ)_R` of an injective map of coordinate types
`j : ι → κ`: the native `Proj.map` of the graded `killCompl`, the inclusion of the coordinate
linear subspace on which the coordinates outside `j(ι)` vanish. -/
def linearEmbedding : ProjectiveSpace R ι ⟶ ProjectiveSpace R κ :=
  Proj.map (MvPolynomial.gradedKillCompl R hj) (MvPolynomial.irrelevant_le_map_gradedKillCompl R hj)

/-- **The linear embedding is a closed immersion**: the graded `killCompl` is surjective in every
degree. -/
instance isClosedImmersion_linearEmbedding : IsClosedImmersion (linearEmbedding R hj) :=
  Proj.map_isClosedImmersion_of_degreewise_surjective _ _
    (MvPolynomial.gradedKillCompl_degreewise_surjective R hj)

/-- The linear embedding lies over `Spec R`. -/
@[reassoc (attr := simp)]
theorem linearEmbedding_toSpec : linearEmbedding R hj ≫ toSpec R κ = toSpec R ι := by
  let f := MvPolynomial.gradedKillCompl R hj
  let hf := MvPolynomial.irrelevant_le_map_gradedKillCompl R hj
  change Proj.map f hf ≫ toSpec R κ = toSpec R ι
  apply (Proj.mapAffineOpenCover f hf).openCover.hom_ext
  intro s
  change (Σ i : ℕ+, MvPolynomial.homogeneousSubmodule κ R i) at s
  change Proj.awayι (MvPolynomial.homogeneousSubmodule ι R) (f s.2) (f.map_mem s.2.2) s.1.2 ≫
      (Proj.map f hf ≫ toSpec R κ) =
    Proj.awayι (MvPolynomial.homogeneousSubmodule ι R) (f s.2) (f.map_mem s.2.2) s.1.2 ≫
      toSpec R ι
  rw [Proj.awayι_comp_map_assoc f hf s.1.2 (s.2 : MvPolynomial κ R) s.2.2]
  simp only [toSpec, Proj.awayι_toSpecZero_assoc, ← Spec.map_comp]
  congr 1
  apply CommRingCat.hom_ext
  apply RingHom.ext
  intro a
  apply HomogeneousLocalization.val_injective
  simp [HomogeneousLocalization.Away.map, HomogeneousLocalization.fromZeroRingHom,
    HomogeneousLocalization.map_mk, f, MvPolynomial.gradedKillCompl,
    MvPolynomial.toHomogeneousSubmoduleZero]

end AlgebraicGeometry.ProjectiveSpace
