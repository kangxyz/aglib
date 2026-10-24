/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.Picard.Scheme.Stratification

/-!
# The Picard scheme is separated

In the setting of [Glue](Glue.lean) (`i : X ⟶ P^N_A` a closed immersion with `ι ≃ Fin (N + 1)`,
`p = i ≫ toSpec A ι` flat with geometrically integral fibres, and the representability premise
`h : Strata.FineStrataRepresentableByHQuasiProjective i N e`), the Picard scheme
`picardScheme h` is separated over `Spec A` (`isSeparated_picardScheme`; Kleiman,
*The Picard scheme*, arXiv:math/0504020v1, Thm 4.8 (1)). No Noetherian hypothesis on `A` is used.

Proof (Kleiman p. 28: "Plainly an `S`-scheme is separated if it is a disjoint union of separated
open subschemes, or if it is an increasing union of separated open subschemes"). The charts are
H-quasi-projective, hence separated over `Spec A`, and for fixed `(φ, ψ, m)` the chart images of the
ranks `k + 1` are pairwise disjoint with union `Pic^{φ,ψ}_m = picardBaseLevelOpens h φ ψ m`, so each
`Pic^{φ,ψ}_m` is separated (`isSeparated_ι_comp_of_iSup_eq_of_pairwise_disjoint`). The
`Pic^{φ,ψ}_m` cover the Picard scheme, increase with `m` and are disjoint for distinct `(φ, ψ)`, so
`isSeparated_of_cover_of_disjoint_of_monotone` applies. A chart image of `Pic^{φ,ψ}_m` need not lie
in a single chart at a larger level, since the rank `h^0(X_t, L_t(m'))` varies, which is why the
ranks are first collected into `Pic^{φ,ψ}_m`.
-/

@[expose] public section

noncomputable section

universe u

open CategoryTheory CategoryTheory.Limits Opposite AlgebraicGeometry
open AlgebraicGeometry.ProjectiveSpace
open AlgebraicGeometry.Scheme.LocalRepresentability

namespace AlgebraicGeometry.Scheme.RelativePicard

open Strata

variable {A : Type u} [CommRing A] {ι : Type u} {X : Scheme.{u}}
  {i : X ⟶ ProjectiveSpace A ι} [IsClosedImmersion i] [Flat (i ≫ toSpec A ι)]
  [GeometricallyIntegral (i ≫ toSpec A ι)] {N : ℕ} {e : ι ≃ Fin (N + 1)}
  (h : FineStrataRepresentableByHQuasiProjective i N e)

/-- The open of each fine stratum `Pic^{φ,ψ,k+1}_m` is separated over `Spec A`: it is the image of
an H-quasi-projective chart. -/
theorem isSeparated_fineCondition_opens (φ ψ : Polynomial ℚ) (m : ℤ) (k : ℕ) :
    IsSeparated (((fineCondition i N e φ ψ m (k + 1)).opens (picardUniversalSection h)).ι ≫
      (picardScheme h).obj.hom) := by
  have hr : Set.range ((picardSubfunctorCover h).ιp (ULift.up (φ, ψ, m, k))).hom.left =
      Set.range ((fineCondition i N e φ ψ m (k + 1)).opens (picardUniversalSection h)).ι := by
    rw [range_picardChart_mk, Scheme.Opens.range_ι]
  exact (isSeparated_comp_iff_of_range_eq _ _ hr _).mp inferInstance

/-- **`Pic^{φ,ψ}_m` is separated over `Spec A`**: it is the disjoint union of the separated chart
images of the ranks `k + 1` (Kleiman, arXiv:math/0504020v1, proof of Thm 4.8, p. 28, disjoint
unions). -/
theorem isSeparated_picardBaseLevelOpens (φ ψ : Polynomial ℚ) (m : ℤ) :
    IsSeparated ((picardBaseLevelOpens h φ ψ m).ι ≫ (picardScheme h).obj.hom) :=
  isSeparated_ι_comp_of_iSup_eq_of_pairwise_disjoint _ _ _
    (iSup_fineCondition_opens_eq_picardBaseLevelOpens h φ ψ m)
    (isSeparated_fineCondition_opens h φ ψ m) (pairwise_disjoint_fineCondition_opens h φ ψ m)

/-- The `Pic^{φ,ψ}_m` cover the Picard scheme. -/
theorem iSup_picardBaseLevelOpens :
    ⨆ x : Polynomial ℚ × Polynomial ℚ, ⨆ m, picardBaseLevelOpens h x.1 x.2 m = ⊤ := by
  rw [eq_top_iff]
  intro y _
  have hy : y ∈ ⨆ z : Polynomial ℚ × Polynomial ℚ × ℤ × ℕ,
      (fineCondition i N e z.1 z.2.1 z.2.2.1 (z.2.2.2 + 1)).opens (picardUniversalSection h) := by
    rw [iSup_opens_fineCondition_eq_top]
    trivial
  obtain ⟨⟨φ, ψ, m, k⟩, hk⟩ := TopologicalSpace.Opens.mem_iSup.mp hy
  exact TopologicalSpace.Opens.mem_iSup.mpr ⟨(φ, ψ), TopologicalSpace.Opens.mem_iSup.mpr
    ⟨m, fineCondition_opens_le_picardBaseLevelOpens h φ ψ m k hk⟩⟩

/-- The `Pic^{φ,ψ}_m` increase with `m`. -/
theorem monotone_picardBaseLevelOpens (φ ψ : Polynomial ℚ) :
    Monotone (picardBaseLevelOpens h φ ψ) :=
  fun _ _ hm => inf_le_inf_right _ (monotone_picardLevelOpens h φ hm)

/-- The `Pic^{φ,ψ}_m` are disjoint for distinct `(φ, ψ)`. -/
theorem disjoint_picardBaseLevelOpens {x y : Polynomial ℚ × Polynomial ℚ} (hxy : x ≠ y)
    (m m' : ℤ) :
    Disjoint (picardBaseLevelOpens h x.1 x.2 m) (picardBaseLevelOpens h y.1 y.2 m') := by
  by_cases hφ : x.1 = y.1
  · have hψ : x.2 ≠ y.2 := fun hψ => hxy (Prod.ext hφ hψ)
    exact (disjoint_opens_baseCondition (picardUniversalSection h) hψ).mono inf_le_right
      inf_le_right
  · exact Disjoint.mono (inf_le_left.trans (picardLevelOpens_le_picardStratumOpens h x.1 m))
      (inf_le_left.trans (picardLevelOpens_le_picardStratumOpens h y.1 m'))
      (pairwise_disjoint_picardStratumOpens h hφ)

/-- **The Picard scheme is separated over `Spec A`** (Kleiman, arXiv:math/0504020v1, Thm 4.8 (1)
and its proof, p. 28). -/
instance isSeparated_picardScheme : IsSeparated (picardScheme h).obj.hom :=
  isSeparated_of_cover_of_disjoint_of_monotone (picardScheme h).obj.hom
    (fun x : Polynomial ℚ × Polynomial ℚ => picardBaseLevelOpens h x.1 x.2)
    (iSup_picardBaseLevelOpens h) (fun x m => isSeparated_picardBaseLevelOpens h x.1 x.2 m)
    (fun x => monotone_picardBaseLevelOpens h x.1 x.2)
    (fun _ _ m m' hxy => disjoint_picardBaseLevelOpens h hxy m m')

end AlgebraicGeometry.Scheme.RelativePicard
