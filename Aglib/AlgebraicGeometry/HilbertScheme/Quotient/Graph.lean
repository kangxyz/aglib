/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.HilbertScheme.Quotient.Points
public import Mathlib.AlgebraicGeometry.Morphisms.Separated

/-!
# The graph of the classifying morphism and its two pullbacks

Let `𝔥 = (H, D, φ)` be a Hilbert datum (`QuotientHilbertDatum`) for `πZ : Z ⟶ S` and a closed
immersion `j : R ⟶ Z ×_S Z`, with projections `p₁ = j ≫ pr₁`, `p₂ = j ≫ pr₂` and family projection
`p = 𝔥.familyProj : D ⟶ H`. This file proves the steps of Nitsure, *Construction of Hilbert and
Quot schemes*, arXiv:math/0504590v1, proof of Theorem 6.8, pp. 34–35, between `(***)` and the
application of Lemma 6.7(2):

* `QuotientHilbertDatum.graph`: the graph `(𝟙, φ) : Z ⟶ Z ×_S H`, a closed immersion when `H` is
  separated over `S` (`QuotientHilbertDatum.isClosedImmersion_graph`; p. 34, "as `H` is separated
  over `S`").
* `QuotientHilbertDatum.exists_comp_subschemeι_eq_graph`: the graph factors through `D` as soon as
  the diagonal of `Z` factors through `R` (p. 34, "as `Δ_X ⊂ R` and as `φ^* D = R`"). A
  factorization `Γ` (the closed subscheme `Γ_φ ⊂ D`) is unique, since `D ⟶ Z ×_S H` is a
  monomorphism; the statements below take any `Γ` with `Γ ≫ D.subschemeι = graph`. Such a `Γ` is a
  closed immersion (`isClosedImmersion_of_comp_subschemeι_eq_graph`) with `Γ ≫ p = φ`
  (`comp_familyProj_of_comp_subschemeι_eq_graph`), and a point `d` of `D`, a pair `(x, V)`, lies
  on `Γ` exactly when `V = φ ∘ x` (`exists_comp_eq_iff_of_comp_subschemeι_eq_graph`; p. 34: "Any
  `T`-valued point of `Γ_φ` is a pair `(x, φ(x)) ∈ D(T)` where `x ∈ X(T)`").
* `QuotientHilbertDatum.ker_comap_fst_eq_ker_comap_snd_of_comp_subschemeι_eq_graph`:
  `p₁⁻¹ Γ_φ = p₂⁻¹ Γ_φ ⊂ D ×_H D` (pp. 34–35), the hypothesis of Lemma 6.7(2) for `p` and `Γ_φ`
  (`Scheme.IdealSheafData.comap_map_eq_self_of_flat_of_surjective`).

The last statement is tested on `T`-points of `D ×_H D` for `T` locally Noetherian
(`Scheme.IdealSheafData.comap_eq_comap_of_locallyNoetherian_exists_lift_iff`): `D ×_H D` is
locally Noetherian when `H` is (`p` is proper, so locally of finite type). For a point
`(x, y, V)`, `p₁(x, y, V) = (x, V) ∈ Γ_φ` means `V = φ(x)`; then `y ∈ V = φ(x)`, so `(y, x) ∈ R(T)`
and `φ(y) = φ(x)` by `(***)` (`QuotientHilbertDatum.pointsRelation_iff_comp_eq`), that is,
`p₂(x, y, V) ∈ Γ_φ`; and symmetrically. Nitsure tests all `S`-schemes `T`.
-/

@[expose] public section

noncomputable section

universe u

open CategoryTheory CategoryTheory.Limits

attribute [local simp] pullback.lift_fst pullback.lift_snd pullback.lift_fst_assoc
  pullback.lift_snd_assoc

namespace AlgebraicGeometry.QuotientHilbertDatum

variable {S Z R : Scheme.{u}} {πZ : Z ⟶ S} {j : R ⟶ pullback πZ πZ}
  (𝔥 : QuotientHilbertDatum πZ j)

/-- The graph `(𝟙, φ) : Z ⟶ Z ×_S H` of the classifying morphism (Nitsure, arXiv:math/0504590v1,
p. 34). -/
def graph : Z ⟶ pullback πZ 𝔥.πH :=
  pullback.lift (𝟙 Z) 𝔥.φ (by rw [Category.id_comp, 𝔥.w])

@[reassoc (attr := simp)]
theorem graph_fst : 𝔥.graph ≫ pullback.fst πZ 𝔥.πH = 𝟙 Z :=
  pullback.lift_fst _ _ _

@[reassoc (attr := simp)]
theorem graph_snd : 𝔥.graph ≫ pullback.snd πZ 𝔥.πH = 𝔥.φ :=
  pullback.lift_snd _ _ _

/-- **The graph is a closed immersion** when `H` is separated over `S` (Nitsure,
arXiv:math/0504590v1, p. 34): it is a section of the separated projection `Z ×_S H ⟶ Z`. -/
instance isClosedImmersion_graph [IsSeparated 𝔥.πH] : IsClosedImmersion 𝔥.graph := by
  have : IsClosedImmersion (𝔥.graph ≫ pullback.fst πZ 𝔥.πH) := by
    rw [graph_fst]
    infer_instance
  exact IsClosedImmersion.of_comp 𝔥.graph (pullback.fst πZ 𝔥.πH)

/-- **The graph factors through `D`** (Nitsure, arXiv:math/0504590v1, p. 34): if the diagonal of
`Z` factors through `R`, that is, every point of `Z` is `R`-related to itself at `T = Z`, then
`(𝟙, φ)` factors through `D`. -/
theorem exists_comp_subschemeι_eq_graph [IsClosedImmersion j]
    (hrefl : pointsRelation (j ≫ pullback.fst πZ πZ) (j ≫ pullback.snd πZ πZ) Z (𝟙 Z) (𝟙 Z)) :
    ∃ Γ : Z ⟶ 𝔥.D.subscheme, Γ ≫ 𝔥.D.subschemeι = 𝔥.graph := by
  obtain ⟨Γ, hΓ⟩ :=
    (𝔥.exists_lift_subschemeι_iff_pointsRelation (𝟙 Z) (𝟙 Z) (by simp [𝔥.w])).mpr hrefl
  exact ⟨Γ, hΓ.trans (pullback.hom_ext (by simp) (by simp))⟩

variable {𝔥} {Γ : Z ⟶ 𝔥.D.subscheme} (hΓ : Γ ≫ 𝔥.D.subschemeι = 𝔥.graph)
include hΓ

/-- `Γ_φ` maps to `H` by `φ`: `Γ ≫ p = φ`. -/
theorem comp_familyProj_of_comp_subschemeι_eq_graph : Γ ≫ 𝔥.familyProj = 𝔥.φ := by
  rw [familyProj, ← Category.assoc, hΓ, graph_snd]

/-- **`Γ_φ` is a closed subscheme of `D`** when `H` is separated over `S`. -/
theorem isClosedImmersion_of_comp_subschemeι_eq_graph [IsSeparated 𝔥.πH] :
    IsClosedImmersion Γ := by
  have : IsClosedImmersion (Γ ≫ 𝔥.D.subschemeι) := by
    rw [hΓ]
    infer_instance
  exact IsClosedImmersion.of_comp Γ 𝔥.D.subschemeι

/-- **Points of `Γ_φ`** (Nitsure, arXiv:math/0504590v1, p. 34): a `T`-point `d = (x, V)` of `D`
factors through `Γ` if and only if `V = φ ∘ x`. -/
theorem exists_comp_eq_iff_of_comp_subschemeι_eq_graph {T : Scheme.{u}}
    (d : T ⟶ 𝔥.D.subscheme) :
    (∃ z : T ⟶ Z, z ≫ Γ = d) ↔
      (d ≫ 𝔥.D.subschemeι ≫ pullback.fst πZ 𝔥.πH) ≫ 𝔥.φ = d ≫ 𝔥.familyProj := by
  constructor
  · rintro ⟨z, rfl⟩
    simp [reassoc_of% hΓ, familyProj]
  · intro h
    refine ⟨d ≫ 𝔥.D.subschemeι ≫ pullback.fst πZ 𝔥.πH, ?_⟩
    rw [← cancel_mono 𝔥.D.subschemeι]
    simp only [Category.assoc, hΓ]
    apply pullback.hom_ext
    · simp
    · simpa [familyProj] using h

/-- **`p₁⁻¹ Γ_φ = p₂⁻¹ Γ_φ`** (Nitsure, arXiv:math/0504590v1, pp. 34–35): the two pullbacks of
the closed subscheme `Γ_φ ⊂ D` to `D ×_H D` agree. Here `j` is a closed immersion whose relation
on locally Noetherian points is an equivalence relation, `πZ` is locally of finite type, `H` is
separated over `S` and locally Noetherian; the equality is tested on locally Noetherian points
of `D ×_H D`. -/
theorem ker_comap_fst_eq_ker_comap_snd_of_comp_subschemeι_eq_graph [IsClosedImmersion j]
    [LocallyOfFiniteType πZ] [IsSeparated 𝔥.πH] [IsLocallyNoetherian 𝔥.H]
    (hequiv : ∀ (T : Scheme.{u}) [IsLocallyNoetherian T],
      _root_.Equivalence (pointsRelation (j ≫ pullback.fst πZ πZ) (j ≫ pullback.snd πZ πZ) T)) :
    Γ.ker.comap (pullback.fst 𝔥.familyProj 𝔥.familyProj) =
      Γ.ker.comap (pullback.snd 𝔥.familyProj 𝔥.familyProj) := by
  have := isClosedImmersion_of_comp_subschemeι_eq_graph hΓ
  have : IsLocallyNoetherian 𝔥.D.subscheme := LocallyOfFiniteType.isLocallyNoetherian 𝔥.familyProj
  refine Scheme.IdealSheafData.comap_eq_comap_of_locallyNoetherian_exists_lift_iff _ _ _
    fun T _ t => ?_
  rw [Scheme.IdealSheafData.exists_lift_subschemeι_iff_le_ker,
    Scheme.IdealSheafData.exists_lift_subschemeι_iff_le_ker,
    ← Scheme.Hom.exists_lift_iff_ker_le_ker, ← Scheme.Hom.exists_lift_iff_ker_le_ker,
    exists_comp_eq_iff_of_comp_subschemeι_eq_graph hΓ,
    exists_comp_eq_iff_of_comp_subschemeι_eq_graph hΓ]
  have hc : (t ≫ pullback.fst 𝔥.familyProj 𝔥.familyProj) ≫ 𝔥.familyProj =
      (t ≫ pullback.snd 𝔥.familyProj 𝔥.familyProj) ≫ 𝔥.familyProj := by
    rw [Category.assoc, Category.assoc, pullback.condition]
  constructor
  · intro h₁
    have hr := 𝔥.pointsRelation_of_comp_familyProj_eq _ _ (hc.symm.trans h₁.symm)
    rw [(𝔥.pointsRelation_iff_comp_eq hequiv _ _).mp hr, h₁, hc]
  · intro h₂
    have hr := 𝔥.pointsRelation_of_comp_familyProj_eq _ _ (hc.trans h₂.symm)
    rw [(𝔥.pointsRelation_iff_comp_eq hequiv _ _).mp hr, h₂, hc]

end AlgebraicGeometry.QuotientHilbertDatum
