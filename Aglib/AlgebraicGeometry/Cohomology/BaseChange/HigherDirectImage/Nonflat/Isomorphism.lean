/-
Copyright (c) 2026 algebraic-geometry contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.Cohomology.BaseChange.HigherDirectImage.Nonflat
public import Aglib.AlgebraicGeometry.Cohomology.BaseChange.HigherDirectImage.Nonflat.ChartCriterion
public import Aglib.AlgebraicGeometry.Cohomology.BaseChange.HigherDirectImage.Nonflat.CoefficientIso
public import Aglib.AlgebraicGeometry.Modules.Locality.Exactness

/-! # Detecting the canonical nonflat comparison on chosen affine charts

Original scalar base-change isomorphisms on any chosen covering family of
affine chart pairs imply that the actual global sheaf comparison is invertible.
The cover index universe is independent of the scheme universe.
-/

@[expose] public section

noncomputable section

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

universe u v

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

namespace AlgebraicGeometry.Scheme.Modules

variable {W U V X : Scheme.{u}}
  (a : W ⟶ U) (b : W ⟶ V) (f : U ⟶ X) (g : V ⟶ X)
  (h : IsPullback a b f g) [QuasiCompact f] [QuasiSeparated f]
  (n : ℕ) (M : U.Modules) [M.IsQuasicoherent]

/-- The original scalar maps on any chosen covering family of affine chart pairs detect
invertibility of the canonical sheaf comparison, without finiteness of the new base. -/
theorem higherDirectImageBaseChangeMap_isIso_of_affineCharts
    {ι : Type v} (C : ι → Nonflat.AffineBaseChangeChart g)
    (hcover : ∀ x : V, ∃ (i : ι) (y : Spec (C i).targetRing), (C i).target y = x)
    (hβ : ∀ i, IsIso (Cohomology.moduleCohomologyBaseChangeMap
      (Limits.pullback.snd f (C i).source) (C i).scalar.hom
      (M.restrict (Limits.pullback.fst f (C i).source)) n)) :
    IsIso (higherDirectImageBaseChangeMap a b f g h n M) := by
  apply isIso_of_restrict_openCover (fun i => Spec (C i).targetRing)
    (fun i => (C i).target) hcover
  intro i
  rw [higherDirectImageBaseChangeMap_chart]
  exact (Nonflat.chartMap_isIso_iff a b f g h
    (C i).source (C i).target (C i).scalar (C i).comm n M).mpr (hβ i)

/-- The chosen-chart criterion in the original ordinary-pullback coefficient presentation,
through the actual restriction/pullback coefficient isomorphism and original scalar maps. -/
theorem higherDirectImageBaseChangeMap_isIso_of_affineCharts_pullback
    {ι : Type v} (C : ι → Nonflat.AffineBaseChangeChart g)
    (hcover : ∀ x : V, ∃ (i : ι) (y : Spec (C i).targetRing), (C i).target y = x)
    (hβ : ∀ i, IsIso (Cohomology.moduleCohomologyBaseChangeMap
      (Limits.pullback.snd f (C i).source) (C i).scalar.hom
      ((pullback (Limits.pullback.fst f (C i).source)).obj M) n)) :
    IsIso (higherDirectImageBaseChangeMap a b f g h n M) := by
  apply higherDirectImageBaseChangeMap_isIso_of_affineCharts a b f g h n M C hcover
  intro i
  exact (Cohomology.moduleCohomologyBaseChangeMap_isIso_iff_of_coefficientIso
    (Limits.pullback.snd f (C i).source) (C i).scalar.hom
    ((restrictFunctorIsoPullback (Limits.pullback.fst f (C i).source)).app M) n).mpr (hβ i)

/-- On every actual chart pair, the global comparison's section-surjectivity condition is
the original scalar base-change condition, with no replacement cohomology groups. -/
theorem higherDirectImageBaseChangeMap_chart_sections_epi_iff
    (C : Nonflat.AffineBaseChangeChart g) :
    Epi (moduleSpecΓFunctor.map
      ((restrictFunctor C.target).map (higherDirectImageBaseChangeMap a b f g h n M))) ↔
      Epi (Cohomology.moduleCohomologyBaseChangeMap
        (Limits.pullback.snd f C.source) C.scalar.hom
        (M.restrict (Limits.pullback.fst f C.source)) n) := by
  rw [higherDirectImageBaseChangeMap_chart]
  exact Nonflat.chartMap_sections_epi_iff a b f g h C.source C.target C.scalar C.comm n M

/-- The actual chart section-surjectivity condition equals the original scalar condition
with ordinary pullback coefficients, through the original coefficient isomorphism. -/
theorem higherDirectImageBaseChangeMap_chart_sections_epi_iff_pullback
    (C : Nonflat.AffineBaseChangeChart g) :
    Epi (moduleSpecΓFunctor.map
      ((restrictFunctor C.target).map (higherDirectImageBaseChangeMap a b f g h n M))) ↔
      Epi (Cohomology.moduleCohomologyBaseChangeMap
        (Limits.pullback.snd f C.source) C.scalar.hom
        ((pullback (Limits.pullback.fst f C.source)).obj M) n) :=
  (higherDirectImageBaseChangeMap_chart_sections_epi_iff a b f g h n M C).trans
    (Cohomology.moduleCohomologyBaseChangeMap_epi_iff_of_coefficientIso
      (Limits.pullback.snd f C.source) C.scalar.hom
      ((restrictFunctorIsoPullback (Limits.pullback.fst f C.source)).app M) n)

/-- Over an actual affine target, surjectivity on the whole target's original sections is
the original scalar condition on any source affine chart through which the target factors.
This applies in particular to the actual residue-field morphism. -/
theorem higherDirectImageBaseChangeMap_specTarget_sections_epi_iff_pullback
    {K R : Type u} [CommRing K] [CommRing R] {W U X : Scheme.{u}}
    (a : W ⟶ U) (b : W ⟶ Spec (CommRingCat.of K)) (f : U ⟶ X)
    (g : Spec (CommRingCat.of K) ⟶ X) (h : IsPullback a b f g)
    [QuasiCompact f] [QuasiSeparated f] (n : ℕ) (M : U.Modules) [M.IsQuasicoherent]
    (j : Spec (CommRingCat.of R) ⟶ X) [IsOpenImmersion j] (σ : R →+* K)
    (hσ : Spec.map (CommRingCat.ofHom σ) ≫ j = g) :
    Epi (moduleSpecΓFunctor.map (higherDirectImageBaseChangeMap a b f g h n M)) ↔
      Epi (Cohomology.moduleCohomologyBaseChangeMap (Limits.pullback.snd f j) σ
        ((pullback (Limits.pullback.fst f j)).obj M) n) := by
  let C : Nonflat.AffineBaseChangeChart g :=
    { sourceRing := CommRingCat.of R
      targetRing := CommRingCat.of K
      source := j
      target := 𝟙 (Spec (CommRingCat.of K))
      scalar := CommRingCat.ofHom σ
      source_open := inferInstance
      target_open := inferInstance
      comm := by simpa only [Category.id_comp] using hσ }
  let β := higherDirectImageBaseChangeMap a b f g h n M
  let G := moduleSpecΓFunctor (R := CommRingCat.of K)
  let I := restrictFunctorId (X := Spec (CommRingCat.of K))
  have hi : Epi (G.map ((restrictFunctor (𝟙 (Spec (CommRingCat.of K)))).map β)) ↔
      Epi (G.map β) := by
    rw [← epi_comp_iff_of_isIso
      (G.map ((restrictFunctor (𝟙 (Spec (CommRingCat.of K)))).map β))
      (G.map (I.hom.app _)), ← G.map_comp, I.hom.naturality β, G.map_comp,
      epi_comp_iff_of_epi]
    simp only [Functor.id_map]
  exact hi.symm.trans
    (higherDirectImageBaseChangeMap_chart_sections_epi_iff_pullback a b f g h n M C)

end AlgebraicGeometry.Scheme.Modules
