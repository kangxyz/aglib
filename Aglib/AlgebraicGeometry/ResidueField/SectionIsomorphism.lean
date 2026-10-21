/-
Copyright (c) 2026 kangxyz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Mathlib.AlgebraicGeometry.ResidueField
public import Mathlib.AlgebraicGeometry.PullbackCarrier

/-!
# Residue-field isomorphisms along sections and open charts

Source actual residueFieldMap isomorphisms along sections and open charts, including literal
cartesian second-projection formula.

Source: `R5Lab.Aglib.AlgebraicGeometry.ResidueField.SectionIsomorphism`, frozen R5
`f8a3314ddecffcada2ec721d26d56a937bed9690`, SHA-256
`76758aa413b2d47d5946a2e1b3671cac67c600ba6a174a635525d790ee9215be`. Selected lines: [[28, 81]].
The actual objects, canonical maps, universes and stated premises are retained.
-/

@[expose] public section

noncomputable section
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory Limits AlgebraicGeometry
universe u

namespace AlgebraicGeometry

/-- A section induces an isomorphism of residue fields at every actual point.
This uses the exact section triangle, not just existence of a field point. -/
theorem residueFieldMap_isIso_of_section {X Y : Scheme.{u}} (p : X ⟶ Y)
    (s : Y ⟶ X) (h : p ≫ s = 𝟙 X) (x : X) : IsIso (p.residueFieldMap x) := by
  have hc : IsIso (s.residueFieldMap (p x) ≫ p.residueFieldMap x) := by
    have : IsIso ((p ≫ s).residueFieldMap x) := by
      rw [h]
      simp only [Scheme.residueFieldMap_id]
      exact inferInstanceAs (IsIso (𝟙 (X.residueField x)))
    simpa only [Scheme.residueFieldMap_comp] using this
  apply (ConcreteCategory.isIso_iff_bijective _).mpr
  refine ⟨(p.residueFieldMap x).hom.injective, ?_⟩
  exact Function.Surjective.of_comp
    (ConcreteCategory.bijective_of_isIso (s.residueFieldMap (p x) ≫ p.residueFieldMap x)).surjective

/-- At a point supplied by two compatible sections over the same scheme, the
intervening morphism has an isomorphism on residue fields. -/
theorem residueFieldMap_isIso_at_section {S X Y : Scheme.{u}}
    (r : S ⟶ X) (f : X ⟶ Y) (s : Y ⟶ S)
    (h : r ≫ f ≫ s = 𝟙 S) (x : S) : IsIso (f.residueFieldMap (r x)) := by
  let : IsIso (r.residueFieldMap x) := residueFieldMap_isIso_of_section r (f ≫ s) h x
  have : IsIso ((r ≫ f).residueFieldMap x) :=
    residueFieldMap_isIso_of_section (r ≫ f) s (by simpa only [Category.assoc] using h) x
  let : IsIso (f.residueFieldMap (r x) ≫ r.residueFieldMap x) := by
    simpa only [Scheme.residueFieldMap_comp] using this
  exact IsIso.of_isIso_comp_right (f.residueFieldMap (r x)) (r.residueFieldMap x)

/-- An actual open chart on which the composite is an open immersion gives a
residue-field isomorphism at every point in that chart. -/
theorem residueFieldMap_isIso_of_open_chart {V X Y : Scheme.{u}}
    (j : V ⟶ X) (f : X ⟶ Y) [IsOpenImmersion j] [IsOpenImmersion (j ≫ f)]
    (x : X) (hx : x ∈ Set.range j) : IsIso (f.residueFieldMap x) := by
  obtain ⟨v, rfl⟩ := hx
  have : IsIso ((j ≫ f).residueFieldMap v) := inferInstance
  let : IsIso (f.residueFieldMap (j v) ≫ j.residueFieldMap v) := by
    simpa only [Scheme.residueFieldMap_comp] using this
  exact IsIso.of_isIso_comp_right (f.residueFieldMap (j v)) (j.residueFieldMap v)

/-- Base change preserves the actual open-chart residue-field comparison. -/
theorem pullback_snd_residueFieldMap_isIso_of_open_chart {V N C Z : Scheme.{u}}
    (j : V ⟶ N) (n : N ⟶ C) (f : Z ⟶ C)
    [IsOpenImmersion j] [IsOpenImmersion (j ≫ n)]
    (a : ↑(pullback n f)) (ha : pullback.fst n f a ∈ Set.range j) :
    IsIso ((pullback.snd n f).residueFieldMap a) := by
  let r := pullback.snd j (pullback.fst n f)
  have hs : IsPullback (pullback.fst j (pullback.fst n f))
      (r ≫ pullback.snd n f) (j ≫ n) f :=
    (IsPullback.of_hasPullback j (pullback.fst n f)).paste_vert
      (IsPullback.of_hasPullback n f)
  let : IsOpenImmersion (r ≫ pullback.snd n f) :=
    MorphismProperty.of_isPullback hs inferInstance
  apply residueFieldMap_isIso_of_open_chart r (pullback.snd n f) a
  change a ∈ Set.range (pullback.snd j (pullback.fst n f))
  rw [Scheme.Pullback.range_snd]
  exact ha

end AlgebraicGeometry
