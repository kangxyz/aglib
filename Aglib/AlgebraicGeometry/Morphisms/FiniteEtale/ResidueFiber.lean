/-
Copyright (c) 2026 kangxyz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.Spec.ResidueFiber
public import Aglib.AlgebraicGeometry.Morphisms.FiniteEtale.BaseChange
public import Aglib.AlgebraicGeometry.Morphisms.FiniteEtale.ProperHenselian
public import Mathlib.AlgebraicGeometry.Morphisms.FlatRank

/-!
# Literal residue-fibre maps and finite-etale cover restriction

The structural maps and fibres are those in `Spec.ResidueFiber`. The induced
map is the existing actual over-category pullback map. Its cartesian square
compares the same literal source fibre with restriction of the same cover.
Both original projections and the supplied sections are preserved.

Source: unmarked `Origin` and `SourceModel` slices from
`R5Lab.AlgebraicGeometry.Curves.LocalModels.CyclicCovers`, frozen R5
`f8a3314ddecffcada2ec721d26d56a937bed9690`, SHA-256 respectively
`3c7bd17bab5363e790aacf9c9e5821790b27464213f5e58a6021a979accac414` and
`bb898d7efd9798cb5657bffab1cf0ad44d163ab82a1823b05aa0daad889c2fae`.
The final conditional adapter is `Henselian:100`, source SHA-256
`3f8b236c996ceb1d2e43899169911683fb12e6916387b1a67bf7c7fc0067f39f`.
It applies the existing universal comparison input and proves no inhabitant
of that input family. There is no model, marked polygon or purity producer.
-/

@[expose] public noncomputable section

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

namespace AlgebraicGeometry.Scheme.LocalRing.ResidueFiber

universe u

section Maps

variable {R : Type u} [CommRing R] [IsLocalRing R] {X Y : Scheme.{u}}
  (πX : X ⟶ Spec (.of R)) (πY : Y ⟶ Spec (.of R))
  (p : X ⟶ Y) (hp : p ≫ πY = πX)

/-- The actual map on the two literal residue fibres. -/
def map : obj πX ⟶ obj πY :=
  ((Over.pullback (residueSpecMap R)).map
    (Over.homMk p hp : Over.mk πX ⟶ Over.mk πY)).left

@[reassoc (attr := simp)] theorem map_projection :
    map πX πY p hp ≫ projection πY = projection πX ≫ p := by
  simp [map, projection, Over.pullback_map_left]

@[reassoc (attr := simp)] theorem map_structureMap :
    map πX πY p hp ≫ structureMap πY = structureMap πX := by
  simp [map, structureMap, Over.pullback_map_left]

/-- The map is the source's literal three-arrow pullback map. -/
theorem map_eq_pullbackMap :
    map πX πY p hp =
      pullback.map πX (residueSpecMap R) πY (residueSpecMap R) p (𝟙 _) (𝟙 _)
        (by simpa using hp.symm) (by simp) := by
  apply pullback.hom_ext <;> simp [map, Over.pullback_map_left]

/-- The induced map is the actual pullback of the original morphism. -/
theorem map_square :
    IsPullback (projection πX) (map πX πY p hp) p (projection πY) := by
  have h : IsPullback (projection πX) (map πX πY p hp ≫ structureMap πY)
      (p ≫ πY) (residueSpecMap R) := by
    rw [map_structureMap, hp]
    exact IsPullback.of_hasPullback πX (residueSpecMap R)
  exact h.of_bot (map_projection πX πY p hp).symm
    (IsPullback.of_hasPullback πY (residueSpecMap R))

/-- The same source residue fibre is the actual restriction pullback.
Its two projections remain the original scheme maps. -/
def comparisonIso : obj πX ≅ pullback p (projection πY) :=
  (map_square πX πY p hp).isoPullback

@[reassoc (attr := simp)] theorem comparisonIso_hom_fst :
    (comparisonIso πX πY p hp).hom ≫ pullback.fst p (projection πY) = projection πX :=
  (map_square πX πY p hp).isoPullback_hom_fst

@[reassoc (attr := simp)] theorem comparisonIso_hom_snd :
    (comparisonIso πX πY p hp).hom ≫ pullback.snd p (projection πY) = map πX πY p hp :=
  (map_square πX πY p hp).isoPullback_hom_snd

/-- The induced map on actual residue fibres is finite when the original map is finite. -/
instance map_finite [IsFinite p] : IsFinite (map πX πY p hp) :=
  MorphismProperty.of_isPullback (map_square πX πY p hp) inferInstance

/-- The induced map on actual residue fibres is etale when the original map is etale. -/
instance map_etale [Etale p] : Etale (map πX πY p hp) :=
  MorphismProperty.of_isPullback (map_square πX πY p hp) inferInstance

/-- Finite flat rank is transported by the same actual residue-fibre square. -/
theorem finrank_map [Flat p] [IsFinite p] (y : obj πY) :
    (map πX πY p hp).finrank y = p.finrank (projection πY y) :=
  Scheme.Hom.finrank_of_isPullback _ _ _ _ (map_square πX πY p hp) y

/-- Compatible original sections specialize to compatible actual residue points. -/
theorem map_section (σX : Spec (.of R) ⟶ X) (hσX : σX ≫ πX = 𝟙 _)
    (σY : Spec (.of R) ⟶ Y) (hσY : σY ≫ πY = 𝟙 _)
    (hσp : σX ≫ p = σY) :
    ResidueFiber.section πX σX hσX ≫ map πX πY p hp =
      ResidueFiber.section πY σY hσY := by
  apply pullback.hom_ext
  · calc
      (ResidueFiber.section πX σX hσX ≫ map πX πY p hp) ≫ projection πY =
          ResidueFiber.section πX σX hσX ≫ projection πX ≫ p := by
        rw [Category.assoc, map_projection]
      _ = (residueSpecMap R ≫ σX) ≫ p := by
        rw [← Category.assoc, section_projection]
      _ = residueSpecMap R ≫ σY := by rw [Category.assoc, hσp]
      _ = ResidueFiber.section πY σY hσY ≫ projection πY :=
        (section_projection πY σY hσY).symm
  · rw [Category.assoc, map_structureMap, section_structureMap, section_structureMap]

end Maps

section ConditionalComparison

variable {R : Type u} [CommRing R] [HenselianLocalRing R] {Y : Scheme.{u}}

/-- Apply, without discharging, the original universal proper-Henselian
comparison input to this displayed proper structural morphism. -/
theorem isEquivalence_of_properHenselianComparison
    (H : Scheme.FiniteEtale.ProperHenselianComparison R)
    (π : Y ⟶ Spec (.of R)) [IsProper π] :
    (Scheme.FiniteEtale.baseChange (projection π)).IsEquivalence :=
  H Y π inferInstance

end ConditionalComparison

end AlgebraicGeometry.Scheme.LocalRing.ResidueFiber
