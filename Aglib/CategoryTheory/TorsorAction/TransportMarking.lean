/-
Copyright (c) 2026 kangxyz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.CategoryTheory.TorsorAction.KernelMarkingOrbits

/-!
# Transport of a genuine kernel marking along a specified commuting group-object isomorphism.

Source: `lean/R5Lab/Aglib/CategoryTheory/TorsorAction/TransportMarking.lean`
at frozen R5 `f8a3314ddecffcada2ec721d26d56a937bed9690`.
SHA-256: `0924b16e6d79b22c447860aada4bc758397e07a177d064851613908a4f29622e`.
Native objects and canonical maps are reused; provenance does not select declaration namespaces.
-/

@[expose] public section

noncomputable section
open CategoryTheory MonoidalCategory CartesianMonoidalCategory MonObj
open scoped CategoryTheory.MonObj
open _root_.CategoryTheory
namespace CategoryTheory.KernelMarking
universe v u
section Transport

variable {C : Type u} [Category.{v} C] [CartesianMonoidalCategory C]
  {A G G' E : Grp C} {p : G ⟶ E} {q : G' ⟶ E}

/-- Transport an actual universal kernel marking across a commuting source-group isomorphism.
Source: auxiliary forget-marking argument at the module snapshot. -/
def transport (m : KernelMarking A G E p) (e : G ≅ G')
    (h : e.hom ≫ q = p) : KernelMarking A G' E q where
  inclusion := m.inclusion ≫ e.hom
  over := by
    have he : e.hom.hom.hom ≫ q.hom.hom = p.hom.hom :=
      congrArg (fun z : G ⟶ E => z.hom.hom) h
    simp only [Grp.comp_hom_hom, Category.assoc, he, m.over]
  unique_lift k hk := by
    have he : e.inv ≫ p = q := by rw [← h]; simp
    have he' : e.inv.hom.hom ≫ p.hom.hom = q.hom.hom :=
      congrArg (fun z : G' ⟶ E => z.hom.hom) he
    have hih : e.inv.hom.hom ≫ e.hom.hom.hom = 𝟙 G'.X :=
      congrArg (fun z : G' ⟶ G' => z.hom.hom) e.inv_hom_id
    have hhi : e.hom.hom.hom ≫ e.inv.hom.hom = 𝟙 G.X :=
      congrArg (fun z : G ⟶ G => z.hom.hom) e.hom_inv_id
    obtain ⟨a, ha, hu⟩ := m.unique_lift (k ≫ e.inv.hom.hom)
      (by rw [Category.assoc, he']; exact hk)
    refine ⟨a, ?_, ?_⟩
    · change a ≫ (m.inclusion.hom.hom ≫ e.hom.hom.hom) = k
      rw [← Category.assoc, ha, Category.assoc, hih, Category.comp_id]
    · intro b hb
      apply hu b
      have hb' := congrArg (fun z => z ≫ e.inv.hom.hom) hb
      simpa only [Grp.comp_hom_hom, Category.assoc, hhi, Category.comp_id] using hb'

end Transport
end CategoryTheory.KernelMarking
