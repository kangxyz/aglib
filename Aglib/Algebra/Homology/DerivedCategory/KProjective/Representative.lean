/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Mathlib.Algebra.Homology.DerivedCategory.KProjective

/-!
# Actual chain representatives from native K-projective sources

Native K-projectivity makes every displayed derived morphism out of the
original source representable by an actual chain map. The original derived
morphism is retained as the literal `Q.map` value. For an actual derived
isomorphism this same representative is a quasi-isomorphism, without any
projectivity condition on its target.
-/

@[expose] public section

noncomputable section

universe u v w

open CategoryTheory CategoryTheory.Limits

namespace CochainComplex.IsKProjective

variable {C : Type u} [Category.{v} C] [Abelian C] [HasDerivedCategory.{w} C]
  (P L : CochainComplex C ℤ) [P.IsKProjective]

/-- Every actual native derived morphism from a K-projective source is the
literal localization of an actual chain map. -/
theorem Q_map_surjective :
    Function.Surjective (DerivedCategory.Q.map : (P ⟶ L) →
      (DerivedCategory.Q.obj P ⟶ DerivedCategory.Q.obj L)) := by
  intro a
  let α := DerivedCategory.quotientCompQhIso C
  obtain ⟨g, hg⟩ := (Qh_map_bijective P ((HomotopyCategory.quotient C (.up ℤ)).obj L)).surjective
    (α.hom.app P ≫ a ≫ α.inv.app L)
  obtain ⟨u, hu⟩ := (HomotopyCategory.quotient C (.up ℤ)).map_surjective g
  refine ⟨u, (cancel_epi (α.hom.app P)).mp ?_⟩
  calc
    α.hom.app P ≫ DerivedCategory.Q.map u =
        DerivedCategory.Qh.map ((HomotopyCategory.quotient C (.up ℤ)).map u) ≫ α.hom.app L :=
      (α.hom.naturality u).symm
    _ = (α.hom.app P ≫ a ≫ α.inv.app L) ≫ α.hom.app L := by rw [hu, hg]
    _ = α.hom.app P ≫ a := by
      simp only [Category.assoc, Iso.inv_hom_id_app, Category.comp_id]

/-- An actual derived isomorphism from a K-projective source has an actual
quasi-isomorphism representative with exactly the original forward map
under native localization. No target projectivity is assumed. -/
theorem exists_quasiIso_of_derivedIso
    (e : DerivedCategory.Q.obj P ≅ DerivedCategory.Q.obj L) :
    ∃ u : P ⟶ L, QuasiIso u ∧ DerivedCategory.Q.map u = e.hom := by
  obtain ⟨u, hu⟩ := (Q_map_surjective P L) e.hom
  refine ⟨u, ?_, hu⟩
  apply (DerivedCategory.isIso_Q_map_iff_quasiIso C u).mp
  rw [hu]
  infer_instance

end CochainComplex.IsKProjective
