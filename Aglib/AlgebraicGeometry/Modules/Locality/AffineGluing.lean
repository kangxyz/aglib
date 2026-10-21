/-
Copyright (c) 2026 algebraic-geometry contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.Modules.Locality.Sections
public import Mathlib.Topology.Sheaves.SheafCondition.UniqueGluing

/-! # Gluing module sections from all affine subopens -/

@[expose] public noncomputable section

open CategoryTheory Opposite

namespace AlgebraicGeometry.Scheme.Modules

universe u
variable {X : Scheme.{u}}

/-- Affine subopens of a given open cover it. -/
theorem affineSubopens_cover (V : X.Opens) :
    V ≤ iSup (fun U : {U : X.affineOpens // U.val ≤ V} => U.val.val) := by
  intro x hx
  obtain ⟨_, ⟨U, hU, rfl⟩, hxU, hUV⟩ :=
    X.isBasis_affineOpens.exists_subset_of_mem_open hx V.isOpen
  exact (le_iSup (fun W : {W : X.affineOpens // W.val ≤ V} => W.val.val)
    ⟨⟨U, hU⟩, hUV⟩) hxU

/-- Two sections are equal if their restrictions agree on every affine subopen. -/
theorem section_ext_affineSubopens (M : X.Modules) (V : X.Opens) {s t : Γ(M, V)}
    (h : ∀ (U : X.affineOpens) (i : U.val ⟶ V), M.val.map i.op s = M.val.map i.op t) :
    s = t := by
  apply (show TopCat.Sheaf AddCommGrpCat X from ⟨M.presheaf, M.isSheaf⟩).eq_of_locally_eq'
    (fun U : {U : X.affineOpens // U.val ≤ V} => U.val.val) V
    (fun U => homOfLE U.property) (affineSubopens_cover V)
  intro U
  exact h U.val (homOfLE U.property)

/-- Restriction-compatible sections on all affine subopens glue uniquely. -/
theorem existsUnique_section_of_affineSubopens (M : X.Modules) (V : X.Opens)
    (s : ∀ U : {U : X.affineOpens // U.val ≤ V}, Γ(M, U.val.val))
    (h : ∀ (U W : {U : X.affineOpens // U.val ≤ V}) (i : W.val.val ⟶ U.val.val),
      M.val.map i.op (s U) = s W) :
    ∃! t : Γ(M, V), ∀ U : {U : X.affineOpens // U.val ≤ V},
      M.val.map (homOfLE U.property).op t = s U := by
  apply (show TopCat.Sheaf AddCommGrpCat X from ⟨M.presheaf, M.isSheaf⟩).existsUnique_gluing'
    (fun U : {U : X.affineOpens // U.val ≤ V} => U.val.val) V
    (fun U => homOfLE U.property) (affineSubopens_cover V) s
  intro U W
  apply section_ext_affineSubopens M (U.val.val ⊓ W.val.val)
  intro Z i
  let Z' : {Z : X.affineOpens // Z.val ≤ V} :=
    ⟨Z, (leOfHom i).trans (inf_le_left.trans U.property)⟩
  change M.val.map i.op (M.val.map (TopologicalSpace.Opens.infLELeft _ _).op (s U)) =
    M.val.map i.op (M.val.map (TopologicalSpace.Opens.infLERight _ _).op (s W))
  erw [← M.val.map_comp_apply, ← M.val.map_comp_apply]
  exact (h U Z' (i ≫ TopologicalSpace.Opens.infLELeft _ _)).trans
    (h W Z' (i ≫ TopologicalSpace.Opens.infLERight _ _)).symm

end AlgebraicGeometry.Scheme.Modules
