/-
Copyright (c) 2026 kangxyz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/

module

public import Aglib.AlgebraicGeometry.Morphisms.FiniteEtale.Descent.FiniteFieldTransport

/-! A single original index for any finite family of actual overlap arrows. -/

@[expose] public section

noncomputable section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Opposite
namespace AlgebraicGeometry.Scheme.FiniteEtale.FieldCoverDescent
universe u

section GeneralLimit
variable {I : Type u} [Category.{u} I] [IsCofiltered I]
  (D : I ⥤ Scheme.{u}) (c : Cone D) (hc : IsLimit c)
  [∀ {i j} (f : i ⟶ j), IsAffineHom (D.map f)]
  (i : I) {J : Type u} [Finite J] (U V : J → Over (D.obj i))
  [∀ j, CompactSpace (U j).left] [∀ j, QuasiSeparatedSpace (U j).left]
  [∀ j, LocallyOfFinitePresentation (V j).hom]

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
include hc in
/-- The source indices for a finite family of maps can be made identical, still above i. -/
theorem exists_common_tail_hom
    (q : ∀ j, pullback (c.π.app i) (U j).hom ⟶ (V j).left)
    (hq : ∀ j, q j ≫ (V j).hom = pullback.snd (c.π.app i) (U j).hom ≫ (U j).hom) :
    ∃ k : Over i, ∀ j, ∃ g : pullback (D.map k.hom) (U j).hom ⟶ (V j).left,
      g ≫ (V j).hom = pullback.snd (D.map k.hom) (U j).hom ≫ (U j).hom ∧
      ((tailSourceCone D c i (U j)).π.app k).left ≫ g = q j := by
  classical
  let := Fintype.ofFinite J
  have H j := exists_tail_hom D c hc i (U j) (V j) (q j) (hq j)
  choose t g hg hqg using H
  obtain ⟨k, hk⟩ := IsCofiltered.inf_objs_exists (Finset.univ.image t)
  refine ⟨k, fun j ↦ ?_⟩
  let a : k ⟶ t j := (hk (Finset.mem_image.mpr ⟨j, Finset.mem_univ j, rfl⟩)).some
  let b := (tailSourceDiagram D i (U j)).map a
  refine ⟨b.left ≫ g j, ?_, ?_⟩
  · rw [Category.assoc, hg, ← Category.assoc]
    exact congrArg (fun w ↦ w ≫ (U j).hom) (Over.w b)
  · have Hc := congrArg (fun w ↦ w.left ≫ g j) ((tailSourceCone D c i (U j)).w a)
    simpa only [Over.comp_left, Category.assoc, hqg] using Hc

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
include hc in
/-- Simultaneous descent of a finite family of actual morphisms between base-changed endpoints. -/
theorem exists_common_tail_overHom
    (q : ∀ j, (Over.pullback (c.π.app i)).obj (U j) ⟶
      (Over.pullback (c.π.app i)).obj (V j)) :
    ∃ k : Over i, ∀ j, ∃ g : (Over.pullback (D.map k.hom)).obj (U j) ⟶
      (Over.pullback (D.map k.hom)).obj (V j),
      (Over.pullback (c.π.app k.left)).map g ≫
        (overCompIso (D.map k.hom) (c.π.app k.left) (c.π.app i) (c.w k.hom) (V j)).hom =
      (overCompIso (D.map k.hom) (c.π.app k.left) (c.π.app i) (c.w k.hom) (U j)).hom ≫ q j := by
  let z j := (pullbackSymmetry (c.π.app i) (U j).hom).hom ≫
    (q j).left ≫ pullback.fst (V j).hom (c.π.app i)
  have hz j : z j ≫ (V j).hom = pullback.snd (c.π.app i) (U j).hom ≫ (U j).hom := by
    have H : (q j).left ≫ pullback.snd (V j).hom (c.π.app i) =
        pullback.snd (U j).hom (c.π.app i) := Over.w (q j)
    dsimp [z]
    rw [Category.assoc, Category.assoc, pullback.condition, ← Category.assoc (q j).left,
      H, ← Category.assoc, pullbackSymmetry_hom_comp_snd, pullback.condition]
  obtain ⟨k, hk⟩ := exists_common_tail_hom D c hc i U V z hz
  refine ⟨k, fun j ↦ ?_⟩
  obtain ⟨a, ha, hqa⟩ := hk j
  exact tail_overHom_of_hom D c i (U j) (V j) (q j) k a ha hqa
end GeneralLimit
end AlgebraicGeometry.Scheme.FiniteEtale.FieldCoverDescent

/- Migration source: the R5Lab/Aglib mirror; exact module in the migration record.
R5 revision c82abf3a72ce1e1cedf4a4f1fe08bea994ad4df5.
SHA256 9901c3337dbf5f37b1f221aa9e12b311cbda7e0a62f5b102e4044af387780d39.
Definitions, hypotheses and universes are retained modulo native names. -/
