/-
Copyright (c) 2026 kangxyz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.Descent.FinitePresentation.ClosedImmersion

/-!
# Eventual closedness over a varying base

A quasi-compact immersion between schemes over one base stage becomes closed
after a later base transition if it is closed over the limiting base. The
statement uses the original inverse image of its range, so it applies to any
specified cartesian realization of the pulled-back immersion.
-/

@[expose] public section

noncomputable section

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false

open CategoryTheory CategoryTheory.Limits TopologicalSpace

universe u

namespace AlgebraicGeometry.Scheme

variable {I : Type u} [Category.{u} I] [IsCofiltered I]
  (D : I ⥤ Scheme.{u}) (c : Cone D) (hc : IsLimit c)
  [∀ {i j} (q : i ⟶ j), IsAffineHom (D.map q)]
  [∀ i, CompactSpace (D.obj i)] [∀ i, QuasiSeparatedSpace (D.obj i)]

include hc in
/-- Closedness of the original immersion's range descends along the
canonical base-change system of its target. -/
theorem exists_isClosed_preimage_range_of_isLimit (i : I)
    {X Y : Scheme.{u}} (f : X ⟶ Y) (g : Y ⟶ D.obj i)
    [IsImmersion f] [QuasiCompact f] [QuasiCompact g] [QuasiSeparated g]
    (hclosed : IsClosed (pullback.snd (c.π.app i) g ⁻¹' Set.range f)) :
    ∃ j : Over i, IsClosed (pullback.snd (D.map j.hom) g ⁻¹' Set.range f) := by
  let j₀ : Over i := Over.mk (𝟙 i)
  let e : (baseChangeDiagram D i g).obj j₀ ⟶ Y := pullback.snd (D.map j₀.hom) g
  have : IsIso e := by
    change IsIso (pullback.snd (D.map (𝟙 i)) g)
    rw [D.map_id]
    infer_instance
  let a : X ⟶ (baseChangeDiagram D i g).obj j₀ := f ≫ inv e
  have ha : a ≫ e = f := by simp [a]
  have hrange : Set.range a = e ⁻¹' Set.range f := by
    ext y
    constructor
    · rintro ⟨x, rfl⟩
      exact ⟨x, congrArg (fun k : X ⟶ Y => k x) ha.symm⟩
    · rintro ⟨x, hx⟩
      refine ⟨x, e.isEmbedding.injective ?_⟩
      rw [← Hom.comp_apply, ha]
      exact hx
  have H {T : Scheme.{u}} (t : T ⟶ (baseChangeDiagram D i g).obj j₀) :
      Set.range (pullback.fst t a) = (t ≫ e) ⁻¹' Set.range f := by
    rw [Pullback.range_fst, hrange]
    rfl
  have : IsClosedImmersion
      (pullback.fst ((baseChangeCone D c i g).π.app j₀) a) := by
    apply IsClosedImmersion.of_isPreimmersion
    rw [H]
    rw [show (baseChangeCone D c i g).π.app j₀ ≫ e = pullback.snd (c.π.app i) g from
      baseChangeCone_π_app_snd D c i g j₀]
    change IsClosed (pullback.snd (c.π.app i) g ⁻¹' Set.range f)
    exact hclosed
  obtain ⟨j, hj⟩ := exists_isClosedImmersion_pullback_fst_of_isLimit
    (baseChangeDiagram D i g) (baseChangeCone D c i g)
    (isLimitBaseChangeCone D c hc i g) j₀ a
  let := hj
  have h := (pullback.fst ((baseChangeDiagram D i g).map j.hom) a).isClosedEmbedding.isClosed_range
  rw [H] at h
  rw [show (baseChangeDiagram D i g).map j.hom ≫ e = pullback.snd (D.map j.left.hom) g from
    baseChangeDiagram_map_snd D i g j.hom] at h
  change IsClosed (pullback.snd (D.map j.left.hom) g ⁻¹' Set.range f) at h
  exact ⟨j.left, h⟩

include hc in
/-- The literal base change of an immersion over a stage target is closed
after a later base transition if it is closed over the limiting base. -/
theorem exists_isClosedImmersion_pullback_fst_over_of_isLimit (i : I)
    {X Y : Scheme.{u}} (f : X ⟶ Y) (g : Y ⟶ D.obj i)
    [IsImmersion f] [QuasiCompact f] [QuasiCompact g] [QuasiSeparated g]
    [IsClosedImmersion (pullback.fst (pullback.snd (c.π.app i) g) f)] :
    ∃ j : Over i, IsClosedImmersion (pullback.fst (pullback.snd (D.map j.hom) g) f) := by
  obtain ⟨j, hj⟩ := exists_isClosed_preimage_range_of_isLimit D c hc i f g (by
    rw [← Pullback.range_fst]
    exact (pullback.fst (pullback.snd (c.π.app i) g) f).isClosedEmbedding.isClosed_range)
  refine ⟨j, IsClosedImmersion.of_isPreimmersion _ ?_⟩
  rwa [Pullback.range_fst]

end AlgebraicGeometry.Scheme
