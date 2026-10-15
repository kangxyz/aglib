/-
Copyright (c) 2026 algebraic-geometry contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Mathlib.CategoryTheory.Functor.KanExtension.Adjunction
public import Mathlib.CategoryTheory.Limits.FunctorCategory.EpiMono
public import Mathlib.CategoryTheory.Abelian.Basic

/-!
# Opposite left Kan extension for an image closed under domains

Let a fully faithful functor have essential image closed under taking the
domain of an arrow into that image. Left Kan extension of abelian-valued
presheaves along its opposite preserves monomorphisms. On the image this is
the native invertible Kan unit. Outside the image the defining pointwise
comma category is empty, so the extension is zero.

The inclusion of opens contained in a fixed open is the intended consumer;
this result itself has no topology or sheaf hypothesis.
-/

@[expose] public section

noncomputable section

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false

open CategoryTheory CategoryTheory.Limits Opposite

namespace CategoryTheory.Functor

universe u v

variable {C D : Type u} [SmallCategory C] [SmallCategory D]
  {A : Type v} [Category.{u} A] [Abelian A] [HasColimitsOfSize.{u, u} A]
  (L : C ⥤ D) [L.Full] [L.Faithful]
  (hclosed : ∀ {d : D} {c : C}, (d ⟶ L.obj c) → ∃ c', Nonempty (L.obj c' ≅ d))

include hclosed in
/-- Opposite Kan extension along a fully faithful functor whose essential image is closed
under domains preserves the original presheaf monomorphisms. -/
theorem lan_op_map_mono_of_closed_under_domains {F G : Cᵒᵖ ⥤ A} (α : F ⟶ G) [Mono α] :
    Mono (L.op.lan.map α) := by
  let g := L.op.lan.map α
  have hm (c : C) : Mono (g.app (op (L.obj c))) := by
    have hw := NatTrans.congr_app (L.op.lanUnit.naturality α) (op c)
    change α.app (op c) ≫ (L.op.lanUnit.app G).app (op c) =
      (L.op.lanUnit.app F).app (op c) ≫ g.app (op (L.obj c)) at hw
    have hg : g.app (op (L.obj c)) =
        CategoryTheory.inv ((L.op.lanUnit.app F).app (op c)) ≫ α.app (op c) ≫
          (L.op.lanUnit.app G).app (op c) := by
      apply (cancel_epi ((L.op.lanUnit.app F).app (op c))).mp
      simpa only [Category.assoc, IsIso.hom_inv_id_assoc] using hw.symm
    rw [hg]
    infer_instance
  have hmono (d : Dᵒᵖ) : Mono (g.app d) := by
    by_cases hd : ∃ c, Nonempty (L.obj c ≅ d.unop)
    · obtain ⟨c, ⟨e⟩⟩ := hd
      let : Mono (g.app (op (L.obj c))) := hm c
      have hg : g.app d =
          (L.op.lan.obj F).map e.op.hom ≫ g.app (op (L.obj c)) ≫
            (L.op.lan.obj G).map e.op.inv := by
        apply (cancel_epi ((L.op.lan.obj F).map e.op.inv)).mp
        simpa only [← Category.assoc, ← Functor.map_comp, Iso.inv_hom_id,
          Functor.map_id, Category.id_comp] using g.naturality e.op.inv
      rw [hg]
      infer_instance
    · have hz : IsZero ((L.op.lan.obj F).obj d) := by
        apply (IsZero.iff_id_eq_zero _).mpr
        apply (L.op.isPointwiseLeftKanExtensionLeftKanExtensionUnit F d).hom_ext
        intro j
        exact (hd (hclosed j.hom.unop)).elim
      exact hz.mono _
  exact NatTrans.mono_of_mono_app g

end CategoryTheory.Functor
