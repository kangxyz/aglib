/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.Morphisms.FiniteEtale.Descent.FiniteFieldCommonMorphisms
public import Aglib.AlgebraicGeometry.Descent.FinitePresentation.Schemes

/-! # Simultaneous descent of original finite families of automorphisms

The common-tail Hom supplier descends the original arrows, and a second
common stage makes them invertible. Both stage covers are literal successive
base changes. The comparison and map on automorphisms use the native pullback
composition isomorphisms, without a new action or cover model.
-/

@[expose] public noncomputable section

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open CategoryTheory CategoryTheory.Limits
open AlgebraicGeometry.Scheme.FiniteEtale.FieldCoverDescent

namespace AlgebraicGeometry.Scheme.FiniteEtale.LimitDescent

universe u

variable {I : Type u} [Category.{u} I] (D : I ⥤ Scheme.{u}) (c : Cone D)
  (i : I) (Yi : FiniteEtale (D.obj i))

/-- The actual two-stage cover, with no replacement or flattened model. -/
abbrev iteratedCover (j : Over i) (k : Over j.left) : FiniteEtale (D.obj k.left) :=
  (baseChange (D.map k.hom)).obj ((baseChange (D.map j.hom)).obj Yi)

/-- The canonical two-step comparison to the original limit pullback. -/
def iteratedCoverIso (j : Over i) (k : Over j.left) :
    (baseChange (c.π.app k.left)).obj (iteratedCover D i Yi j k) ≅
      (baseChange (c.π.app i)).obj Yi :=
  ObjectProperty.isoMk _
    (overCompIso (D.map k.hom) (c.π.app k.left) (c.π.app j.left) (c.w k.hom)
        ((baseChange (D.map j.hom)).obj Yi).obj ≪≫
      overCompIso (D.map j.hom) (c.π.app j.left) (c.π.app i) (c.w j.hom) Yi.obj)

/-- The original map on automorphisms followed by the original comparison. -/
def iteratedCoverMapAut (Y : FiniteEtale c.pt)
    (e : (baseChange (c.π.app i)).obj Yi ≅ Y) (j : Over i) (k : Over j.left) :
    Aut (iteratedCover D i Yi j k) →* Aut Y :=
  (Aut.autMulEquivOfIso (iteratedCoverIso D c i Yi j k ≪≫ e)).toMonoidHom.comp
    (Functor.mapAut (iteratedCover D i Yi j k) (baseChange (c.π.app k.left)))

variable [IsCofiltered I] (hc : IsLimit c)
  [∀ {i j} (f : i ⟶ j), IsAffineHom (D.map f)]
  [∀ i, CompactSpace (D.obj i)] [∀ i, QuasiSeparatedSpace (D.obj i)]

include hc in
/-- A finite family of original automorphisms lifts at two common actual
stages. No Galoisness or action-law hypothesis is used. -/
theorem exists_iteratedCover_lifts_aut_family
    (Y : FiniteEtale c.pt) (e : (baseChange (c.π.app i)).obj Yi ≅ Y)
    {J : Type u} [Finite J] (τ : J → Aut Y) :
    ∃ (j : Over i) (k : Over j.left), ∀ t, ∃ σ : Aut (iteratedCover D i Yi j k),
      iteratedCoverMapAut D c i Yi Y e j k σ = τ t := by
  classical
  let : CompactSpace Yi.obj.left := QuasiCompact.compactSpace_of_compactSpace Yi.obj.hom
  let : QuasiSeparatedSpace Yi.obj.left := quasiSeparatedSpace_of_quasiSeparated Yi.obj.hom
  let q (t : J) : (Over.pullback (c.π.app i)).obj Yi.obj ⟶
      (Over.pullback (c.π.app i)).obj Yi.obj :=
    e.hom.hom ≫ (τ t).hom.hom ≫ e.inv.hom
  obtain ⟨j, hj⟩ := exists_common_tail_overHom D c hc i
    (fun _ : J => Yi.obj) (fun _ : J => Yi.obj) q
  choose g hg using hj
  let B := (Over.pullback (D.map j.hom)).obj Yi.obj
  let e₁ := overCompIso (D.map j.hom) (c.π.app j.left) (c.π.app i) (c.w j.hom) Yi.obj
  have (t : J) : IsIso ((Over.pullback (c.π.app j.left)).map (g t)) := by
    have h : (Over.pullback (c.π.app j.left)).map (g t) =
        e₁.hom ≫ q t ≫ e₁.inv := by
      apply (cancel_mono e₁.hom).mp
      have ht : (Over.pullback (c.π.app j.left)).map (g t) ≫ e₁.hom =
          e₁.hom ≫ q t := hg t
      rw [ht]
      simp only [Category.assoc, Iso.inv_hom_id, Category.comp_id]
    rw [h]
    infer_instance
  let : Etale B.hom :=
    inferInstanceAs (Etale (pullback.snd Yi.obj.hom (D.map j.hom)))
  let : IsFinite B.hom :=
    inferInstanceAs (IsFinite (pullback.snd Yi.obj.hom (D.map j.hom)))
  let : ∀ _ : J, LocallyOfFinitePresentation B.hom := fun _ => inferInstance
  let : ∀ _ : J, QuasiCompact B.hom := fun _ => inferInstance
  let : ∀ _ : J, QuasiSeparated B.hom := fun _ => inferInstance
  obtain ⟨k, hk⟩ := Scheme.exists_common_stage_isIso_baseChange_maps_of_isLimit
    D c hc j.left (fun _ : J => B.hom) (fun _ : J => B.hom) g
  refine ⟨j, k, fun t => ?_⟩
  let : IsIso ((Over.pullback (D.map k.hom)).map (g t)) := hk t
  let σ : Aut (iteratedCover D i Yi j k) :=
    ObjectProperty.isoMk _ (asIso ((Over.pullback (D.map k.hom)).map (g t)))
  let e₂ := overCompIso (D.map k.hom) (c.π.app k.left) (c.π.app j.left) (c.w k.hom) B
  let E := iteratedCoverIso D c i Yi j k ≪≫ e
  have hσ : (baseChange (c.π.app k.left)).map σ.hom ≫ E.hom = E.hom ≫ (τ t).hom := by
    apply ObjectProperty.hom_ext
    change (Over.pullback (c.π.app k.left)).map
        ((Over.pullback (D.map k.hom)).map (g t)) ≫ e₂.hom ≫ e₁.hom ≫ e.hom.hom =
      e₂.hom ≫ e₁.hom ≫ e.hom.hom ≫ (τ t).hom.hom
    have hn : (Over.pullback (c.π.app k.left)).map
        ((Over.pullback (D.map k.hom)).map (g t)) ≫ e₂.hom =
        e₂.hom ≫ (Over.pullback (c.π.app j.left)).map (g t) :=
      overCompIso_naturality (D.map k.hom) (c.π.app k.left) (c.π.app j.left)
        (c.w k.hom) (g t)
    have ht : (Over.pullback (c.π.app j.left)).map (g t) ≫ e₁.hom =
        e₁.hom ≫ q t := hg t
    rw [← Category.assoc, hn, Category.assoc,
      ← Category.assoc ((Over.pullback (c.π.app j.left)).map (g t)), ht]
    simp only [q, Category.assoc, ObjectProperty.isoInv_hom_id_hom, Category.comp_id]
  refine ⟨σ, ?_⟩
  apply Iso.ext
  change E.inv ≫ (baseChange (c.π.app k.left)).map σ.hom ≫ E.hom = (τ t).hom
  rw [hσ]
  simp

include hc in
/-- Finiteness of the original automorphism group supplies a stage whose
actual map on automorphisms is surjective onto that original group. -/
theorem exists_iteratedCover_mapAut_surjective
    (Y : FiniteEtale c.pt) (e : (baseChange (c.π.app i)).obj Yi ≅ Y)
    [Finite (Aut Y)] :
    ∃ (j : Over i) (k : Over j.left),
      Function.Surjective (iteratedCoverMapAut D c i Yi Y e j k) := by
  obtain ⟨j, k, h⟩ := exists_iteratedCover_lifts_aut_family D c i Yi hc Y e (fun τ => τ)
  exact ⟨j, k, h⟩

end AlgebraicGeometry.Scheme.FiniteEtale.LimitDescent
