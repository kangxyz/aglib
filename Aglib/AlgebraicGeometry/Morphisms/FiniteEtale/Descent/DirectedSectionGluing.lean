/-
Copyright (c) 2026 kangxyz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/

module

public import Aglib.AlgebraicGeometry.Morphisms.FiniteEtale.Descent.EtaleSectionDescent
public import Mathlib.AlgebraicGeometry.Cover.Directed

/-!
# DirectedSectionGluing

General constructions and comparisons for this native mathematical family.
-/

@[expose] public section

noncomputable section
set_option autoImplicit false
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open CategoryTheory CategoryTheory.Category CategoryTheory.Limits AlgebraicGeometry Opposite
namespace AlgebraicGeometry.Scheme.FiniteEtale.SheafDescent
universe u v
variable {X : Scheme.{u}}

lemma etaleSheaf_section_ext (F : Scheme.EtaleCohomology.SetSheaf X) {I : Type v} {V : X.Etale}
    (U : I → X.Etale) (f : ∀ i, U i ⟶ V)
    (h : ∀ x : V.left, ∃ i, ∃ y : (U i).left, (f i).left y = x)
    {s t : F.obj.obj (op V)} (hst : ∀ i, F.obj.map (f i).op s = F.obj.map (f i).op t) :
    s = t := by
  have he : (↾fun _ : PUnit => s) = (↾fun _ : PUnit => t) :=
    F.property.hom_ext_ofArrows f (etaleFamily_covering U f h) (by
      intro i
      ext z
      exact hst i)
  exact congrArg (fun f => f PUnit.unit) he

namespace DirectedSectionGluing
variable {Y : Scheme.{u}} (p : Y ⟶ X) [Etale p] (C : Y.OpenCover)
variable [Category C.I₀] [C.LocallyDirected]

/-- The étale object over `X` obtained by composing the open-chart map with `p` . -/
abbrev site (i : C.I₀) : X.Etale := Scheme.Etale.mk (C.f i ≫ p)

/-- The open-chart inclusion into the étale object defined by `p` . -/
def inclusion (i : C.I₀) : site p C i ⟶ Scheme.Etale.mk p :=
  MorphismProperty.Over.homMk (C.f i) rfl (by trivial)

/-- The morphism between étale chart objects induced by a transition in the locally directed
open cover. -/
def trans {i j : C.I₀} (h : i ⟶ j) : site p C i ⟶ site p C j :=
  MorphismProperty.Over.homMk (C.trans h) (by
    change C.trans h ≫ (C.f j ≫ p) = C.f i ≫ p
    rw [← Category.assoc, C.trans_map]) (by trivial)

variable (F : Scheme.EtaleCohomology.SetSheaf X)

/-- Compatibility on a directed open diagram implies the complete sheaf matching condition. -/
theorem matching (s : ∀ i, F.obj.obj (op (site p C i)))
    (hs : ∀ {i j} (h : i ⟶ j), F.obj.map (trans p C h).op (s j) = s i)
    (i j : C.I₀) (W : X.Etale) (a : W ⟶ site p C i) (b : W ⟶ site p C j)
    (hab : a ≫ inclusion p C i = b ≫ inclusion p C j) :
    F.obj.map a.op (s i) = F.obj.map b.op (s j) := by
  let c : W.left ⟶ Y := a.left ≫ C.f i
  have hc : c ≫ p = W.hom := by
    simpa [c, site, Category.assoc] using MorphismProperty.Over.w a
  have hcb : b.left ≫ C.f j = c := by
    exact (congrArg (fun f => f.left) hab).symm
  let K := Σ k : C.I₀, (k ⟶ i) × (k ⟶ j)
  let T (k : K) : X.Etale :=
    Scheme.Etale.mk (pullback.fst c (C.f k.1) ≫ W.hom)
  let f (k : K) : T k ⟶ W :=
    MorphismProperty.Over.homMk (pullback.fst c (C.f k.1)) rfl (by trivial)
  let g (k : K) : T k ⟶ site p C k.1 :=
    MorphismProperty.Over.homMk (pullback.snd c (C.f k.1)) (by
      change pullback.snd c (C.f k.1) ≫ (C.f k.1 ≫ p) =
        pullback.fst c (C.f k.1) ≫ W.hom
      rw [← Category.assoc, ← pullback.condition, Category.assoc, hc]) (by trivial)
  apply etaleSheaf_section_ext F T f
  · intro w
    have hw : C.f i (a.left w) = C.f j (b.left w) := by
      have hh : a.left ≫ C.f i = b.left ≫ C.f j := congrArg (fun f => f.left) hab
      exact congrArg (fun q => q w) hh
    obtain ⟨k, ki, kj, y, hyi, hyj⟩ := C.exists_of_f_eq_f (a.left w) (b.left w) hw
    have hy : c w = C.f k y := by
      calc
        c w = C.f i (a.left w) := rfl
        _ = C.f i (C.trans ki y) := congrArg (fun z => C.f i z) hyi.symm
        _ = C.f k y := congrArg (fun q : C.X k ⟶ Y => q y) (C.trans_map ki)
    obtain ⟨z, hz, _⟩ := Scheme.Pullback.exists_preimage_pullback (f := c) (g := C.f k) w y hy
    exact ⟨⟨k, ki, kj⟩, z, hz⟩
  · intro k
    have hia : f k ≫ a = g k ≫ trans p C k.2.1 := by
      apply MorphismProperty.Over.Hom.ext
      apply (cancel_mono (C.f i)).1
      change (pullback.fst c (C.f k.1) ≫ a.left) ≫ C.f i =
        (pullback.snd c (C.f k.1) ≫ C.trans k.2.1) ≫ C.f i
      simp only [Category.assoc, C.trans_map]
      exact pullback.condition
    have hjb : f k ≫ b = g k ≫ trans p C k.2.2 := by
      apply MorphismProperty.Over.Hom.ext
      apply (cancel_mono (C.f j)).1
      change (pullback.fst c (C.f k.1) ≫ b.left) ≫ C.f j =
        (pullback.snd c (C.f k.1) ≫ C.trans k.2.2) ≫ C.f j
      simp only [Category.assoc, C.trans_map, hcb]
      exact pullback.condition
    rw [← Functor.map_comp_apply, ← op_comp, hia,
      ← Functor.map_comp_apply, ← op_comp, hjb]
    simp only [op_comp, Functor.map_comp, types_comp_apply, hs]

/-- Actual global sections glue from a compatible locally directed open diagram. -/
theorem existsUnique_glue (s : ∀ i, F.obj.obj (op (site p C i)))
    (hs : ∀ {i j} (h : i ⟶ j), F.obj.map (trans p C h).op (s j) = s i) :
    ∃! t : F.obj.obj (op (Scheme.Etale.mk p)),
      ∀ i, F.obj.map (inclusion p C i).op t = s i := by
  apply etaleSheaf_existsUnique_glue F (site p C) (inclusion p C)
  · intro x
    obtain ⟨i, y, hy⟩ := C.exists_eq x
    exact ⟨i, y, hy⟩
  · exact matching p C F s hs

end DirectedSectionGluing
end AlgebraicGeometry.Scheme.FiniteEtale.SheafDescent

/- Migration source: the R5Lab/Aglib mirror; exact module in the migration record.
R5 revision c82abf3a72ce1e1cedf4a4f1fe08bea994ad4df5.
SHA256 fcf12fd097da32b7d3a9c412470bbf76d524460ce37f0dbbf42ce06ee899679e.
Definitions, hypotheses and universes are retained modulo native names. -/
