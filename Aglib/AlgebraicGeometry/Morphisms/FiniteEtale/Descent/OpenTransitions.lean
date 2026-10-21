/-
Copyright (c) 2026 kangxyz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/

module

public import Aglib.AlgebraicGeometry.Morphisms.FiniteEtale.Descent.ChartSections
public import Mathlib.AlgebraicGeometry.RelativeGluing

/-!
# OpenTransitions

General constructions and comparisons for this native mathematical family.
-/

@[expose] public section

noncomputable section
set_option autoImplicit false
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open CategoryTheory CategoryTheory.Category CategoryTheory.Limits AlgebraicGeometry Opposite
open _root_.AlgebraicGeometry.Scheme.FiniteEtale (toEtale)
namespace AlgebraicGeometry.Scheme.FiniteEtale.SheafDescent.FiniteSetOpenRepresentation
universe u
variable {X : Scheme.{u}} {F : Scheme.EtaleCohomology.SetSheaf X} {U V W : X.Opens}

lemma factor_le (r : FiniteSetOpenRepresentation F U) (h : U ≤ V) :
    (r.cover.obj.hom ≫ X.homOfLE h) ≫ V.ι = r.site.hom := by
  change (r.cover.obj.hom ≫ X.homOfLE h) ≫ V.ι = r.cover.obj.hom ≫ U.ι
  simp

/-- The transition is uniquely specified by the original sheaf's universal sections. -/
def transition (r : FiniteSetOpenRepresentation F U) (s : FiniteSetOpenRepresentation F V)
    (h : U ≤ V) : r.site ⟶ s.site :=
  Classical.choose ((s.section_bijective_of_factor r.site
    (r.cover.obj.hom ≫ X.homOfLE h) (r.factor_le h)).2 r.section_)

@[simp] lemma transition_section (r : FiniteSetOpenRepresentation F U)
    (s : FiniteSetOpenRepresentation F V) (h : U ≤ V) :
    F.obj.map (r.transition s h).op s.section_ = r.section_ :=
  Classical.choose_spec ((s.section_bijective_of_factor r.site
    (r.cover.obj.hom ≫ X.homOfLE h) (r.factor_le h)).2 r.section_)

@[simp] lemma transition_w (r : FiniteSetOpenRepresentation F U)
    (s : FiniteSetOpenRepresentation F V) (h : U ≤ V) :
    (r.transition s h).left ≫ s.cover.obj.hom = r.cover.obj.hom ≫ X.homOfLE h := by
  apply (cancel_mono V.ι).1
  rw [r.factor_le h]
  simpa [site, toEtale] using MorphismProperty.Over.w (r.transition s h)

@[simp] lemma transition_id (r : FiniteSetOpenRepresentation F U) :
    r.transition r le_rfl = 𝟙 r.site := by
  apply (r.section_bijective_of_factor r.site r.cover.obj.hom rfl).1
  simp

@[simp] lemma transition_comp (r : FiniteSetOpenRepresentation F U)
    (s : FiniteSetOpenRepresentation F V) (q : FiniteSetOpenRepresentation F W)
    (h : U ≤ V) (k : V ≤ W) :
    r.transition s h ≫ s.transition q k = r.transition q (h.trans k) := by
  apply (q.section_bijective_of_factor r.site
    (r.cover.obj.hom ≫ X.homOfLE (h.trans k)) (r.factor_le (h.trans k))).1
  simp [op_comp, Functor.map_comp]

/-- The transition square is a pullback, proved from local representability. -/
theorem transition_isPullback (r : FiniteSetOpenRepresentation F U)
    (s : FiniteSetOpenRepresentation F V) (h : U ≤ V) :
    IsPullback (r.transition s h).left r.cover.obj.hom s.cover.obj.hom (X.homOfLE h) := by
  let P := pullback s.cover.obj.hom (X.homOfLE h)
  let ps : P ⟶ U.toScheme := pullback.snd _ _
  let pf : P ⟶ s.cover.obj.left := pullback.fst _ _
  let Z : X.Etale := Scheme.Etale.mk (ps ≫ U.ι)
  let q : Z ⟶ s.site := MorphismProperty.Over.homMk pf (by
    change pf ≫ (s.cover.obj.hom ≫ V.ι) = ps ≫ U.ι
    dsimp [pf, ps]
    rw [← Category.assoc, pullback.condition, Category.assoc, X.homOfLE_ι]) (by trivial)
  obtain ⟨i, hi⟩ := (r.section_bijective_of_factor Z ps rfl).2 (F.obj.map q.op s.section_)
  change F.obj.map i.op r.section_ = F.obj.map q.op s.section_ at hi
  have hiq : i ≫ r.transition s h = q := by
    apply (s.section_bijective_of_factor Z (ps ≫ X.homOfLE h) (by
      change (ps ≫ X.homOfLE h) ≫ V.ι = ps ≫ U.ι
      simp)).1
    simpa [op_comp, Functor.map_comp, ConcreteCategory.comp_apply] using hi
  have hiw : i.left ≫ r.cover.obj.hom = ps := by
    apply (cancel_mono U.ι).1
    simpa [site, toEtale, Z, Category.assoc] using MorphismProperty.Over.w i
  let l : r.site.left ⟶ P := pullback.lift (r.transition s h).left r.cover.obj.hom
    (r.transition_w s h)
  let ls : r.site ⟶ Z := MorphismProperty.Over.homMk l (by
    change l ≫ (ps ≫ U.ι) = r.cover.obj.hom ≫ U.ι
    dsimp [l, ps]
    simp) (by trivial)
  have hlq : ls ≫ q = r.transition s h := by
    apply MorphismProperty.Over.Hom.ext
    exact pullback.lift_fst _ _ _
  have hli : ls ≫ i = 𝟙 r.site := by
    apply (r.section_bijective_of_factor r.site r.cover.obj.hom rfl).1
    simp only [op_comp, Functor.map_comp, types_comp_apply, op_id]
    rw [hi, ← Functor.map_comp_apply, ← op_comp, hlq, r.transition_section s h]
    simp
  let e : r.site.left ≅ P := {
    hom := l
    inv := i.left
    hom_inv_id := congrArg (fun f => f.left) hli
    inv_hom_id := by
      apply pullback.hom_ext
      · have hh : i.left ≫ (r.transition s h).left = pf :=
          congrArg (fun f => f.left) hiq
        simpa [l, pf] using hh
      · simpa [l, ps] using hiw }
  exact IsPullback.of_iso_pullback ⟨r.transition_w s h⟩ e
    (pullback.lift_fst _ _ _) (pullback.lift_snd _ _ _)

end AlgebraicGeometry.Scheme.FiniteEtale.SheafDescent.FiniteSetOpenRepresentation

/- Migration source: the R5Lab/Aglib mirror; exact module in the migration record.
R5 revision c82abf3a72ce1e1cedf4a4f1fe08bea994ad4df5.
SHA256 6e656ce1c0159e68a0b619d3ab4ca0b7f50281a7f554c660f36f3c12740751ad.
Definitions, hypotheses and universes are retained modulo native names. -/
