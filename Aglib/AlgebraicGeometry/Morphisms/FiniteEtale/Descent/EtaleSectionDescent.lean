/-
Copyright (c) 2026 kangxyz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/

module

public import Aglib.AlgebraicGeometry.Morphisms.FiniteEtale.Descent.FiniteRepresentedRestriction
public import Mathlib.CategoryTheory.Sites.IsSheafFor

/-! Actual section gluing on small etale covers and the represented-section
Yoneda equivalence, with the specified universe lift. -/

@[expose] public section

noncomputable section
set_option autoImplicit false
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open CategoryTheory CategoryTheory.Category CategoryTheory.Limits AlgebraicGeometry Opposite
open _root_.AlgebraicGeometry.Scheme.FiniteEtale (toEtale)

namespace AlgebraicGeometry.Scheme.FiniteEtale.SheafDescent

universe u v
variable {X : Scheme.{u}}

lemma etaleFamily_covering {I : Type v} {V : X.Etale} (U : I → X.Etale)
    (f : ∀ i, U i ⟶ V)
    (h : ∀ x : V.left, ∃ i, ∃ y : (U i).left, (f i).left y = x) :
    Sieve.ofArrows U f ∈ Scheme.smallEtaleTopology X V := by
  change Sieve.ofArrows U f ∈ X.smallGrothendieckTopology @Etale V
  rw [Scheme.smallGrothendieckTopology_eq_toGrothendieck_smallPretopology _ le_rfl,
    Scheme.mem_toGrothendieck_smallPretopology]
  intro x
  obtain ⟨i, y, hy⟩ := h x
  exact ⟨U i, f i, y, Sieve.ofArrows_mk _ _ i, inferInstance, hy⟩

theorem etaleSheaf_existsUnique_glue (F : Scheme.EtaleH1.SetSheaf X) {I : Type v} {V : X.Etale}
    (U : I → X.Etale) (f : ∀ i, U i ⟶ V)
    (h : ∀ x : V.left, ∃ i, ∃ y : (U i).left, (f i).left y = x)
    (s : ∀ i, F.obj.obj (op (U i)))
    (hs : ∀ i j (W : X.Etale) (a : W ⟶ U i) (b : W ⟶ U j),
      a ≫ f i = b ≫ f j → F.obj.map a.op (s i) = F.obj.map b.op (s j)) :
    ∃! t, ∀ i, F.obj.map (f i).op t = s i := by
  have hF := (isSheaf_iff_isSheaf_of_type _ _).1 F.property
  have hf := hF.isSheafFor _ (etaleFamily_covering U f h)
  exact (Presieve.isSheafFor_arrows_iff (P := F.obj) f).1 hf s hs

theorem etaleSheaf_existsUnique_descend (F : Scheme.EtaleH1.SetSheaf X) {U V : X.Etale}
    (f : U ⟶ V) [Surjective f.left] (s : F.obj.obj (op U))
    (hs : ∀ (W : X.Etale) (a b : W ⟶ U), a ≫ f = b ≫ f →
      F.obj.map a.op s = F.obj.map b.op s) :
    ∃! t, F.obj.map f.op t = s := by
  have h := etaleSheaf_existsUnique_glue F (fun _ : Unit => U) (fun _ => f)
    (fun x => by obtain ⟨y, hy⟩ := f.left.surjective x; exact ⟨(), y, hy⟩)
    (fun _ => s) (fun _ _ W a b hab => hs W a b hab)
  simpa only [forall_const] using h

variable {F : Scheme.EtaleH1.SetSheaf X} (Y : Scheme.FiniteEtale X)

/-- The morphism in the small étale site associated to a section of the finite étale cover `Y`. -/
def finiteSectionSiteMap {U : X.Etale} (s : (Scheme.Etale.forget X).obj U ⟶ Y.obj) :
    U ⟶ (toEtale X).obj Y :=
  MorphismProperty.Over.homMk s.left (Over.w s) (by trivial)

@[simp] lemma finiteSectionSiteMap_id :
    finiteSectionSiteMap Y (U := (toEtale X).obj Y) (𝟙 Y.obj) = 𝟙 ((toEtale X).obj Y) := by
  apply MorphismProperty.Over.Hom.ext
  rfl

/-- A section on the actual representing cover gives a morphism of sheaves. -/
def finiteRepresentedSectionMap (s : F.obj.obj (op ((toEtale X).obj Y))) :
    Scheme.EtaleH1.finiteRepresentedSetSheaf Y ⟶ F where
  hom := {
    app U := ↾fun q => F.obj.map (finiteSectionSiteMap Y q.down).op s
    naturality {U V} g := by
      ext q
      change F.obj.map _ s = F.obj.map _ (F.obj.map _ s)
      rw [← Functor.map_comp_apply]
      apply congrArg (fun k => F.obj.map k s)
      apply congrArg Quiver.Hom.op
      apply MorphismProperty.Over.Hom.ext
      rfl }

@[simp] lemma finiteRepresentedSectionMap_identity
    (s : F.obj.obj (op ((toEtale X).obj Y))) :
    (finiteRepresentedSectionMap Y s).hom.app (op ((toEtale X).obj Y))
      (ULift.up (𝟙 Y.obj)) = s := by
  change F.obj.map (finiteSectionSiteMap Y (U := (toEtale X).obj Y) (𝟙 Y.obj)).op s = s
  simp

lemma finiteRepresentedSectionMap_section (q : Scheme.EtaleH1.finiteRepresentedSetSheaf Y ⟶ F) :
    finiteRepresentedSectionMap Y
      (q.hom.app (op ((toEtale X).obj Y)) (ULift.up (𝟙 Y.obj))) = q := by
  ext U s
  have h := congrArg (fun k => k (ULift.up (𝟙 Y.obj)))
    (q.hom.naturality (finiteSectionSiteMap Y s.down).op)
  change q.hom.app U (ULift.up (s.down ≫ 𝟙 Y.obj)) =
    F.obj.map (finiteSectionSiteMap Y s.down).op
      (q.hom.app (op ((toEtale X).obj Y)) (ULift.up (𝟙 Y.obj))) at h
  cases s
  simpa [finiteRepresentedSectionMap] using h.symm

/-- The equivalence evaluating a morphism from the represented section sheaf at the identity
section. -/
def finiteRepresentedSectionEquiv :
    (Scheme.EtaleH1.finiteRepresentedSetSheaf Y ⟶ F) ≃ F.obj.obj (op ((toEtale X).obj Y)) where
  toFun q := q.hom.app (op ((toEtale X).obj Y)) (ULift.up (𝟙 Y.obj))
  invFun := finiteRepresentedSectionMap Y
  left_inv := finiteRepresentedSectionMap_section Y
  right_inv := finiteRepresentedSectionMap_identity Y

end AlgebraicGeometry.Scheme.FiniteEtale.SheafDescent

/- Migration source: the R5Lab/Aglib mirror; exact module in the migration record.
R5 revision c82abf3a72ce1e1cedf4a4f1fe08bea994ad4df5.
SHA256 2da9eaa395acfb7f9a5da8fbe2237406ef8a744ec2ef64aa7f4b9c30984e57f4.
Definitions, hypotheses and universes are retained modulo native names. -/
