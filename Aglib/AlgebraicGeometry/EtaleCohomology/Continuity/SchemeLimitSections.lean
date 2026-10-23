/-
Copyright (c) 2026 kangxyz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Mathlib.AlgebraicGeometry.AffineTransitionLimit
public import Mathlib.CategoryTheory.Limits.Types.Filtered

/-!
# Represented sections on affine-transition scheme limits

For a locally finitely presented scheme over the fixed base, the original
relative Hom sets on a qcqs inverse system have the original relative Hom set
on its limit as their filtered colimit. The cocone maps are composition with
the given cone projections. This is the finite-presentation local generator
input for scheme-limit continuity, not yet arbitrary inverse-image sheaf
continuity.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite

namespace AlgebraicGeometry.Scheme.EtaleCohomology.Continuity

universe u

variable {I : Type u} [Category.{u} I] {S : Scheme.{u}}

/-- The diagram of actual relative sections of a represented object. -/
def representedSectionsDiagram (D : I ⥤ Over S) (Y : Over S) : Iᵒᵖ ⥤ Type u :=
  D.op ⋙ yoneda.obj Y

/-- The original projection-composition cocone, with no replacement of its point. -/
def representedSectionsCocone (D : I ⥤ Over S) (c : Cone D) (Y : Over S) :
    Cocone (representedSectionsDiagram D Y) :=
  (yoneda.obj Y).mapCocone c.op

/-- Each original projection sends a stage section to its composite at the limit. -/
@[simp]
lemma representedSectionsCocone_ι_apply (D : I ⥤ Over S) (c : Cone D) (Y : Over S)
    (i : I) (a : D.obj i ⟶ Y) :
    (TypeCat.Hom.hom
      (X := (representedSectionsDiagram D Y).obj (op i))
      (Y := (representedSectionsCocone D c Y).pt)
      ((representedSectionsCocone D c Y).ι.app (op i))) a = c.π.app i ≫ a := rfl

/-- Finite-presentation descent and eventual equality prove the actual relative
section cocone universal. The supplied limit is the underlying scheme limit. -/
def representedSectionsCoconeIsColimit [IsCofiltered I]
    (D : I ⥤ Over S) (c : Cone D)
    (hc : IsLimit ((Over.forget S).mapCone c)) (Y : Over S)
    [LocallyOfFinitePresentation Y.hom]
    [∀ i, CompactSpace (D.obj i).left]
    [∀ i, QuasiSeparatedSpace (D.obj i).left]
    [∀ {i j} (f : i ⟶ j), IsAffineHom (D.map f).left] :
    IsColimit (representedSectionsCocone D c Y) := by
  let D₀ := D ⋙ Over.forget S
  have (i : I) : CompactSpace (D₀.obj i) :=
    inferInstanceAs (CompactSpace (D.obj i).left)
  have (i : I) : QuasiSeparatedSpace (D₀.obj i) :=
    inferInstanceAs (QuasiSeparatedSpace (D.obj i).left)
  have {i j : I} (f : i ⟶ j) : IsAffineHom (D₀.map f) :=
    inferInstanceAs (IsAffineHom (D.map f).left)
  let t : D₀ ⟶ (Functor.const I).obj S :=
    { app i := (D.obj i).hom
      naturality {i j} f := by
        change (D.map f).left ≫ (D.obj j).hom = (D.obj i).hom ≫ 𝟙 S
        rw [Category.comp_id]
        exact Over.w (D.map f) }
  let c₀ := (Over.forget S).mapCone c
  refine Types.FilteredColimit.isColimitOf _ _ ?_ ?_
  · intro a
    obtain ⟨i, g, hg, hgS⟩ :=
      Scheme.exists_π_app_comp_eq_of_locallyOfFinitePresentation D₀ t Y.hom c₀ hc
        a.left (by
          ext i
          exact (Over.w (c.π.app i)).trans (Over.w a).symm)
    refine ⟨op i, Over.homMk g hgS, ?_⟩
    apply Over.OverMorphism.ext
    exact hg.symm
  · intro i j a b hab
    have hab' : (c.π.app i.unop).left ≫ a.left =
        (c.π.app j.unop).left ≫ b.left := congrArg (fun k ↦ k.left) hab
    obtain ⟨k, hik, hjk, heq⟩ :=
      Scheme.exists_hom_hom_comp_eq_comp_of_locallyOfFiniteType D₀ t Y.hom c₀ hc
        a.left (Over.w a).symm b.left (Over.w b).symm hab'
    refine ⟨op k, hik.op, hjk.op, ?_⟩
    apply Over.OverMorphism.ext
    exact heq

/-- The canonical colimit comparison for represented sections is an isomorphism. -/
def representedSectionsColimitIso [IsCofiltered I]
    (D : I ⥤ Over S) (c : Cone D)
    (hc : IsLimit ((Over.forget S).mapCone c)) (Y : Over S)
    [LocallyOfFinitePresentation Y.hom]
    [∀ i, CompactSpace (D.obj i).left]
    [∀ i, QuasiSeparatedSpace (D.obj i).left]
    [∀ {i j} (f : i ⟶ j), IsAffineHom (D.map f).left] :
    colimit (representedSectionsDiagram D Y) ≅ (c.pt ⟶ Y) :=
  colimit.isoColimitCocone
    ⟨representedSectionsCocone D c Y, representedSectionsCoconeIsColimit D c hc Y⟩

/-- The isomorphism retains the original projection-composition map on every stage. -/
@[simp]
lemma representedSectionsColimitIso_ι [IsCofiltered I]
    (D : I ⥤ Over S) (c : Cone D)
    (hc : IsLimit ((Over.forget S).mapCone c)) (Y : Over S)
    [LocallyOfFinitePresentation Y.hom]
    [∀ i, CompactSpace (D.obj i).left]
    [∀ i, QuasiSeparatedSpace (D.obj i).left]
    [∀ {i j} (f : i ⟶ j), IsAffineHom (D.map f).left]
    (i : I) (a : D.obj i ⟶ Y) :
    (representedSectionsColimitIso D c hc Y).hom
      (colimit.ι (representedSectionsDiagram D Y) (op i) a) = c.π.app i ≫ a := by
  exact congrArg (fun k ↦ k a) (colimit.isoColimitCocone_ι_hom
      ⟨representedSectionsCocone D c Y, representedSectionsCoconeIsColimit D c hc Y⟩
      (op i))

end AlgebraicGeometry.Scheme.EtaleCohomology.Continuity
