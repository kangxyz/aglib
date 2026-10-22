/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.Approximation.FinitePresentationEnvelope.SubalgebraOpenDiagram
public import Aglib.AlgebraicGeometry.Approximation.FinitePresentationEnvelope.BinarySystem

/-!
# Arithmetic systems from finite-subalgebra overlap gluing

A cofiltered diagram of actual open overlaps is glued to the spectra of
eligible finite integer subalgebras. The original second chart is reindexed
along the native final finite-subalgebra projection. Its limit is unchanged.
The affine chart limit and every affine-overlap square come from the actual
ring cocone and prescribed principal images.

This is the categorical assembly step of Stacks Project, Tag 07RN. All input
maps and principal-image certificates are explicit; constructing the original
overlap and its ring diagram remains the geometric supplier's responsibility.
-/

@[expose] public noncomputable section

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open CategoryTheory CategoryTheory.Limits Opposite

universe u

namespace AlgebraicGeometry.Scheme.FinitePresentationEnvelope.SubalgebraGluing

variable {I : Type u} [Category.{u} I]

/-- Remove the double opposite when reindexing the original geometric stages. -/
def reindex (F : Iᵒᵖ ⥤ CommRingCat.{u}) {L : Type u} (h : ∀ i, L → F.obj i) :
    (SubalgebraOpenDiagram.Index F h)ᵒᵖ ⥤ I :=
  (CommRingCat.FilteredSubalgebra.forget F (SubalgebraOpenDiagram.Eligible F h)).op ⋙
    unopUnop I

/-- The original spectrum map transported only through the native double
opposite equivalence, with unchanged components. -/
def doubleOppositeMap (F : Iᵒᵖ ⥤ CommRingCat.{u}) (W : I ⥤ Scheme.{u})
    (e : W ⟶ F.rightOp ⋙ Scheme.Spec) :
    unopUnop I ⋙ W ⟶ F.op ⋙ Scheme.Spec := by
  let a := Functor.whiskerLeft (unopUnop I) e
  exact a

/-- The opposite-index adapter preserves every original component literally. -/
@[simp]
theorem doubleOppositeMap_app (F : Iᵒᵖ ⥤ CommRingCat.{u}) (W : I ⥤ Scheme.{u})
    (e : W ⟶ F.rightOp ⋙ Scheme.Spec) (i : Iᵒᵖᵒᵖ) :
    (doubleOppositeMap F W e).app i = e.app i.unop.unop := rfl

/-- Glue the reindexed original second chart to the eligible finite-subalgebra
spectra. The limiting scheme is the literal original open pushout. Neither an
overlap limit certificate nor an affine-side cartesian-square oracle is needed. -/
def system [IsCofiltered I]
    (F : Iᵒᵖ ⥤ CommRingCat.{u}) (W V : I ⥤ Scheme.{u})
    (e : W ⟶ F.rightOp ⋙ Scheme.Spec) (α : W ⟶ V)
    [∀ i, IsOpenImmersion (e.app i)] [∀ i, IsOpenImmersion (α.app i)]
    [∀ i, LocallyOfFiniteType (specULiftZIsTerminal.from (W.obj i))]
    [∀ i, LocallyOfFiniteType (specULiftZIsTerminal.from (V.obj i))]
    [∀ i, CompactSpace (V.obj i)]
    [∀ {i j} (r : i ⟶ j), IsAffineHom (V.map r)]
    (hα : α.Equifibered) {L : Type u} [Finite L]
    (h : ∀ i, L → F.obj i)
    (hh : ∀ {i j} (r : i ⟶ j) l, (F.map r).hom (h i l) = h j l)
    (he : ∀ i, (e.app i).opensRange = ⨆ l, PrimeSpectrum.basicOpen (h (op i) l))
    (c : Cocone F) (hc : IsColimit c) (cW : Cone W) (cV : Cone V) (hcV : IsLimit cV)
    (j₀ : cW.pt ⟶ Spec c.pt) (g₀ : cW.pt ⟶ cV.pt)
    [IsOpenImmersion j₀] [IsOpenImmersion g₀]
    (Hj : ∀ i, cW.π.app i ≫ e.app i = j₀ ≫ Spec.map (c.ι.app (op i)))
    (hj₀ : ∀ i, j₀.opensRange = ⨆ l,
      PrimeSpectrum.basicOpen ((c.ι.app (op i)).hom (h (op i) l)))
    (Hg : ∀ i, IsPullback (cW.π.app i) g₀ (α.app i) (cV.π.app i)) :
    System (pushout j₀ g₀) := by
  let W' : Iᵒᵖᵒᵖ ⥤ Scheme.{u} := unopUnop I ⋙ W
  let e' : W' ⟶ F.op ⋙ Scheme.Spec := doubleOppositeMap F W e
  let (i : Iᵒᵖᵒᵖ) : IsOpenImmersion (e'.app i) :=
    inferInstanceAs (IsOpenImmersion (e.app i.unop.unop))
  let (i : Iᵒᵖᵒᵖ) :
      LocallyOfFiniteType (specULiftZIsTerminal.from (W'.obj i)) :=
    inferInstanceAs (LocallyOfFiniteType (specULiftZIsTerminal.from (W.obj i.unop.unop)))
  have he' (i : Iᵒᵖ) : (e'.app (op i)).opensRange =
      ⨆ l, PrimeSpectrum.basicOpen (h i l) := he i.unop
  let : IsFiltered (SubalgebraOpenDiagram.Index F h) :=
    SubalgebraOpenDiagram.index_isFiltered F h W' e' he'
  let : (CommRingCat.FilteredSubalgebra.forget F
      (SubalgebraOpenDiagram.Eligible F h)).Final :=
    SubalgebraOpenDiagram.forget_final F h W' e' he'
  let K := reindex F h
  let : K.Initial := inferInstanceAs
    ((CommRingCat.FilteredSubalgebra.forget F
      (SubalgebraOpenDiagram.Eligible F h)).op ⋙ unopUnop I).Initial
  let f : K ⋙ W ⟶ SubalgebraOpenDiagram.affine F h := by
    let a := SubalgebraOpenDiagram.toAffine F h W' e'
    exact a
  let g : K ⋙ W ⟶ K ⋙ V := Functor.whiskerLeft K α
  let (i : (SubalgebraOpenDiagram.Index F h)ᵒᵖ) : IsOpenImmersion (f.app i) :=
    SubalgebraOpenDiagram.toAffine_isOpenImmersion F h W' e' he' i
  let (i : (SubalgebraOpenDiagram.Index F h)ᵒᵖ) : IsOpenImmersion (g.app i) :=
    inferInstanceAs (IsOpenImmersion (α.app (K.obj i)))
  let {i j : (SubalgebraOpenDiagram.Index F h)ᵒᵖ} (r : i ⟶ j) :
      IsAffineHom ((SubalgebraOpenDiagram.affine F h).map r) := by
    change IsAffineHom (Spec.map _)
    infer_instance
  let {i j : (SubalgebraOpenDiagram.Index F h)ᵒᵖ} (r : i ⟶ j) :
      IsAffineHom ((K ⋙ V).map r) :=
    inferInstanceAs (IsAffineHom (V.map (K.map r)))
  let (i : (SubalgebraOpenDiagram.Index F h)ᵒᵖ) : CompactSpace ((K ⋙ V).obj i) :=
    inferInstanceAs (CompactSpace (V.obj (K.obj i)))
  let (i : (SubalgebraOpenDiagram.Index F h)ᵒᵖ) :
      LocallyOfFiniteType (specULiftZIsTerminal.from ((K ⋙ V).obj i)) :=
    inferInstanceAs (LocallyOfFiniteType (specULiftZIsTerminal.from (V.obj (K.obj i))))
  have hf : f.Equifibered := SubalgebraOpenDiagram.toAffine_equifibered F h W' e' he' hh
  have hg : g.Equifibered := hα.whiskerLeft K
  let cW' : Cone (K ⋙ W) := cW.whisker K
  let cV' : Cone (K ⋙ V) := cV.whisker K
  let cA := SubalgebraOpenDiagram.affineCone F h c
  have Hf (i : (SubalgebraOpenDiagram.Index F h)ᵒᵖ) :
      IsPullback (cW'.π.app i) j₀ (f.app i) (cA.π.app i) :=
    SubalgebraOpenDiagram.toAffine_cone_isPullback F h W' e' he' c i j₀
      (cW.π.app (K.obj i)) (Hj (K.obj i)) (hj₀ (K.obj i))
  have Hg' (i : (SubalgebraOpenDiagram.Index F h)ᵒᵖ) :
      IsPullback (cW'.π.app i) g₀ (g.app i) (cV'.π.app i) := Hg (K.obj i)
  exact BinaryGluing.system f g hf hg cW' cA cV' j₀ g₀
    (fun i ↦ (Hf i).w.symm) (fun i ↦ (Hg' i).w.symm) Hf Hg'
    (SubalgebraOpenDiagram.affineConeIsLimit F h W' e' he' c hc)
    ((Functor.Initial.isLimitWhiskerEquiv K cV).symm hcV)

end AlgebraicGeometry.Scheme.FinitePresentationEnvelope.SubalgebraGluing
