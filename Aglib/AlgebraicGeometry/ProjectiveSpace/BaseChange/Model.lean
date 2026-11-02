/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.ProjectiveSpace.BaseChange.Cartesian
public import Aglib.AlgebraicGeometry.ProjectiveSpace.Smooth
public import Aglib.AlgebraicGeometry.Descent.FinitePresentation.ModelBaseFactor

/-! # The original projective space as a finite-presentation model

The stage source is the original polynomial projective space. Its comparison
is the original coefficient map; rebasing uses the existing cartesian
projective-space isomorphism, not a second projective model.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite

namespace AlgebraicGeometry.ProjectiveSpace

universe u

open Scheme.FinitePresentationDescent

variable {A B L : Type u} [CommRing A] [CommRing B] [CommRing L]

/-- The actual standard projective space is a finitely presented model along
any coefficient-ring map, with its original cartesian comparison. -/
def model (φ : A →+* L) (ι : Type u) [Finite ι] [Nonempty ι] :
    Model (Spec.map (CommRingCat.ofHom φ)) (toSpec L ι) := by
  classical
  let : Fintype ι := Fintype.ofFinite ι
  let n := Fintype.card ι - 1
  have hpos : 0 < Fintype.card ι := Fintype.card_pos
  let e : ι ≃ Fin (n + 1) := Fintype.equivFinOfCardEq (by omega)
  let : SmoothOfRelativeDimension n (toSpec A ι) :=
    toSpec_smoothOfRelativeDimension A ι n e
  let : Smooth (toSpec A ι) := SmoothOfRelativeDimension.smooth n (toSpec A ι)
  exact {
    X := ProjectiveSpace A ι
    f := toSpec A ι
    locallyOfFinitePresentation := inferInstance
    quasiCompact := inferInstance
    quasiSeparated := inferInstance
    p := map φ ι
    square := isPullback_map φ ι }

/-- The original coefficient factorization gives the original spectrum triangle. -/
theorem spec_factor (φ : A →+* L) (ψ : A →+* B) (χ : B →+* L)
    (h : χ.comp ψ = φ) :
    Spec.map (CommRingCat.ofHom χ) ≫ Spec.map (CommRingCat.ofHom ψ) =
      Spec.map (CommRingCat.ofHom φ) := by
  rw [← Spec.map_comp]
  change Spec.map (CommRingCat.ofHom (χ.comp ψ)) = _
  rw [h]

/-- The literal factored model is canonically the original projective space
over the intermediate ring. -/
def factorBaseModelIso (φ : A →+* L) (ψ : A →+* B) (χ : B →+* L)
    (h : χ.comp ψ = φ) (ι : Type u) [Finite ι] [Nonempty ι] :
    ((model φ ι).factorBase (Spec.map (CommRingCat.ofHom χ))
      (Spec.map (CommRingCat.ofHom ψ)) (spec_factor φ ψ χ h)).X ≅
        ProjectiveSpace B ι :=
  (baseChangeIso ψ ι).symm

@[reassoc (attr := simp)]
theorem factorBaseModelIso_hom_toSpec
    (φ : A →+* L) (ψ : A →+* B) (χ : B →+* L)
    (h : χ.comp ψ = φ) (ι : Type u) [Finite ι] [Nonempty ι] :
    (factorBaseModelIso φ ψ χ h ι).hom ≫ toSpec B ι =
      ((model φ ι).factorBase (Spec.map (CommRingCat.ofHom χ))
        (Spec.map (CommRingCat.ofHom ψ)) (spec_factor φ ψ χ h)).f := by
  exact (Iso.inv_comp_eq (baseChangeIso ψ ι)).mpr (baseChangeIso_hom_snd ψ ι).symm

/-- In an actual ring diagram, the native `Model.rebase` is the original
projective space at that stage, via the same base-change isomorphism. -/
def rebaseModelIso {I : Type u} [Category.{u} I]
    (F : I ⥤ CommRingCat.{u}) (c : Cocone F) (i : I)
    (j : Over (op i)) (ι : Type u) [Finite ι] [Nonempty ι] :
    ((model (c.ι.app i).hom ι).rebase (F.op ⋙ Scheme.Spec)
      (Scheme.Spec.mapCone c.op) (op i) j).X ≅
        ProjectiveSpace (F.obj j.left.unop) ι :=
  (baseChangeIso (F.map j.hom.unop).hom ι).symm

@[reassoc (attr := simp)]
theorem rebaseModelIso_hom_toSpec {I : Type u} [Category.{u} I]
    (F : I ⥤ CommRingCat.{u}) (c : Cocone F) (i : I)
    (j : Over (op i)) (ι : Type u) [Finite ι] [Nonempty ι] :
    (rebaseModelIso F c i j ι).hom ≫ toSpec (F.obj j.left.unop) ι =
      ((model (c.ι.app i).hom ι).rebase (F.op ⋙ Scheme.Spec)
        (Scheme.Spec.mapCone c.op) (op i) j).f := by
  exact (Iso.inv_comp_eq (baseChangeIso (F.map j.hom.unop).hom ι)).mpr
    (baseChangeIso_hom_snd (F.map j.hom.unop).hom ι).symm

end AlgebraicGeometry.ProjectiveSpace
