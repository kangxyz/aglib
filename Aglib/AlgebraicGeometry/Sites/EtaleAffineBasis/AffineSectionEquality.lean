/-
Copyright (c) 2026 kangxyz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.Sites.EtaleAffineBasis.AffineRepresentativeEquality
public import Aglib.AlgebraicGeometry.Sites.EtaleAffineBasis.RepresentativeEqualityWitnesses

/-! # Eventual equality of original represented sections on affine limits -/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite

namespace AlgebraicGeometry.Scheme.EtaleAffineBasis

universe u

open EtaleCohomology EtaleCohomology.Continuity
attribute [local instance] hasSheafifyLarge

/-- Equality of original represented sections on the affine limit holds at an
actual finite stage. All finite witness covers are produced by the proof. -/
theorem exists_affine_representatives_eventually_equal
    {I : Type u} [Category.{u} I] [IsFiltered I]
    (R : I ⥤ CommRingCat.{u}) (c : Cocone R) (hc : IsColimit c)
    (i : I) {X : Scheme.{u}} (r : Spec (R.obj i) ⟶ X)
    (F : AbelianSheaf.{u, u + 1} X) (U V : X.Etale)
    (a : Spec (R.obj i) ⟶ U.left) (b : Spec (R.obj i) ⟶ V.left)
    (ha : a ≫ U.hom = r) (hb : b ≫ V.hom = r)
    (s : F.obj.obj (op U)) (t : F.obj.obj (op V))
    (h : etaleRepresentativeSection F (Over.mk (Spec.map (c.ι.app i) ≫ r)) U
          (Over.homMk (Spec.map (c.ι.app i) ≫ a) ((Category.assoc _ _ _).trans
            (congrArg (fun z ↦ Spec.map (c.ι.app i) ≫ z) ha))) s =
      etaleRepresentativeSection F (Over.mk (Spec.map (c.ι.app i) ≫ r)) V
          (Over.homMk (Spec.map (c.ι.app i) ≫ b) ((Category.assoc _ _ _).trans
            (congrArg (fun z ↦ Spec.map (c.ι.app i) ≫ z) hb))) t) :
    ∃ (k : I) (α : i ⟶ k),
      etaleRepresentativeSection F (Over.mk (Spec.map (R.map α) ≫ r)) U
          (Over.homMk (Spec.map (R.map α) ≫ a) ((Category.assoc _ _ _).trans
            (congrArg (fun z ↦ Spec.map (R.map α) ≫ z) ha))) s =
        etaleRepresentativeSection F (Over.mk (Spec.map (R.map α) ≫ r)) V
          (Over.homMk (Spec.map (R.map α) ≫ b) ((Category.assoc _ _ _).trans
            (congrArg (fun z ↦ Spec.map (R.map α) ≫ z) hb))) t := by
  obtain ⟨J, hJ, Y, hY, he, hcover, T, p, q, w, hw, hp, hq, hst⟩ :=
    exists_finite_affine_representative_equality_witnesses
      (Spec.map (c.ι.app i) ≫ r) F U V (Spec.map (c.ι.app i) ≫ a)
      (Spec.map (c.ι.app i) ≫ b)
      ((Category.assoc _ _ _).trans (congrArg (fun z ↦ Spec.map (c.ι.app i) ≫ z) ha))
      ((Category.assoc _ _ _).trans (congrArg (fun z ↦ Spec.map (c.ι.app i) ≫ z) hb)) s t h
  have : Finite J := hJ
  have (j : J) : IsAffine (Y j).left := hY j
  have (j : J) : Etale (Y j).hom := he j
  exact exists_affine_stage_representative_eq R c hc i r F Y hcover U V a b ha hb s t
    T p q w hw hp hq hst

end AlgebraicGeometry.Scheme.EtaleAffineBasis
