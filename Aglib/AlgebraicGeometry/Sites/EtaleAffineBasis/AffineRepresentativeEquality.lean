/-
Copyright (c) 2026 kangxyz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.Sites.EtaleAffineBasis.FiniteCoverModelsAbove
public import Aglib.AlgebraicGeometry.Sites.EtaleAffineBasis.StageRepresentativeEquality

/-! # Descending section equality witnessed on a finite affine limit cover -/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite

namespace AlgebraicGeometry.Scheme.EtaleAffineBasis

universe u v

open EtaleCohomology EtaleCohomology.Continuity
attribute [local instance] hasSheafifyLarge

private lemma transport_representative_equality
    {X S : Scheme.{u}} (F : AbelianSheaf.{u, u + 1} X) (U V : X.Etale)
    {f f' : S ⟶ X} {a a' : S ⟶ U.left} {b b' : S ⟶ V.left}
    (ha : a ≫ U.hom = f) (hb : b ≫ V.hom = f)
    (ha' : a' ≫ U.hom = f') (hb' : b' ≫ V.hom = f')
    (s : F.obj.obj (op U)) (t : F.obj.obj (op V))
    (hf : f = f') (hA : a = a') (hB : b = b')
    (h : etaleRepresentativeSection F (Over.mk f) U (Over.homMk a ha) s =
      etaleRepresentativeSection F (Over.mk f) V (Over.homMk b hb) t) :
    etaleRepresentativeSection F (Over.mk f') U (Over.homMk a' ha') s =
      etaleRepresentativeSection F (Over.mk f') V (Over.homMk b' hb') t := by
  cases hf
  cases hA
  cases hB
  exact h

/-- Finite affine witnesses on the limit, not assumed to have stage models,
force equality of the original represented sections at a later stage. -/
theorem exists_affine_stage_representative_eq
    {I : Type u} [Category.{u} I] [IsFiltered I]
    (R : I ⥤ CommRingCat.{u}) (c : Cocone R) (hc : IsColimit c)
    (i : I) {X : Scheme.{u}} (r : Spec (R.obj i) ⟶ X)
    (F : AbelianSheaf.{u, u + 1} X)
    {J : Type v} [Finite J] (Y : J → Over (Spec c.pt))
    [∀ j, IsAffine (Y j).left] [∀ j, Etale (Y j).hom]
    (hcover : ∀ x : Spec c.pt, ∃ j, ∃ y : (Y j).left, (Y j).hom y = x)
    (U V : X.Etale) (a : Spec (R.obj i) ⟶ U.left) (b : Spec (R.obj i) ⟶ V.left)
    (ha : a ≫ U.hom = r) (hb : b ≫ V.hom = r)
    (s : F.obj.obj (op U)) (t : F.obj.obj (op V))
    (T : J → X.Etale) (p : ∀ j, T j ⟶ U) (q : ∀ j, T j ⟶ V)
    (w : ∀ j, (Y j).left ⟶ (T j).left)
    (hw : ∀ j, w j ≫ (T j).hom = (Y j).hom ≫ Spec.map (c.ι.app i) ≫ r)
    (hp : ∀ j, w j ≫ (p j).left = (Y j).hom ≫ Spec.map (c.ι.app i) ≫ a)
    (hq : ∀ j, w j ≫ (q j).left = (Y j).hom ≫ Spec.map (c.ι.app i) ≫ b)
    (hst : ∀ j, F.obj.map (p j).op s = F.obj.map (q j).op t) :
    ∃ (k : I) (α : i ⟶ k),
      etaleRepresentativeSection F (Over.mk (Spec.map (R.map α) ≫ r)) U
          (Over.homMk (Spec.map (R.map α) ≫ a) ((Category.assoc _ _ _).trans
            (congrArg (fun z ↦ Spec.map (R.map α) ≫ z) ha))) s =
        etaleRepresentativeSection F (Over.mk (Spec.map (R.map α) ≫ r)) V
          (Over.homMk (Spec.map (R.map α) ≫ b) ((Category.assoc _ _ _).trans
            (congrArg (fun z ↦ Spec.map (R.map α) ≫ z) hb))) t := by
  classical
  obtain ⟨k, α, Z, hZ, he, e, hcov⟩ :=
    exists_affine_etale_cover_model_of_isColimit_above R c hc i Y hcover
  have (j : J) : IsAffine (Z j).left := hZ j
  have (j : J) : Etale (Z j).hom := he j
  let τ := Spec.map (R.map α)
  let σ := Spec.map (c.ι.app k)
  let E (j : J) : pullback σ (Z j).hom ⟶ (Y j).left :=
    (pullbackSymmetry σ (Z j).hom).hom ≫ (Classical.choice (e j)).hom.left
  have hE (j : J) : E j ≫ (Y j).hom = pullback.fst σ (Z j).hom :=
    (Category.assoc _ _ _).trans
      ((congrArg (fun z ↦ (pullbackSymmetry σ (Z j).hom).hom ≫ z)
        (Over.w (Classical.choice (e j)).hom)).trans
        (pullbackSymmetry_hom_comp_snd σ (Z j).hom))
  have hστ : σ ≫ τ = Spec.map (c.ι.app i) := by
    dsimp [σ, τ]
    rw [← Spec.map_comp, c.w]
  have htransport (j : J) {A : Scheme.{u}} (z : Spec (R.obj i) ⟶ A)
      (v : (Y j).left ⟶ A) (hv : v = (Y j).hom ≫ Spec.map (c.ι.app i) ≫ z) :
      E j ≫ v = pullback.snd σ (Z j).hom ≫ (Z j).hom ≫ (τ ≫ z) := by
    calc
      E j ≫ v = (E j ≫ (Y j).hom) ≫ Spec.map (c.ι.app i) ≫ z := by
        exact (congrArg (fun z ↦ E j ≫ z) hv).trans (Category.assoc _ _ _).symm
      _ = pullback.fst σ (Z j).hom ≫ Spec.map (c.ι.app i) ≫ z := by rw [hE]
      _ = pullback.fst σ (Z j).hom ≫ (σ ≫ τ) ≫ z := by rw [hστ]
      _ = (pullback.fst σ (Z j).hom ≫ σ) ≫ τ ≫ z := by
        simp only [Category.assoc]
      _ = (pullback.snd σ (Z j).hom ≫ (Z j).hom) ≫ τ ≫ z := by
        rw [pullback.condition]
      _ = _ := by simp only [Category.assoc]
  let D := R.op ⋙ Scheme.Spec
  let d := Scheme.Spec.mapCone c.op
  have hd : IsLimit d := isLimitOfPreserves Scheme.Spec hc.op
  have (j : Iᵒᵖ) : CompactSpace (D.obj j) :=
    inferInstanceAs (CompactSpace (Spec (R.obj j.unop)))
  have (j : Iᵒᵖ) : QuasiSeparatedSpace (D.obj j) :=
    inferInstanceAs (QuasiSeparatedSpace (Spec (R.obj j.unop)))
  have {j l : Iᵒᵖ} (f : j ⟶ l) : IsAffineHom (D.map f) :=
    inferInstanceAs (IsAffineHom (Spec.map (R.map f.unop)))
  obtain ⟨l, hl⟩ := exists_stage_etaleRepresentativeSection_eq D d hd (op k) (τ ≫ r) F
    Z hcov U V (τ ≫ a) (τ ≫ b)
    ((Category.assoc _ _ _).trans (congrArg (fun z ↦ τ ≫ z) ha))
    ((Category.assoc _ _ _).trans (congrArg (fun z ↦ τ ≫ z) hb))
    s t T p q (fun j ↦ E j ≫ w j)
    (fun j ↦ (Category.assoc _ _ _).trans (htransport j r _ (hw j)))
    (fun j ↦ (Category.assoc _ _ _).trans (htransport j a _ (hp j)))
    (fun j ↦ (Category.assoc _ _ _).trans (htransport j b _ (hq j))) hst
  refine ⟨l.left.unop, α ≫ l.hom.unop, ?_⟩
  have hmap : Spec.map (R.map (α ≫ l.hom.unop)) =
      Spec.map (R.map l.hom.unop) ≫ τ := by
    rw [Functor.map_comp, Spec.map_comp]
  have hcomp {A : Scheme.{u}} (z : Spec (R.obj i) ⟶ A) :
      D.map l.hom ≫ (τ ≫ z) = Spec.map (R.map (α ≫ l.hom.unop)) ≫ z :=
    (Category.assoc _ _ _).symm.trans (congrArg (fun k ↦ k ≫ z) hmap.symm)
  exact transport_representative_equality F U V
    ((Category.assoc _ _ _).trans (congrArg (fun z ↦ D.map l.hom ≫ z)
      ((Category.assoc _ _ _).trans (congrArg (fun z ↦ τ ≫ z) ha))))
    ((Category.assoc _ _ _).trans (congrArg (fun z ↦ D.map l.hom ≫ z)
      ((Category.assoc _ _ _).trans (congrArg (fun z ↦ τ ≫ z) hb))))
    ((Category.assoc _ _ _).trans
      (congrArg (fun z ↦ Spec.map (R.map (α ≫ l.hom.unop)) ≫ z) ha))
    ((Category.assoc _ _ _).trans
      (congrArg (fun z ↦ Spec.map (R.map (α ≫ l.hom.unop)) ≫ z) hb))
    s t (hcomp r) (hcomp a) (hcomp b) hl

end AlgebraicGeometry.Scheme.EtaleAffineBasis
