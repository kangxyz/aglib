/-
Copyright (c) 2026 kangxyz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.Descent.FinitePresentation.Diagrams
public import Mathlib.AlgebraicGeometry.Morphisms.Etale

/-! # Finite simultaneous maps from stage models to original etale targets

The original coefficient objects need not be affine or quasi-compact. Only
local finite presentation of their etale structural maps is used. Every output
map retains its structural triangle and its literal limit-cone comparison.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite

namespace AlgebraicGeometry.Scheme.EtaleAffineBasis

universe u v

/-- Maps from finitely many actual limit base changes to original etale
coefficient objects descend at one common stage, with their original triangles. -/
theorem exists_common_maps_to_etale_targets
    {I : Type u} [Category.{u} I] [IsCofiltered I]
    (D : I ⥤ Scheme.{u}) (c : Cone D) (hc : IsLimit c)
    [∀ i, CompactSpace (D.obj i)] [∀ i, QuasiSeparatedSpace (D.obj i)]
    [∀ {i j} (a : i ⟶ j), IsAffineHom (D.map a)]
    (i : I) {X : Scheme.{u}} (r : D.obj i ⟶ X)
    {J : Type v} [Finite J] (Z : J → Over (D.obj i))
    [∀ j, QuasiCompact (Z j).hom] [∀ j, QuasiSeparated (Z j).hom]
    (U : J → X.Etale)
    (a : ∀ j, pullback (c.π.app i) (Z j).hom ⟶ (U j).left)
    (ha : ∀ j, a j ≫ (U j).hom =
      pullback.snd (c.π.app i) (Z j).hom ≫ (Z j).hom ≫ r) :
    ∃ k : Over i, ∀ j, ∃ b : (Scheme.baseChangeDiagram D i (Z j).hom).obj k ⟶ (U j).left,
      b ≫ (U j).hom = pullback.snd (D.map k.hom) (Z j).hom ≫ (Z j).hom ≫ r ∧
      (Scheme.baseChangeCone D c i (Z j).hom).π.app k ≫ b = a j := by
  classical
  let t (j : J) : Scheme.baseChangeDiagram D i (Z j).hom ⟶
      (Functor.const (Over i)).obj X :=
    { app k := pullback.snd (D.map k.hom) (Z j).hom ≫ (Z j).hom ≫ r
      naturality {k l} q := by
        have h := Over.w ((Over.pullback (Z j).hom).map ((Over.post D).map q))
        exact (Category.assoc _ _ _).symm.trans
          ((congrArg (fun b => b ≫ (Z j).hom ≫ r) h).trans
            (Category.comp_id _).symm) }
  have hdesc (j : J) : ∃ (k : Over i)
      (b : (Scheme.baseChangeDiagram D i (Z j).hom).obj k ⟶ (U j).left),
      (Scheme.baseChangeCone D c i (Z j).hom).π.app k ≫ b = a j ∧
      b ≫ (U j).hom = (t j).app k := by
    have : Etale (U j).hom := (U j).prop
    apply Scheme.exists_π_app_comp_eq_of_locallyOfFinitePresentation
      (Scheme.baseChangeDiagram D i (Z j).hom) (t j) (U j).hom
      (Scheme.baseChangeCone D c i (Z j).hom)
      (Scheme.isLimitBaseChangeCone D c hc i (Z j).hom) (a j)
    ext k
    have h := Over.w ((Over.pullback (Z j).hom).map
      (((Over.conePost D i).obj c).π.app k))
    exact (Category.assoc _ _ _).symm.trans
      ((congrArg (fun b => b ≫ (Z j).hom ≫ r) h).trans (ha j).symm)
  choose k b hlimit hbase using hdesc
  let : Fintype J := Fintype.ofFinite J
  obtain ⟨l, hl⟩ := IsCofiltered.inf_objs_exists (Finset.univ.image k)
  let q (j : J) : l ⟶ k j := (hl (Finset.mem_image.mpr ⟨j, by simp, rfl⟩)).some
  refine ⟨l, fun j ↦ ⟨(Scheme.baseChangeDiagram D i (Z j).hom).map (q j) ≫ b j, ?_, ?_⟩⟩
  · rw [Category.assoc, hbase]
    exact ((t j).naturality (q j)).trans (Category.comp_id _)
  · rw [← Category.assoc, (Scheme.baseChangeCone D c i (Z j).hom).w (q j), hlimit]

end AlgebraicGeometry.Scheme.EtaleAffineBasis
