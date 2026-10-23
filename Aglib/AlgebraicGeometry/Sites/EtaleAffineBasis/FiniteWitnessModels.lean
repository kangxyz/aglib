/-
Copyright (c) 2026 kangxyz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.EtaleCohomology.Continuity.RelativeFactorization
public import Mathlib.AlgebraicGeometry.Morphisms.Etale

/-!
# Common stage models for finite equality witnesses

The two original target triangles of each local equality witness descend
simultaneously. The coefficient targets need not be affine. The source systems
are arbitrary qcqs systems with affine transition maps.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite

namespace AlgebraicGeometry.Scheme.EtaleAffineBasis

universe u v

open EtaleCohomology.Continuity

/-- Descend finitely many common representatives, retaining both target
triangles and their literal comparison with the limit representatives. -/
theorem exists_common_etale_witness_models
    {I : Type u} [Category.{u} I] [IsCofiltered I]
    {X : Scheme.{u}} {J : Type v} [Finite J]
    (D : J → I ⥤ Over X) (c : ∀ j, Cone (D j))
    (hc : ∀ j, IsLimit ((Over.forget X).mapCone (c j)))
    [∀ j i, CompactSpace ((D j).obj i).left]
    [∀ j i, QuasiSeparatedSpace ((D j).obj i).left]
    [∀ j {i k} (q : i ⟶ k), IsAffineHom ((D j).map q).left]
    (T U V : J → X.Etale) (i : I)
    (a : ∀ j, (D j).obj i ⟶ Over.mk (U j).hom)
    (b : ∀ j, (D j).obj i ⟶ Over.mk (V j).hom)
    (p : ∀ j, T j ⟶ U j) (q : ∀ j, T j ⟶ V j)
    (s : ∀ j, (c j).pt ⟶ Over.mk (T j).hom)
    (hp : ∀ j, s j ≫ (Etale.forget X).map (p j) = (c j).π.app i ≫ a j)
    (hq : ∀ j, s j ≫ (Etale.forget X).map (q j) = (c j).π.app i ≫ b j) :
    ∃ (k : I) (f : k ⟶ i) (r : ∀ j, (D j).obj k ⟶ Over.mk (T j).hom),
      (∀ j, r j ≫ (Etale.forget X).map (p j) = (D j).map f ≫ a j) ∧
      (∀ j, r j ≫ (Etale.forget X).map (q j) = (D j).map f ≫ b j) ∧
      ∀ j, (c j).π.app k ≫ r j = s j := by
  classical
  have hfp (W : X.Etale) : LocallyOfFinitePresentation (Over.mk W.hom).hom :=
    inferInstanceAs (LocallyOfFinitePresentation W.hom)
  have heach (j : J) : ∃ (k : I) (f : k ⟶ i)
      (r : (D j).obj k ⟶ Over.mk (T j).hom),
      r ≫ (Etale.forget X).map (p j) = (D j).map f ≫ a j ∧
      r ≫ (Etale.forget X).map (q j) = (D j).map f ≫ b j ∧
      (c j).π.app k ≫ r = s j := by
    obtain ⟨k, f, r, hrp, hrs⟩ := exists_relative_factorization
      (D j) (c j) (hc j) (U := Over.mk (T j).hom) (V := Over.mk (U j).hom)
      i (a j) ((Etale.forget X).map (p j)) (s j) (hp j)
    have heq : (c j).π.app k ≫ (r ≫ (Etale.forget X).map (q j)) =
        (c j).π.app k ≫ ((D j).map f ≫ b j) := by
      exact (Category.assoc _ _ _).symm.trans
        ((congrArg (fun z ↦ z ≫ (Etale.forget X).map (q j)) hrs).trans
          ((hq j).trans ((congrArg (fun z ↦ z ≫ b j) ((c j).w f).symm).trans
            (Category.assoc _ _ _))))
    obtain ⟨l, g, hg⟩ := (Types.FilteredColimit.isColimit_eq_iff'
      (representedSectionsCoconeIsColimit (D j) (c j) (hc j) (Over.mk (V j).hom))
      (r ≫ (Etale.forget X).map (q j)) ((D j).map f ≫ b j)).mp heq
    refine ⟨l.unop, g.unop ≫ f, (D j).map g.unop ≫ r, ?_, ?_, ?_⟩
    · exact (Category.assoc _ _ _).trans
        ((congrArg (fun z ↦ (D j).map g.unop ≫ z) hrp).trans
          ((Category.assoc _ _ _).symm.trans
            (congrArg (fun z ↦ z ≫ a j) ((D j).map_comp g.unop f).symm)))
    · exact (Category.assoc _ _ _).trans
        (hg.trans ((Category.assoc _ _ _).symm.trans
          (congrArg (fun z ↦ z ≫ b j) ((D j).map_comp g.unop f).symm)))
    · rw [← Category.assoc, (c j).w g.unop, hrs]
  choose k f r hrp hrq hrs using heach
  let : Fintype J := Fintype.ofFinite J
  obtain ⟨l, g, h, hh⟩ := IsCofiltered.wideCospan f
  refine ⟨l, g, fun j ↦ (D j).map (h j) ≫ r j, ?_, ?_, ?_⟩
  · intro j
    have hm := ((D j).map_comp (h j) (f j)).symm.trans
      (congrArg (D j).map (hh j))
    exact (Category.assoc _ _ _).trans
      ((congrArg (fun z ↦ (D j).map (h j) ≫ z) (hrp j)).trans
        ((Category.assoc _ _ _).symm.trans (congrArg (fun z ↦ z ≫ a j) hm)))
  · intro j
    have hm := ((D j).map_comp (h j) (f j)).symm.trans
      (congrArg (D j).map (hh j))
    exact (Category.assoc _ _ _).trans
      ((congrArg (fun z ↦ (D j).map (h j) ≫ z) (hrq j)).trans
        ((Category.assoc _ _ _).symm.trans (congrArg (fun z ↦ z ≫ b j) hm)))
  · intro j
    rw [← Category.assoc, (c j).w (h j), hrs]

end AlgebraicGeometry.Scheme.EtaleAffineBasis
