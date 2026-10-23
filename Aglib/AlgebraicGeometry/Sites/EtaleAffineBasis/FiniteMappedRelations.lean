/-
Copyright (c) 2026 kangxyz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.EtaleCohomology.Continuity.SchemeLimitSections
public import Mathlib.AlgebraicGeometry.Morphisms.Etale

/-! # Common finite stages for equations between original relative maps

This supplies the equality part of finite local-witness descent. The source
systems are qcqs with affine transitions and need not be etale over the fixed
base. Every target is an original etale coefficient object.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite

namespace AlgebraicGeometry.Scheme.EtaleAffineBasis

universe u v

open EtaleCohomology.Continuity

/-- Finitely many equalities of maps to original etale objects, holding at the
actual limits, hold simultaneously at one common later stage. -/
theorem exists_common_equalities_to_etale_targets
    {I : Type u} [Category.{u} I] [IsCofiltered I]
    {X : Scheme.{u}} {J : Type v} [Finite J]
    (D : J → I ⥤ Over X) (c : ∀ j, Cone (D j))
    (hc : ∀ j, IsLimit ((Over.forget X).mapCone (c j)))
    [∀ j i, CompactSpace ((D j).obj i).left]
    [∀ j i, QuasiSeparatedSpace ((D j).obj i).left]
    [∀ j {i k} (q : i ⟶ k), IsAffineHom ((D j).map q).left]
    (U : J → X.Etale) (i : I)
    (a b : ∀ j, (D j).obj i ⟶ Over.mk (U j).hom)
    (h : ∀ j, (c j).π.app i ≫ a j = (c j).π.app i ≫ b j) :
    ∃ (k : I) (q : k ⟶ i), ∀ j, (D j).map q ≫ a j = (D j).map q ≫ b j := by
  classical
  have heach (j : J) : ∃ (k : I) (q : k ⟶ i),
      (D j).map q ≫ a j = (D j).map q ≫ b j := by
    have : Etale (U j).hom := (U j).prop
    have : LocallyOfFinitePresentation (Over.mk (U j).hom).hom :=
      inferInstanceAs (LocallyOfFinitePresentation (U j).hom)
    obtain ⟨k, q, hq⟩ := (Types.FilteredColimit.isColimit_eq_iff'
      (representedSectionsCoconeIsColimit (D j) (c j) (hc j) (Over.mk (U j).hom))
      (a j) (b j)).mp (h j)
    exact ⟨k.unop, q.unop, hq⟩
  choose k q hq using heach
  let : Fintype J := Fintype.ofFinite J
  obtain ⟨l, r, s, hs⟩ := IsCofiltered.wideCospan q
  refine ⟨l, r, fun j ↦ ?_⟩
  rw [← hs j, Functor.map_comp, Category.assoc, hq,
    ← Category.assoc, ← Functor.map_comp, hs j]

end AlgebraicGeometry.Scheme.EtaleAffineBasis
