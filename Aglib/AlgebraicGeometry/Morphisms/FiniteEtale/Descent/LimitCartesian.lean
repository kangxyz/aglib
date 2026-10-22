/-
Copyright (c) 2026 kangxyz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.Descent.FinitePresentation.Schemes
public import Mathlib.CategoryTheory.Limits.Constructions.Over.Connected

/-!
# Eventual cartesianness of finite families of model squares

Only the cartesian comparison morphisms become invertible. The arrows between
open charts need not become isomorphisms, and no faithful base change is used.
-/

@[expose] public noncomputable section

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

namespace AlgebraicGeometry.Scheme.FiniteEtale.LimitDescent

universe u v w

private theorem isIso_comparison_of_isPullback
    {C : Type u} [Category.{v} C] {A P B E Z : C}
    {a : A ⟶ B} {b : A ⟶ E} {p : P ⟶ B} {r : P ⟶ E}
    {f : B ⟶ Z} {g : E ⟶ Z}
    (H : IsPullback a b f g) (K : IsPullback p r f g)
    (q : A ⟶ P) (hq : q ≫ p = a) (hr : q ≫ r = b) : IsIso q := by
  have h : q = (H.isoIsPullback B E K).hom := by
    apply K.hom_ext
    · exact hq.trans (H.isoIsPullback_hom_fst B E K).symm
    · exact hr.trans (H.isoIsPullback_hom_snd B E K).symm
  rw [h]
  infer_instance

private theorem isPullback_of_isIso_comparison
    {C : Type u} [Category.{v} C] {A P B E Z : C}
    {a : A ⟶ B} {b : A ⟶ E} {p : P ⟶ B} {r : P ⟶ E}
    {f : B ⟶ Z} {g : E ⟶ Z}
    (K : IsPullback p r f g) (q : A ⟶ P) [IsIso q]
    (hq : q ≫ p = a) (hr : q ≫ r = b) : IsPullback a b f g := by
  refine K.of_iso (asIso q).symm (.refl _) (.refl _) (.refl _) ?_ ?_ ?_ ?_
  · simp [← hq]
  · simp [← hr]
  · simp
  · simp

/-- Finitely many model squares which are cartesian at the limit become
cartesian at one stage, provided their specified cartesian-comparison targets
are finitely presented models. -/
theorem exists_common_cartesian_stage
    {I : Type u} [Category.{u} I] [IsCofiltered I]
    (D : I ⥤ Scheme.{u})
    [∀ {i j} (f : i ⟶ j), IsAffineHom (D.map f)]
    [∀ i, CompactSpace (D.obj i)] [∀ i, QuasiSeparatedSpace (D.obj i)]
    (c : Cone D) (hc : IsLimit c) (i : I)
    {J : Type w} [Finite J]
    (A P B E Z : J → Over (D.obj i))
    [∀ j, LocallyOfFinitePresentation (A j).hom] [∀ j, QuasiCompact (A j).hom]
    [∀ j, LocallyOfFinitePresentation (P j).hom] [∀ j, QuasiCompact (P j).hom]
    [∀ j, QuasiSeparated (P j).hom]
    (a : ∀ j, A j ⟶ B j) (b : ∀ j, A j ⟶ E j)
    (p : ∀ j, P j ⟶ B j) (r : ∀ j, P j ⟶ E j)
    (f : ∀ j, B j ⟶ Z j) (g : ∀ j, E j ⟶ Z j)
    (K : ∀ j, IsPullback (p j) (r j) (f j) (g j))
    (q : ∀ j, A j ⟶ P j) (hq : ∀ j, q j ≫ p j = a j)
    (hr : ∀ j, q j ≫ r j = b j)
    (H : ∀ j, IsPullback ((Over.pullback (c.π.app i)).map (a j))
      ((Over.pullback (c.π.app i)).map (b j))
      ((Over.pullback (c.π.app i)).map (f j))
      ((Over.pullback (c.π.app i)).map (g j))) :
    ∃ k : Over i, ∀ j, IsPullback ((Over.pullback (D.map k.hom)).map (a j))
      ((Over.pullback (D.map k.hom)).map (b j))
      ((Over.pullback (D.map k.hom)).map (f j))
      ((Over.pullback (D.map k.hom)).map (g j)) := by
  have (j : J) : IsIso ((Over.pullback (c.π.app i)).map (q j)) :=
    isIso_comparison_of_isPullback (H j) ((K j).map (Over.pullback (c.π.app i)))
      ((Over.pullback (c.π.app i)).map (q j))
      (by rw [← Functor.map_comp, hq]) (by rw [← Functor.map_comp, hr])
  obtain ⟨k, hk⟩ := Scheme.exists_common_stage_isIso_baseChange_maps_of_isLimit
    D c hc i (fun j ↦ (A j).hom) (fun j ↦ (P j).hom) q
  refine ⟨k, fun j ↦ ?_⟩
  let : IsIso ((Over.pullback (D.map k.hom)).map (q j)) := hk j
  exact isPullback_of_isIso_comparison ((K j).map (Over.pullback (D.map k.hom)))
    ((Over.pullback (D.map k.hom)).map (q j))
    (by rw [← Functor.map_comp, hq]) (by rw [← Functor.map_comp, hr])

end AlgebraicGeometry.Scheme.FiniteEtale.LimitDescent
