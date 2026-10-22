/-
Copyright (c) 2026 kangxyz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.Descent.FinitePresentation.RelativeClosedImmersion
public import Aglib.AlgebraicGeometry.Limits.ImmersionBaseChange

/-!
# Eventual separatedness of the original stage morphism

Separatedness descends along qcqs affine-transition base systems for a
quasi-compact quasi-separated stage morphism. The diagonal is always an
immersion, so no finite-presentation or Noetherian hypothesis is needed.
-/

@[expose] public section

noncomputable section

open CategoryTheory CategoryTheory.Limits

universe u

namespace AlgebraicGeometry.Scheme

/-- A quasi-compact quasi-separated stage morphism that is separated over
the limit is separated after a later actual base transition. -/
theorem exists_isSeparated_baseChange_of_isLimit
    {I : Type u} [Category.{u} I] [IsCofiltered I]
    (D : I ⥤ Scheme.{u})
    [∀ {i j} (q : i ⟶ j), IsAffineHom (D.map q)]
    [∀ i, CompactSpace (D.obj i)] [∀ i, QuasiSeparatedSpace (D.obj i)]
    (c : Cone D) (hc : IsLimit c) (i : I)
    {X : Scheme.{u}} (f : X ⟶ D.obj i) [QuasiCompact f] [QuasiSeparated f]
    [IsSeparated (pullback.fst (c.π.app i) f)] :
    ∃ j : Over i, IsSeparated (pullback.fst (D.map j.hom) f) := by
  obtain ⟨j, hj⟩ := exists_isClosed_preimage_range_of_isLimit D c hc i
    (pullback.diagonal f) (pullback.snd f f ≫ f)
    ((isSeparated_pullback_fst_iff_isClosed_preimage_diagonal f (c.π.app i)).mp inferInstance)
  exact ⟨j, (isSeparated_pullback_fst_iff_isClosed_preimage_diagonal f (D.map j.hom)).mpr hj⟩

end AlgebraicGeometry.Scheme
