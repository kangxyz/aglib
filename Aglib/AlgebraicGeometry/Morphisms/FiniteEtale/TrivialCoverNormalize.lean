/-
Copyright (c) 2026 kangxyz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/

module

public import Aglib.AlgebraicGeometry.Morphisms.FiniteEtale.TrivialCoverFunctor

/-! A trivialization normalized by its actual geometric fibre. -/

@[expose] public section

noncomputable section
set_option autoImplicit false

open _root_.CategoryTheory _root_.CategoryTheory.Limits AlgebraicGeometry

namespace AlgebraicGeometry.Scheme.FiniteEtale
open _root_.AlgebraicGeometry.Scheme.FiniteEtale (fiberToFinite)

universe u
variable {X : Scheme.{u}} {K : Type u} [Field K]
    (s : Spec (CommRingCat.of K) ⟶ X) {A : FintypeCat.{u}} {Y : Scheme.FiniteEtale X}
    (e : (trivialCoverFunctor X).obj A ≅ Y)

/-- The isomorphism from the label set `A` to the fiber of `Y` , induced by the supplied
trivialization `e` . -/
def trivialCoverFiberLabelIso : A ≅ (fiberToFinite s).obj Y :=
  (trivialCoverFunctorFiberIso s).app A ≪≫ (fiberToFinite s).mapIso e

/-- The trivialization of `Y` relabeled by its own fiber at `s` , using the supplied
trivialization `e` . -/
def normalizedTrivialCoverIso :
    (trivialCoverFunctor X).obj ((fiberToFinite s).obj Y) ≅ Y :=
  (trivialCoverFunctor X).mapIso (trivialCoverFiberLabelIso s e).symm ≪≫ e

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
theorem normalizedTrivialCoverIso_fiber :
    (fiberToFinite s).map (normalizedTrivialCoverIso s e).hom =
      ((trivialCoverFunctorFiberIso s).app ((fiberToFinite s).obj Y)).inv := by
  apply (cancel_epi ((trivialCoverFunctorFiberIso s).app ((fiberToFinite s).obj Y)).hom).mp
  change _ ≫ (fiberToFinite s).map
      ((trivialCoverFunctor X).map (trivialCoverFiberLabelIso s e).inv ≫ e.hom) = _
  rw [Functor.map_comp, ← Category.assoc]
  have h := (trivialCoverFunctorFiberIso s).hom.naturality
    (trivialCoverFiberLabelIso s e).inv
  change _ ≫ ((trivialCoverFunctorFiberIso s).app A).hom =
    ((trivialCoverFunctorFiberIso s).app ((fiberToFinite s).obj Y)).hom ≫
      (fiberToFinite s).map ((trivialCoverFunctor X).map (trivialCoverFiberLabelIso s e).inv) at h
  rw [← h, Category.assoc]
  change (trivialCoverFiberLabelIso s e).inv ≫ (trivialCoverFiberLabelIso s e).hom = _
  rw [Iso.inv_hom_id, Iso.hom_inv_id]
  rfl

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
theorem normalizedTrivialCoverIso_fiber_naturality (f : Y ⟶ Y) :
    (fiberToFinite s).map
        ((trivialCoverFunctor X).map ((fiberToFinite s).map f) ≫
          (normalizedTrivialCoverIso s e).hom) =
      (fiberToFinite s).map ((normalizedTrivialCoverIso s e).hom ≫ f) := by
  rw [Functor.map_comp, Functor.map_comp, normalizedTrivialCoverIso_fiber]
  exact ((trivialCoverFunctorFiberIso s).inv.naturality ((fiberToFinite s).map f))

end AlgebraicGeometry.Scheme.FiniteEtale

/- Migration source: the R5Lab/Aglib mirror; exact module in the migration record.
R5 revision c82abf3a72ce1e1cedf4a4f1fe08bea994ad4df5.
SHA256 322d8d0f9d8b409d7d1c826a5aa5162ad67d5b9b7feb2af9718ed0534c5dbee4.
Definitions, hypotheses and universes are retained modulo native names. -/
