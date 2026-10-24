/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.Modules.Invertible.Nonvanishing

/-! # Nonvanishing in an actual global unit frame

An actual global trivialization computes the section's geometric nonvanishing
open as the basic open of its literal coefficient. In particular, when all
global functions come from a field, a nonzero section of an actually trivial
line bundle is nowhere vanishing. The structural field map is retained.
-/

@[expose] public noncomputable section

set_option backward.isDefEq.respectTransparency false

open AlgebraicGeometry CategoryTheory Opposite

universe u

namespace AlgebraicGeometry.Scheme.Modules.Invertible.Nonvanishing

variable {X : Scheme.{u}}

/-- A global actual unit frame computes the original nonvanishing open by
the literal global coefficient of the original section. -/
theorem nonvanishingOpen_eq_basicOpen_of_unitIso (L : LineBundle X)
    (e : L.val ≅ SheafOfModules.unit X.ringCatSheaf) (s : Γ(L.val, ⊤)) :
    nonvanishingOpen L s = X.basicOpen (e.hom.val.app (op ⊤) s) := by
  let M : X.Modules := L.val
  let d := (SheafOfModules.overFunctor X.ringCatSheaf ⊤).mapIso e
  have h := inter_nonvanishingOpen L s ⊤ d
  have hres : M.presheaf.map (homOfLE (show (⊤ : X.Opens) ≤ ⊤ from le_top)).op s = s := by
    change M.presheaf.map (𝟙 (op ⊤)) s = s
    rw [CategoryTheory.Functor.map_id]
    rfl
  change ⊤ ⊓ nonvanishingOpen L s =
    X.basicOpen (e.hom.val.app (op ⊤)
      (M.presheaf.map (homOfLE (show (⊤ : X.Opens) ≤ ⊤ from le_top)).op s)) at h
  simpa only [top_inf_eq, hres] using h

/-- If every global function is a constant from a field, every nonzero
section in an actual unit frame is nowhere vanishing. -/
theorem nonvanishingOpen_eq_top_of_field_constants
    {k : Type u} [Field k] (c : k →+* Γ(X, ⊤)) (hc : Function.Surjective c)
    (L : LineBundle X) (e : L.val ≅ SheafOfModules.unit X.ringCatSheaf)
    (s : Γ(L.val, ⊤)) (hs : s ≠ 0) : nonvanishingOpen L s = ⊤ := by
  let M : X.Modules := L.val
  let d := (SheafOfModules.overFunctor X.ringCatSheaf ⊤).mapIso e
  let E := chartSectionEquiv X M ⊤ d ⊤ le_rfl
  let b : Γ(X, ⊤) := e.hom.val.app (op ⊤) s
  have he : b ≠ 0 := by
    intro hz
    apply hs
    change E s = 0 at hz
    exact E.injective (hz.trans E.map_zero.symm)
  obtain ⟨a, ha⟩ := hc b
  have ha0 : a ≠ 0 := by
    intro hz
    apply he
    rw [← ha, hz, map_zero]
  have hu : IsUnit b := by
    rw [← ha]
    exact (isUnit_iff_ne_zero.mpr ha0).map c
  rw [nonvanishingOpen_eq_basicOpen_of_unitIso L e s]
  exact X.basicOpen_of_isUnit hu

end AlgebraicGeometry.Scheme.Modules.Invertible.Nonvanishing
