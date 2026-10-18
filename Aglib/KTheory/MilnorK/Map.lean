/-
Copyright (c) 2026 Motivic Cohomology contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.KTheory.MilnorK.Basic

/-!
# Field functoriality in every Milnor degree

A field homomorphism acts coordinatewise on the actual symbol presentation.
Its preservation of multiplicativity and of the equation `a + b = 1` proves
that the map descends. Identity and composition follow from the universal
property. The fields may occupy different universes.
-/

@[expose] public section

noncomputable section

namespace MilnorK

universe u v w

variable {F : Type u} {E : Type v} {L : Type w} [Field F] [Field E] [Field L]
variable (n : ℕ)

/-- A field map induces the usual map of Milnor groups in every degree. -/
def map (f : F →+* E) : K F n →ₗ[ℤ] K E n :=
  lift (fun a => symbol ((Units.map f.toMonoidHom) ∘ a)) {
    map_mul := by
      intro a i b c
      simp only [Function.comp_update, map_mul]
      exact symbol_mul _ i _ _
    steinberg := by
      intro a i j hij h
      apply steinberg _ i j hij
      change f (a i : F) + f (a j : F) = 1
      rw [← map_add, h, map_one] }

/-- Symbols are sent to symbols of the coordinatewise field images. -/
@[simp] theorem map_symbol (f : F →+* E) (a : SymbolTuple F n) :
    map n f (symbol a) = symbol ((Units.map f.toMonoidHom) ∘ a) :=
  lift_symbol _ _ _

/-- The identity field map acts identically on every Milnor group. -/
@[simp] theorem map_id : map n (RingHom.id F) = LinearMap.id := by
  apply linearMap_ext
  intro a
  simp [map_symbol, Units.map, Function.comp_def]

/-- Composition of field maps is preserved in every degree. -/
theorem map_comp (f : F →+* E) (g : E →+* L) :
    map n (g.comp f) = (map n g).comp (map n f) := by
  apply linearMap_ext
  intro a
  simp only [LinearMap.comp_apply, map_symbol]
  rfl

/-- The additive version of the same field-induced map. -/
def mapAdd (f : F →+* E) : K F n →+ K E n := (map n f).toAddMonoidHom

/-- The additive map has the same coordinatewise symbol formula. -/
@[simp] theorem mapAdd_symbol (f : F →+* E) (a : SymbolTuple F n) :
    mapAdd n f (symbol a) = symbol ((Units.map f.toMonoidHom) ∘ a) :=
  map_symbol n f a

end MilnorK
