/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Mathlib.CategoryTheory.Galois.Full

/-! # Actual morphisms from invariant fibre points

Fullness of the native finite-action functor lifts the constant equivariant
map. In particular, a terminal source gives an actual global section with
its literal fibre evaluation, not merely an abstract existence comparison.
-/

@[expose] public noncomputable section

namespace CategoryTheory.PreGaloisCategory

universe c h v

variable {C : Type c} [Category.{h} C] [GaloisCategory C]
  (F : C ⥤ FintypeCat.{v}) [FiberFunctor F]

/-- An invariant fibre point determines an actual morphism with constant fibre
map. The terminal-source specialization is the global-section construction. -/
theorem exists_hom_of_fixed_fiber_point {T A : C} (a : F.obj A)
    (ha : ∀ g : Aut F, g • a = a) :
    ∃ f : T ⟶ A, ∀ t : F.obj T, F.map f t = a := by
  let q : (functorToAction F).obj T ⟶ (functorToAction F).obj A :=
    { hom := FintypeCat.homMk (fun _ => a)
      comm := fun g => by
        ext t
        change a = g • a
        exact (ha g).symm }
  refine ⟨(functorToAction F).preimage q, ?_⟩
  intro t
  have h := congrArg (fun f => f.hom) ((functorToAction F).map_preimage q)
  exact ConcreteCategory.congr_hom h t

end CategoryTheory.PreGaloisCategory
