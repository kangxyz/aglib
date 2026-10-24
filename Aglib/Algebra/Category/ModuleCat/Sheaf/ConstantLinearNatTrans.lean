/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.Algebra.Category.ModuleCat.Sheaf.ConstantLinear
public import Mathlib.CategoryTheory.Linear.LinearFunctor

/-! # Lifting natural transformations to original module sheaves

Naturality with respect to scalar endomorphisms upgrades an underlying
abelian natural transformation between scalar-linear module-sheaf functors.
All module structures and the underlying section maps are unchanged.
-/

@[expose] public noncomputable section

open CategoryTheory

namespace ModuleCat.Sheaf

universe u v r w h

variable {C : Type u} [Category.{v} C] (R : Type r) [CommRing R]
  (J : GrothendieckTopology C)
  {D : Type w} [Category.{h} D] [Preadditive D] [CategoryTheory.Linear R D]
  (P Q : D ⥤ CategoryTheory.Sheaf J (ModuleCat.{max u v} R))
  [P.Linear R] [Q.Linear R]
  (t : P ⋙ underlying R J ⟶ Q ⋙ underlying R J)

/-- Scalar naturality lifts an underlying transformation to the existing module structures. -/
def natTransOfUnderlying : P ⟶ Q where
  app F := homOfUnderlying R J (F := P.obj F) (G := Q.obj F) (t.app F)
    (fun V r x => by
      have h := t.naturality (r • 𝟙 F)
      have hs : (underlying R J).map (r • 𝟙 (P.obj F)) ≫ t.app F =
          t.app F ≫ (underlying R J).map (r • 𝟙 (Q.obj F)) := by
        simpa only [Functor.comp_map, P.map_smul, Q.map_smul, P.map_id, Q.map_id] using h
      have hV := congrArg (fun k => k.hom.app V) hs
      exact ConcreteCategory.congr_hom (C := AddCommGrpCat.{max u v}) hV x)
  naturality F G f := by
    apply (underlying R J).map_injective
    exact t.naturality f

/-- Forgetting the lifted transformation returns its original component exactly. -/
@[simp]
theorem underlying_map_natTransOfUnderlying (F : D) :
    (underlying R J).map ((natTransOfUnderlying R J P Q t).app F) = t.app F := by
  rfl

end ModuleCat.Sheaf
