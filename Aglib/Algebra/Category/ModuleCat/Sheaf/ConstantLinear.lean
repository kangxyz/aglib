/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.Algebra.Category.ModuleCat.Sheaf.ConstantCoefficients
public import Mathlib.CategoryTheory.Linear.FunctorCategory

/-! # Lifting underlying morphisms of constant-ring module sheaves

An original underlying abelian sheaf morphism which commutes with scalar
multiplication on sections is a morphism of the original ModuleCat-valued
sheaves. Forgetting the lifted morphism returns the supplied morphism exactly.
-/

@[expose] public noncomputable section

open CategoryTheory

namespace ModuleCat.Sheaf

universe u v r

variable {C : Type u} [Category.{v} C] (R : Type r) [CommRing R]
  (J : GrothendieckTopology C)
  {F G : CategoryTheory.Sheaf J (ModuleCat.{max u v} R)}

/-- Lift an underlying abelian morphism whose original section maps are scalar-linear. -/
def homOfUnderlying (f : (underlying R J).obj F ⟶ (underlying R J).obj G)
    (hf : ∀ (U : Cᵒᵖ) (r : R) (x : F.obj.obj U),
      f.hom.app U (r • x) = LinearMap.lsmul R (G.obj.obj U) r (f.hom.app U x)) : F ⟶ G :=
  ⟨{
    app U := ModuleCat.ofHom { (f.hom.app U).hom with map_smul' := hf U }
    naturality U V k := by
      apply (forget₂ (ModuleCat.{max u v} R) AddCommGrpCat.{max u v}).map_injective
      exact f.hom.naturality k }⟩

/-- The lift has precisely the supplied original underlying abelian morphism. -/
@[simp]
theorem underlying_map_homOfUnderlying
    (f : (underlying R J).obj F ⟶ (underlying R J).obj G)
    (hf : ∀ (U : Cᵒᵖ) (r : R) (x : F.obj.obj U),
      f.hom.app U (r • x) = LinearMap.lsmul R (G.obj.obj U) r (f.hom.app U x)) :
    (underlying R J).map (homOfUnderlying R J f hf) = f := by
  rfl

end ModuleCat.Sheaf
