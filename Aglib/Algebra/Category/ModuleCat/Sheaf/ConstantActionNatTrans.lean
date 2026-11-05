/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aglib contributors
-/
module

public import Aglib.Algebra.Category.ModuleCat.Sheaf.ConstantRing.UnderlyingAction

/-! # Lifting maps compatible with the original left scalar action

The source category need not be linear over the scalar ring. Compatibility is
with the actual additive scalar transformations on the whole underlying
functors, so noncentral scalars are never treated as module endomorphisms.
-/

@[expose] public noncomputable section

open CategoryTheory
namespace ModuleCat.Sheaf
universe u v r w h
variable {C : Type u} [Category.{v} C] (R : Type r) [Ring R]
  (J : GrothendieckTopology C)

/-- Lift a genuinely scalar-compatible map of the original underlying sheaves. -/
def homOfUnderlyingAction
    {F G : CategoryTheory.Sheaf J (ModuleCat.{max u v} R)}
    (f : (underlying R J).obj F ⟶ (underlying R J).obj G)
    (hf : ∀ (U : Cᵒᵖ) (a : R) (x : F.obj.obj U),
      f.hom.app U (a • x) = a • (show G.obj.obj U from f.hom.app U x)) : F ⟶ G :=
  ⟨{
    app U := ModuleCat.ofHom { (f.hom.app U).hom with map_smul' := hf U }
    naturality U V k := by
      apply (forget₂ (ModuleCat.{max u v} R) AddCommGrpCat.{max u v}).map_injective
      exact f.hom.naturality k }⟩

variable {D : Type w} [Category.{h} D]
  (P Q : D ⥤ CategoryTheory.Sheaf J (ModuleCat.{max u v} R))
  (t : P ⋙ underlying R J ⟶ Q ⋙ underlying R J)
  (ht : ∀ (F : D) (a : R),
    (underlyingScalar J R a).app (P.obj F) ≫ t.app F =
      t.app F ≫ (underlyingScalar J R a).app (Q.obj F))

/-- Lift the original transformation from its actual scalar compatibility. -/
def natTransOfUnderlyingAction : P ⟶ Q where
  app F := homOfUnderlyingAction R J (t.app F) (fun U a x => by
    exact ConcreteCategory.congr_hom (C := AddCommGrpCat.{max u v})
      (congrArg (fun k => k.hom.app U) (ht F a)) x)
  naturality F G f := by
    apply (underlying R J).map_injective
    exact t.naturality f

/-- The underlying component is precisely the supplied original component. -/
@[simp]
theorem underlying_map_natTransOfUnderlyingAction (F : D) :
    (underlying R J).map ((natTransOfUnderlyingAction R J P Q t ht).app F) =
      t.app F := rfl

end ModuleCat.Sheaf
