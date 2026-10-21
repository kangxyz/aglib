/-
Copyright (c) 2026 algebraic-geometry contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.CategoryTheory.Abelian.CoproductKernels

/-! # Transporting actual kernels to coproduct components -/

@[expose] public noncomputable section
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false

open CategoryTheory CategoryTheory.Limits
namespace CategoryTheory.Limits
universe u v w u' v'
variable {C : Type u} [Category.{v} C] [Abelian C]
  {D : Type u'} [Category.{v'} D] [Abelian D]
  {ι : Type w} [HasCoproducts.{w} C] [AB4OfSize.{w} C]
  (T : D ⥤ C) [T.PreservesZeroMorphisms] [PreservesFiniteLimits T]
  {P Q R : ι → C} (f : ∀ i, P i ⟶ Q i) (eR : ∀ i, R i ≅ kernel (f i))
  {G H : D} (g : G ⟶ H)
  (eP : T.obj G ≅ ∐ P) (eQ : T.obj H ≅ ∐ Q)
  (h : T.map g ≫ eQ.hom = eP.hom ≫ Sigma.map f)

/-- A limit-preserving functor and an actual coproduct square identify the
original kernel with the coproduct of the specified component kernels. -/
def mapKernelCoproductIso : T.obj (kernel g) ≅ ∐ R :=
  PreservesKernel.iso T g ≪≫ kernel.mapIso (T.map g) (Sigma.map f) eP eQ h ≪≫
    (coproductKernelIso f).symm ≪≫ (Sigma.mapIso eR).symm

/-- The comparison retains every original kernel inclusion. -/
@[reassoc (attr := simp)]
theorem mapKernelCoproductIso_inv_ι :
    (mapKernelCoproductIso T f eR g eP eQ h).inv ≫ T.map (kernel.ι g) ≫ eP.hom =
      Sigma.map (fun i => (eR i).hom ≫ kernel.ι (f i)) := by
  dsimp only [mapKernelCoproductIso, Iso.trans_inv, Iso.symm_inv]
  simp only [Category.assoc, kernel.mapIso_inv, kernel.map]
  apply Sigma.hom_ext
  intro i
  simp

end CategoryTheory.Limits
