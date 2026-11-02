/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.Algebra.Category.ModuleCat.Sheaf.InternalHom.Functor

/-! # Naturality from the original evaluation laws

For a fixed original coefficient sheaf, given evaluation morphisms into
the original double internal Hom, their actual section formulas imply
naturality. No evaluation morphism or alternative dual is constructed here.
The module carrier universe is closed under the native internal Hom.
-/

@[expose] public noncomputable section

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open CategoryTheory Opposite

universe uC vC uR uM

namespace SheafOfModules.InternalHom

variable {C : Type uC} [Category.{vC} C] {J : GrothendieckTopology C}
  [J.HasSheafCompose (forget₂ CommRingCat.{uR} RingCat.{uR})]
  (R : Sheaf J CommRingCat.{uR})
  (M N O : SheafOfModules.{max uC vC uM}
    ((sheafCompose J (forget₂ CommRingCat RingCat)).obj R))

/-- The full original evaluation formulas force the original naturality square. -/
theorem evaluation_naturality_of_section_formula
    (eM : M ⟶ sheaf R (sheaf R M O) O)
    (eN : N ⟶ sheaf R (sheaf R N O) O)
    (hM : ∀ (U : C) (m : M.val.obj (op U)) (V : (Over U)ᵒᵖ)
      (ell : (sheaf R M O).val.obj (op V.unop.left)),
      (eM.val.app (op U) m).val.app V ell =
        ell.val.app (op (Over.mk (𝟙 V.unop.left))) (M.val.map V.unop.hom.op m))
    (hN : ∀ (U : C) (m : N.val.obj (op U)) (V : (Over U)ᵒᵖ)
      (ell : (sheaf R N O).val.obj (op V.unop.left)),
      (eN.val.app (op U) m).val.app V ell =
        ell.val.app (op (Over.mk (𝟙 V.unop.left))) (N.val.map V.unop.hom.op m))
    (f : M ⟶ N) :
    f ≫ eN = eM ≫ map R (map R f (𝟙 O)) (𝟙 O) := by
  apply SheafOfModules.hom_ext
  ext U : 1
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro m
  apply Subtype.ext
  change (_ : RawHom R (sheaf R N O) O U.unop) = _
  ext V ell
  have h₁ := hN U.unop (f.val.app U m) V ell
  have h₂ := map_apply R (map R f (𝟙 O)) (𝟙 O) U.unop
    (eM.val.app U m) V ell
  have h₃ := hM U.unop m V ((map R f (𝟙 O)).val.app (op V.unop.left) ell)
  have h₄ := map_apply R f (𝟙 O) V.unop.left ell
    (op (Over.mk (𝟙 V.unop.left))) (M.val.map V.unop.hom.op m)
  have hn := congrArg (fun n => ell.val.app (op (Over.mk (𝟙 V.unop.left))) n)
    (ConcreteCategory.congr_hom (f.val.naturality V.unop.hom.op) m).symm
  exact h₁.trans (hn.trans (h₄.symm.trans (h₃.symm.trans h₂.symm)))

end SheafOfModules.InternalHom
