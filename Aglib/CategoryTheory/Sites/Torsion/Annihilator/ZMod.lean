/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.CategoryTheory.Preadditive.Annihilator.Kernels
public import Aglib.CategoryTheory.Sites.Torsion.Annihilator.Basic
public import Aglib.CategoryTheory.Sites.Torsion.ZMod.Full
public import Aglib.CategoryTheory.Sites.Torsion.ZMod.Sheaf

/-! # Genuine ZMod annihilator targets on a fixed site

An arrow from the original underlying sheaf of a genuine ZMod module factors
through the actual native annihilator. Fullness of native scalar forgetting
lifts the factorization with the original source action, and faithfulness
reflects monicity. The target has its existing canonical scalar structure and
its existing underlying-sheaf isomorphism. Every natural modulus is allowed.
-/

@[expose] public noncomputable section

open CategoryTheory.Limits

namespace CategoryTheory.TorsionZMod

universe u v w

variable {C : Type u} [Category.{v} C] (J : GrothendieckTopology C) (n : ℕ)

private theorem module_nsmul (M : ModuleCat.{w} (ZMod n)) (x : M) : n • x = 0 := by
  rw [← Nat.cast_smul_eq_nsmul (R := ZMod n), ZMod.natCast_self, zero_smul]

section Underlying

variable [J.HasSheafCompose (forget₂ (ModuleCat.{w} (ZMod n)) AddCommGrpCat.{w})]

/-- The original underlying abelian sheaf is killed by its genuine scalar modulus. -/
theorem sheafUnderlying_nsmul_id (M : Sheaf J (ModuleCat.{w} (ZMod n))) :
    n • 𝟙 ((sheafCompose J
      (forget₂ (ModuleCat.{w} (ZMod n)) AddCommGrpCat.{w})).obj M) = 0 := by
  apply Sheaf.hom_ext
  apply NatTrans.ext
  funext U
  apply AddCommGrpCat.hom_ext
  apply AddMonoidHom.ext
  intro x
  exact module_nsmul n (M.obj.obj U) x

end Underlying

variable [HasSheafify J AddCommGrpCat.{w}]

/-- The existing canonical genuine module structure on the actual native annihilator. -/
def annihilator (G : Sheaf J AddCommGrpCat.{w}) : Sheaf J (ModuleCat.{w} (ZMod n)) :=
  sheaf J n (Sheaf.annihilator G n) (Sheaf.nsmul_id_annihilator G n)

variable [J.HasSheafCompose (forget₂ (ModuleCat.{w} (ZMod n)) AddCommGrpCat.{w})]

/-- The original scalar-conversion comparison with the actual native annihilator. -/
def annihilatorUnderlyingIso (G : Sheaf J AddCommGrpCat.{w}) :
    (sheafCompose J (forget₂ (ModuleCat.{w} (ZMod n)) AddCommGrpCat.{w})).obj
        (annihilator J n G) ≅ Sheaf.annihilator G n :=
  sheafUnderlyingIso J n (Sheaf.annihilator G n) (Sheaf.nsmul_id_annihilator G n)

/-- Lift the original abelian arrow without changing its genuine source module. -/
def annihilatorLift (M : Sheaf J (ModuleCat.{w} (ZMod n)))
    (G : Sheaf J AddCommGrpCat.{w})
    (a : (sheafCompose J (forget₂ (ModuleCat.{w} (ZMod n)) AddCommGrpCat.{w})).obj M ⟶ G) :
    M ⟶ annihilator J n G := by
  let : (sheafCompose J
      (forget₂ (ModuleCat.{w} (ZMod n)) AddCommGrpCat.{w})).Full :=
    sheafUnderlying_full J n
  exact (sheafCompose J (forget₂ (ModuleCat.{w} (ZMod n)) AddCommGrpCat.{w})).preimage
    (Preadditive.killedKernelLift n (sheafUnderlying_nsmul_id J n M) a ≫
      (annihilatorUnderlyingIso J n G).inv)

/-- Scalar forgetting, the original comparison and the original inclusion
recover the given arrow. -/
@[reassoc]
theorem annihilatorLift_underlying (M : Sheaf J (ModuleCat.{w} (ZMod n)))
    (G : Sheaf J AddCommGrpCat.{w})
    (a : (sheafCompose J (forget₂ (ModuleCat.{w} (ZMod n)) AddCommGrpCat.{w})).obj M ⟶ G) :
    (sheafCompose J (forget₂ (ModuleCat.{w} (ZMod n)) AddCommGrpCat.{w})).map
        (annihilatorLift J n M G a) ≫
      (annihilatorUnderlyingIso J n G).hom ≫ Sheaf.annihilatorι G n = a := by
  let : (sheafCompose J
      (forget₂ (ModuleCat.{w} (ZMod n)) AddCommGrpCat.{w})).Full :=
    sheafUnderlying_full J n
  dsimp only [annihilatorLift]
  rw [Functor.map_preimage]
  simp only [Category.assoc, Iso.inv_hom_id_assoc, Preadditive.killedKernelLift_ι]

/-- An original abelian monomorphism gives a genuine module monomorphism. -/
theorem mono_annihilatorLift (M : Sheaf J (ModuleCat.{w} (ZMod n)))
    (G : Sheaf J AddCommGrpCat.{w})
    (a : (sheafCompose J (forget₂ (ModuleCat.{w} (ZMod n)) AddCommGrpCat.{w})).obj M ⟶ G)
    [Mono a] : Mono (annihilatorLift J n M G a) := by
  apply (sheafCompose J
    (forget₂ (ModuleCat.{w} (ZMod n)) AddCommGrpCat.{w})).mono_of_mono_map
  exact mono_of_mono_fac (annihilatorLift_underlying J n M G a)

end CategoryTheory.TorsionZMod
