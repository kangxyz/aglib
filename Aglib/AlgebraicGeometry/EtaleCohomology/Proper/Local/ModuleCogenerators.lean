/-
Copyright (c) 2026 kangxyz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.EtaleCohomology.Proper.Reduction.ZModRetract
public import Aglib.CategoryTheory.Sites.Torsion.Annihilator.Basic
public import Aglib.CategoryTheory.Sites.Torsion.ZMod.Full
public import Mathlib.CategoryTheory.Limits.Preserves.Shapes.Kernels

/-! # Genuine module cogenerators from original abelian embeddings

An original abelian embedding of an n-killed coefficient factors through the
native n-annihilator of its target. This yields a monomorphism of the original
genuine module sheaves. For a constant direct-image target, its annihilator is
the same original direct image of the constant finite-value kernel. No scalar
structure on the original target and no injectivity after forgetting is assumed.
-/

@[expose] public noncomputable section

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry.Scheme.EtaleCohomology.Proper

section TypedKernels

variable {C D : Type*} [Category* C] [Category* D]
  [Preadditive C] [Preadditive D] [HasKernels C] [HasKernels D]

/-- An additive left exact functor transports the actual scalar kernel
through its original preserved-kernel comparison and scalar normalization. -/
def nsmulKernelIso (F : C ⥤ D) [F.Additive] [PreservesFiniteLimits F]
    (A : C) (n : ℕ) : F.obj (kernel (n • 𝟙 A)) ≅ kernel (n • 𝟙 (F.obj A)) :=
  PreservesKernel.iso F (n • 𝟙 A) ≪≫ kernelIsoOfEq (by simp)

private theorem nsmulKernelIso_inv_ι
    (F : C ⥤ D) [F.Additive] [PreservesFiniteLimits F] (A : C) (n : ℕ) :
    (nsmulKernelIso F A n).inv ≫ F.map (kernel.ι (n • 𝟙 A)) =
      kernel.ι (n • 𝟙 (F.obj A)) := by
  simp only [nsmulKernelIso, Iso.trans_inv, Category.assoc,
    PreservesKernel.iso_inv_ι, kernelIsoOfEq_inv_comp_ι]

/-- An arrow from an actually n-killed object factors through the original
scalar kernel of its target by the native kernel universal property. -/
def killedKernelLift {A B : C} (n : ℕ) (hA : n • 𝟙 A = 0) (a : A ⟶ B) :
    A ⟶ kernel (n • 𝟙 B) :=
  kernel.lift (n • 𝟙 B) a (by
    calc
      a ≫ (n • 𝟙 B) = n • a := by simp
      _ = (n • 𝟙 A) ≫ a := by simp
      _ = 0 := by rw [hA, zero_comp])

private theorem killedKernelLift_ι {A B : C} (n : ℕ) (hA : n • 𝟙 A = 0) (a : A ⟶ B) :
    killedKernelLift n hA a ≫ kernel.ι (n • 𝟙 B) = a :=
  kernel.lift_ι _ _ _

end TypedKernels

universe u

attribute [local instance] hasSheafifyLarge TorsionZMod.hasSheafifyStandard

/-- The original standard-value constant-sheaf functor is left exact. -/
theorem constantSheaf_preservesFiniteLimits (Y : Scheme.{u}) :
    PreservesFiniteLimits (constantSheaf Y.smallEtaleTopology AddCommGrpCat.{u + 1}) := by
  change PreservesFiniteLimits
    (Functor.const Y.Etaleᵒᵖ ⋙ presheafToSheaf Y.smallEtaleTopology AddCommGrpCat.{u + 1})
  infer_instance

variable (X : Scheme.{u}) (n : ℕ)

/-- The genuine module structure on the actual native annihilator of the
original target coefficient. The modulus may be zero or one. -/
def zmodAnnihilator (G : AbelianSheaf.{u, u + 1} X) : Reduction.ZModSheaf X n :=
  TorsionZMod.sheaf X.smallEtaleTopology n (Sheaf.annihilator G n)
    (Sheaf.nsmul_id_annihilator G n)

/-- The original underlying coefficient of the constructed module target is
the actual native annihilator, through the original scalar-conversion iso. -/
def zmodAnnihilatorUnderlyingIso (G : AbelianSheaf.{u, u + 1} X) :
    (Reduction.zmodUnderlying X n).obj (zmodAnnihilator X n G) ≅
      Sheaf.annihilator G n :=
  TorsionZMod.sheafUnderlyingIso X.smallEtaleTopology n (Sheaf.annihilator G n)
    (Sheaf.nsmul_id_annihilator G n)

/-- Lift an original underlying abelian arrow to the genuine module
annihilator target, preserving the original source module and its scalar action. -/
def zmodAnnihilatorLift (M : Reduction.ZModSheaf X n) (G : AbelianSheaf.{u, u + 1} X)
    (a : (Reduction.zmodUnderlying X n).obj M ⟶ G) : M ⟶ zmodAnnihilator X n G := by
  let : (Reduction.zmodUnderlying X n).Full :=
    TorsionZMod.sheafUnderlying_full.{u + 1, u, u + 1} X.smallEtaleTopology n
  exact (Reduction.zmodUnderlying X n).preimage
    (killedKernelLift n (Reduction.zmodUnderlying_nsmul_id X n M) a ≫
      (zmodAnnihilatorUnderlyingIso X n G).inv)

/-- The genuine module lift recovers the literal original abelian arrow after
the original scalar comparison and annihilator inclusion. -/
@[reassoc]
theorem zmodAnnihilatorLift_underlying
    (M : Reduction.ZModSheaf X n) (G : AbelianSheaf.{u, u + 1} X)
    (a : (Reduction.zmodUnderlying X n).obj M ⟶ G) :
    (Reduction.zmodUnderlying X n).map (zmodAnnihilatorLift X n M G a) ≫
        (zmodAnnihilatorUnderlyingIso X n G).hom ≫ Sheaf.annihilatorι G n = a := by
  let : (Reduction.zmodUnderlying X n).Full :=
    TorsionZMod.sheafUnderlying_full.{u + 1, u, u + 1} X.smallEtaleTopology n
  dsimp only [zmodAnnihilatorLift]
  rw [Functor.map_preimage]
  simp only [Category.assoc, Iso.inv_hom_id_assoc, killedKernelLift_ι]

/-- An actual original abelian monomorphism gives an actual genuine module
monomorphism, without changing the source module or its original arrow. -/
theorem mono_zmodAnnihilatorLift
    (M : Reduction.ZModSheaf X n) (G : AbelianSheaf.{u, u + 1} X)
    (a : (Reduction.zmodUnderlying X n).obj M ⟶ G) [Mono a] :
    Mono (zmodAnnihilatorLift X n M G a) := by
  apply (Reduction.zmodUnderlying X n).mono_of_mono_map
  exact mono_of_mono_fac (zmodAnnihilatorLift_underlying X n M G a)

variable {X}

/-- The actual n-annihilator of a constant direct image is the same direct
image of the actual constant value kernel. This holds for every scheme map. -/
def constantDirectImageAnnihilatorIso {Y : Scheme.{u}} (f : Y ⟶ X)
    (A : AddCommGrpCat.{u + 1}) :
    Sheaf.annihilator ((directImage f).obj
      ((constantSheaf Y.smallEtaleTopology AddCommGrpCat.{u + 1}).obj A)) n ≅
      (directImage f).obj ((constantSheaf Y.smallEtaleTopology AddCommGrpCat.{u + 1}).obj
        (kernel (n • 𝟙 A))) := by
  let : PreservesFiniteLimits (constantSheaf Y.smallEtaleTopology AddCommGrpCat.{u + 1}) :=
    constantSheaf_preservesFiniteLimits Y
  let : PreservesFiniteLimits
      (constantSheaf Y.smallEtaleTopology AddCommGrpCat.{u + 1} ⋙ directImage f) :=
    Limits.comp_preservesFiniteLimits _ _
  exact (nsmulKernelIso
    (constantSheaf Y.smallEtaleTopology AddCommGrpCat.{u + 1} ⋙ directImage f) A n).symm

/-- The comparison retains the original kernel inclusion on finite values
and its original constant-sheaf/direct-image map. -/
@[reassoc]
theorem constantDirectImageAnnihilatorIso_hom_ι {Y : Scheme.{u}} (f : Y ⟶ X)
    (A : AddCommGrpCat.{u + 1}) :
    (constantDirectImageAnnihilatorIso n f A).hom ≫
        (directImage f).map
          ((constantSheaf Y.smallEtaleTopology AddCommGrpCat.{u + 1}).map
            (kernel.ι (n • 𝟙 A))) =
      Sheaf.annihilatorι ((directImage f).obj
        ((constantSheaf Y.smallEtaleTopology AddCommGrpCat.{u + 1}).obj A)) n := by
  let : PreservesFiniteLimits (constantSheaf Y.smallEtaleTopology AddCommGrpCat.{u + 1}) :=
    constantSheaf_preservesFiniteLimits Y
  let : PreservesFiniteLimits
      (constantSheaf Y.smallEtaleTopology AddCommGrpCat.{u + 1} ⋙ directImage f) :=
    Limits.comp_preservesFiniteLimits _ _
  exact nsmulKernelIso_inv_ι
    (constantSheaf Y.smallEtaleTopology AddCommGrpCat.{u + 1} ⋙ directImage f) A n

/-- The actual kernel value remains finite whenever the original constant
value is finite. No positivity or invertibility condition is needed. -/
theorem finite_nsmulKernelValue (A : AddCommGrpCat.{u + 1}) [Finite A] :
    Finite (kernel (n • 𝟙 A) : AddCommGrpCat.{u + 1}) :=
  Finite.of_injective (kernel.ι (n • 𝟙 A))
    ((AddCommGrpCat.mono_iff_injective _).mp inferInstance)

end AlgebraicGeometry.Scheme.EtaleCohomology.Proper
