/-
Copyright (c) 2026 kangxyz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.EtaleCohomology.Proper.Reduction.ZModRetract
public import Aglib.CategoryTheory.Sites.Torsion.Annihilator.ZMod

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

/-- The original scalar-kernel comparison, supplied by the generic kernel API. -/
def nsmulKernelIso (F : C ⥤ D) [F.Additive] [PreservesFiniteLimits F]
    (A : C) (n : ℕ) : F.obj (kernel (n • 𝟙 A)) ≅ kernel (n • 𝟙 (F.obj A)) :=
  Preadditive.nsmulKernelIso F A n

/-- The original factorization through the actual scalar kernel of the target. -/
def killedKernelLift {A B : C} (n : ℕ) (hA : n • 𝟙 A = 0) (a : A ⟶ B) :
    A ⟶ kernel (n • 𝟙 B) :=
  Preadditive.killedKernelLift n hA a

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
  TorsionZMod.annihilator X.smallEtaleTopology n G

/-- The original underlying coefficient of the constructed module target is
the actual native annihilator, through the original scalar-conversion iso. -/
def zmodAnnihilatorUnderlyingIso (G : AbelianSheaf.{u, u + 1} X) :
    (Reduction.zmodUnderlying X n).obj (zmodAnnihilator X n G) ≅
      Sheaf.annihilator G n :=
  TorsionZMod.annihilatorUnderlyingIso X.smallEtaleTopology n G

/-- Lift an original underlying abelian arrow to the genuine module
annihilator target, preserving the original source module and its scalar action. -/
def zmodAnnihilatorLift (M : Reduction.ZModSheaf X n) (G : AbelianSheaf.{u, u + 1} X)
    (a : (Reduction.zmodUnderlying X n).obj M ⟶ G) : M ⟶ zmodAnnihilator X n G :=
  TorsionZMod.annihilatorLift X.smallEtaleTopology n M G a

/-- The genuine module lift recovers the literal original abelian arrow after
the original scalar comparison and annihilator inclusion. -/
@[reassoc]
theorem zmodAnnihilatorLift_underlying
    (M : Reduction.ZModSheaf X n) (G : AbelianSheaf.{u, u + 1} X)
    (a : (Reduction.zmodUnderlying X n).obj M ⟶ G) :
    (Reduction.zmodUnderlying X n).map (zmodAnnihilatorLift X n M G a) ≫
        (zmodAnnihilatorUnderlyingIso X n G).hom ≫ Sheaf.annihilatorι G n = a :=
  TorsionZMod.annihilatorLift_underlying X.smallEtaleTopology n M G a

/-- An actual original abelian monomorphism gives an actual genuine module
monomorphism, without changing the source module or its original arrow. -/
theorem mono_zmodAnnihilatorLift
    (M : Reduction.ZModSheaf X n) (G : AbelianSheaf.{u, u + 1} X)
    (a : (Reduction.zmodUnderlying X n).obj M ⟶ G) [Mono a] :
    Mono (zmodAnnihilatorLift X n M G a) :=
  TorsionZMod.mono_annihilatorLift X.smallEtaleTopology n M G a

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
  exact Preadditive.nsmulKernelIso_inv_ι
    (constantSheaf Y.smallEtaleTopology AddCommGrpCat.{u + 1} ⋙ directImage f) A n

/-- The actual kernel value remains finite whenever the original constant
value is finite. No positivity or invertibility condition is needed. -/
theorem finite_nsmulKernelValue (A : AddCommGrpCat.{u + 1}) [Finite A] :
    Finite (kernel (n • 𝟙 A) : AddCommGrpCat.{u + 1}) :=
  Finite.of_injective (kernel.ι (n • 𝟙 A))
    ((AddCommGrpCat.mono_iff_injective _).mp inferInstance)

end AlgebraicGeometry.Scheme.EtaleCohomology.Proper
