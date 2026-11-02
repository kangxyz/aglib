/-
Copyright (c) 2026 kangxyz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.EtaleCohomology.Proper.Local.ModuleCogenerators

/-! # Original annihilators of finite products

The native annihilator of the original abelian product is the product of its
actual coordinate annihilators. Combined with the genuine-module lift, this
converts a given finite constant product embedding into a genuine module
embedding with the required original finite constant kernel targets. Every
original product projection and kernel inclusion is retained.
-/

@[expose] public noncomputable section

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry.Scheme.EtaleCohomology.Proper

universe u

attribute [local instance] hasSheafifyLarge

variable (X : Scheme.{u}) (n : ℕ) {k : ℕ}

/-- The actual finite family of original coordinate annihilators. -/
def annihilatorProductFamily (G : Fin k → AbelianSheaf.{u, u + 1} X) :
    Fin k → AbelianSheaf.{u, u + 1} X :=
  Preadditive.nsmulKernelProductFamily n G

/-- The original product of the native kernel inclusions. -/
def annihilatorProductInclusion (G : Fin k → AbelianSheaf.{u, u + 1} X) :
    (∏ᶜ annihilatorProductFamily X n G) ⟶ ∏ᶜ G :=
  Preadditive.nsmulKernelProductInclusion n G

instance annihilatorProductInclusion_mono (G : Fin k → AbelianSheaf.{u, u + 1} X) :
    Mono (annihilatorProductInclusion X n G) :=
  Preadditive.nsmulKernelProductInclusion_mono n G

/-- The original coefficient maps induced by each product projection. -/
def annihilatorProductForward (G : Fin k → AbelianSheaf.{u, u + 1} X) :
    Sheaf.annihilator (∏ᶜ G) n ⟶ ∏ᶜ annihilatorProductFamily X n G :=
  Preadditive.nsmulKernelProductForward n G

/-- Each forward projection is the original annihilator coefficient map. -/
@[reassoc]
theorem annihilatorProductForward_π
    (G : Fin k → AbelianSheaf.{u, u + 1} X) (i : Fin k) :
    annihilatorProductForward X n G ≫ Pi.π (annihilatorProductFamily X n G) i =
      Sheaf.annihilatorCoefficientMap (Pi.π G i) n := by
  apply (cancel_mono (Sheaf.annihilatorι (G i) n)).mp
  rw [Category.assoc, Sheaf.annihilatorCoefficientMap_ι]
  exact Preadditive.nsmulKernelProductForward_π_ι n G i

/-- The original product of coordinate annihilators is itself killed by n. -/
theorem annihilatorProduct_nsmul_id
    (G : Fin k → AbelianSheaf.{u, u + 1} X) :
    n • 𝟙 (∏ᶜ annihilatorProductFamily X n G) = 0 :=
  Preadditive.nsmulKernelProduct_nsmul_id n G

/-- The native kernel lift of the actual product of kernel inclusions. -/
def annihilatorProductBackward (G : Fin k → AbelianSheaf.{u, u + 1} X) :
    (∏ᶜ annihilatorProductFamily X n G) ⟶ Sheaf.annihilator (∏ᶜ G) n :=
  Preadditive.nsmulKernelProductBackward n G

/-- The forward map retains the original product projections and kernel inclusion. -/
@[reassoc]
theorem annihilatorProductForward_inclusion
    (G : Fin k → AbelianSheaf.{u, u + 1} X) :
    annihilatorProductForward X n G ≫ annihilatorProductInclusion X n G =
      Sheaf.annihilatorι (∏ᶜ G) n :=
  Preadditive.nsmulKernelProductForward_inclusion n G

/-- The backward map retains the literal product of original kernel inclusions. -/
@[reassoc]
theorem annihilatorProductBackward_inclusion
    (G : Fin k → AbelianSheaf.{u, u + 1} X) :
    annihilatorProductBackward X n G ≫ Sheaf.annihilatorι (∏ᶜ G) n =
      annihilatorProductInclusion X n G :=
  Preadditive.nsmulKernelProductBackward_inclusion n G

/-- The actual original annihilator of a finite product is the product of the
actual coordinate annihilators, through the displayed original maps. -/
def annihilatorProductIso (G : Fin k → AbelianSheaf.{u, u + 1} X) :
    Sheaf.annihilator (∏ᶜ G) n ≅ ∏ᶜ annihilatorProductFamily X n G :=
  Preadditive.nsmulKernelProductIso n G

variable {X}

/-- A finite product of original constant direct images has annihilator the
same product with the original finite-value kernels. This supplies the target
comparison for the already proved genuine-module annihilator embedding. -/
def constantDirectImageProductAnnihilatorIso
    (Y : Fin k → Scheme.{u}) (f : ∀ i, Y i ⟶ X) (A : Fin k → AddCommGrpCat.{u + 1}) :
    Sheaf.annihilator
        (∏ᶜ fun i => (directImage (f i)).obj
          ((constantSheaf (Y i).smallEtaleTopology AddCommGrpCat.{u + 1}).obj (A i))) n ≅
      ∏ᶜ fun i => (directImage (f i)).obj
        ((constantSheaf (Y i).smallEtaleTopology AddCommGrpCat.{u + 1}).obj
          (kernel (n • 𝟙 (A i)))) :=
  annihilatorProductIso X n _ ≪≫
    Pi.mapIso (fun i => constantDirectImageAnnihilatorIso n (f i) (A i))

end AlgebraicGeometry.Scheme.EtaleCohomology.Proper
