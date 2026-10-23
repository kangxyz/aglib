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
    Fin k → AbelianSheaf.{u, u + 1} X := fun i => Sheaf.annihilator (G i) n

/-- The original product of the native kernel inclusions. -/
def annihilatorProductInclusion (G : Fin k → AbelianSheaf.{u, u + 1} X) :
    (∏ᶜ annihilatorProductFamily X n G) ⟶ ∏ᶜ G :=
  CategoryTheory.Limits.Pi.map fun i => Sheaf.annihilatorι (G i) n

instance annihilatorProductInclusion_mono (G : Fin k → AbelianSheaf.{u, u + 1} X) :
    Mono (annihilatorProductInclusion X n G) := by
  dsimp only [annihilatorProductInclusion]
  infer_instance

/-- The original coefficient maps induced by each product projection. -/
def annihilatorProductForward (G : Fin k → AbelianSheaf.{u, u + 1} X) :
    Sheaf.annihilator (∏ᶜ G) n ⟶ ∏ᶜ annihilatorProductFamily X n G :=
  Pi.lift fun i => Sheaf.annihilatorCoefficientMap (Pi.π G i) n

/-- The original product of coordinate annihilators is itself killed by n. -/
theorem annihilatorProduct_nsmul_id
    (G : Fin k → AbelianSheaf.{u, u + 1} X) :
    n • 𝟙 (∏ᶜ annihilatorProductFamily X n G) = 0 := by
  apply Pi.hom_ext
  intro i
  have hi : n • 𝟙 (annihilatorProductFamily X n G i) = 0 :=
    Sheaf.nsmul_id_annihilator (G i) n
  calc
    _ = Pi.π (annihilatorProductFamily X n G) i ≫
        (n • 𝟙 (annihilatorProductFamily X n G i)) := by
      simp only [Preadditive.nsmul_comp, Category.id_comp,
        Preadditive.comp_nsmul, Category.comp_id]
    _ = 0 := by rw [hi, comp_zero]
    _ = _ := by rw [zero_comp]

/-- The native kernel lift of the actual product of kernel inclusions. -/
def annihilatorProductBackward (G : Fin k → AbelianSheaf.{u, u + 1} X) :
    (∏ᶜ annihilatorProductFamily X n G) ⟶ Sheaf.annihilator (∏ᶜ G) n :=
  killedKernelLift n (annihilatorProduct_nsmul_id X n G) (annihilatorProductInclusion X n G)

/-- The forward map retains the original product projections and kernel inclusion. -/
@[reassoc]
theorem annihilatorProductForward_inclusion
    (G : Fin k → AbelianSheaf.{u, u + 1} X) :
    annihilatorProductForward X n G ≫ annihilatorProductInclusion X n G =
      Sheaf.annihilatorι (∏ᶜ G) n := by
  apply Pi.hom_ext
  intro i
  rw [Category.assoc, annihilatorProductInclusion, Pi.map_π, ← Category.assoc,
    annihilatorProductForward, Pi.lift_comp_π]
  exact Sheaf.annihilatorCoefficientMap_ι (Pi.π G i) n

/-- The backward map retains the literal product of original kernel inclusions. -/
@[reassoc]
theorem annihilatorProductBackward_inclusion
    (G : Fin k → AbelianSheaf.{u, u + 1} X) :
    annihilatorProductBackward X n G ≫ Sheaf.annihilatorι (∏ᶜ G) n =
      annihilatorProductInclusion X n G := by
  change killedKernelLift n _ _ ≫ kernel.ι (n • 𝟙 (∏ᶜ G)) = _
  exact kernel.lift_ι _ _ _

/-- The actual original annihilator of a finite product is the product of the
actual coordinate annihilators, through the displayed original maps. -/
def annihilatorProductIso (G : Fin k → AbelianSheaf.{u, u + 1} X) :
    Sheaf.annihilator (∏ᶜ G) n ≅ ∏ᶜ annihilatorProductFamily X n G where
  hom := annihilatorProductForward X n G
  inv := annihilatorProductBackward X n G
  hom_inv_id := by
    apply (cancel_mono (Sheaf.annihilatorι (∏ᶜ G) n)).mp
    rw [Category.assoc, annihilatorProductBackward_inclusion,
      annihilatorProductForward_inclusion, Category.id_comp]
  inv_hom_id := by
    apply (cancel_mono (annihilatorProductInclusion X n G)).mp
    rw [Category.assoc, annihilatorProductForward_inclusion,
      annihilatorProductBackward_inclusion, Category.id_comp]

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
