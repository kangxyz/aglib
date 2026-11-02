/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.Modules.Invertible.IsomorphismSheaf
public import Aglib.AlgebraicGeometry.Modules.Invertible.ScalarAutomorphisms

/-! # Inversion on the actual module-isomorphism sheaves

Inversion swaps the two original mutually inverse maps. Its naturality,
involution, unit and reversed-composition laws are laws of the whole sheaf
maps, before passage to any small-etale chart or torsor class.
-/

@[expose] public noncomputable section

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open AlgebraicGeometry CategoryTheory Opposite
open scoped MonoidalCategory

namespace AlgebraicGeometry.Scheme.Modules.Invertible.EtaleDescent

universe u
variable {X : Scheme.{u}} (L M N : lineBundles.obj (.mk (op X)))
  (h : EtaleLineBundleDescent.{u})

/-- Invert the actual local module isomorphism, without choosing another model. -/
def isoSheafInverse : isoSheaf L M h ≅ isoSheaf M L h where
  hom := ⟨{
    app U := TypeCat.ofHom fun p => ⟨(p.val.2, p.val.1), p.property.2, p.property.1⟩
    naturality {_ _} _ := rfl }⟩
  inv := ⟨{
    app U := TypeCat.ofHom fun p => ⟨(p.val.2, p.val.1), p.property.2, p.property.1⟩
    naturality {_ _} _ := rfl }⟩
  hom_inv_id := by ext U p; rfl
  inv_hom_id := by ext U p; rfl

/-- The native section equivalence identifies inversion with inverse isomorphisms. -/
@[simp] theorem isoSectionsEquiv_inverse (U : (Over X)ᵒᵖ)
    (p : (isoSheaf L M h).obj.obj U) :
    isoSectionsEquiv M L h U ((isoSheafInverse L M h).hom.hom.app U p) =
      (isoSectionsEquiv L M h U p).symm := rfl

/-- Inversion is involutive as a whole sheaf isomorphism. -/
@[simp] theorem isoSheafInverse_twice :
    isoSheafInverse L M h ≪≫ isoSheafInverse M L h = Iso.refl _ := by
  apply Iso.ext
  ext U p
  rfl

/-- The identity local isomorphisms form a section of the actual isomorphism sheaf. -/
def isoSheafIdentity : 𝟙_ (Sheaf (Scheme.etaleTopology.over X) (Type u)) ⟶
    isoSheaf L L h :=
  ⟨{
    app U := TypeCat.ofHom fun _ => ⟨(𝟙 _, 𝟙 _), by constructor <;> simp⟩
    naturality {U V} f := by
      ext p
      apply Subtype.ext
      exact Prod.ext (homRestriction_id L f).symm (homRestriction_id L f).symm }⟩

/-- Compose the two original local module isomorphisms as a whole sheaf map. -/
def isoSheafComposition : isoSheaf L M h ⊗ isoSheaf M N h ⟶ isoSheaf L N h :=
  ⟨{
    app U := TypeCat.ofHom fun p =>
      ⟨(p.1.val.1 ≫ p.2.val.1, p.2.val.2 ≫ p.1.val.2), by
        constructor
        · calc
            (p.1.val.1 ≫ p.2.val.1) ≫ (p.2.val.2 ≫ p.1.val.2) =
                p.1.val.1 ≫ (p.2.val.1 ≫ p.2.val.2) ≫ p.1.val.2 := by
                  simp only [Category.assoc]
            _ = 𝟙 _ := by rw [p.2.property.1, Category.id_comp, p.1.property.1]
        · calc
            (p.2.val.2 ≫ p.1.val.2) ≫ (p.1.val.1 ≫ p.2.val.1) =
                p.2.val.2 ≫ (p.1.val.2 ≫ p.1.val.1) ≫ p.2.val.1 := by
                  simp only [Category.assoc]
            _ = 𝟙 _ := by rw [p.1.property.2, Category.id_comp, p.2.property.2]⟩
    naturality {U V} f := by
      ext p
      apply Subtype.ext
      exact Prod.ext
        (homRestriction_comp L M N f p.1.val.1 p.2.val.1).symm
        (homRestriction_comp N M L f p.2.val.2 p.1.val.2).symm }⟩

/-- Inversion preserves the unit section. -/
@[simp] theorem isoSheafIdentity_inverse :
    isoSheafIdentity L h ≫ (isoSheafInverse L L h).hom = isoSheafIdentity L h := by
  ext U p
  rfl

/-- Inversion reverses composition as a whole sheaf map. -/
theorem isoSheafComposition_inverse :
    isoSheafComposition L M N h ≫ (isoSheafInverse L N h).hom =
      ((isoSheafInverse L M h).hom ⊗ₘ (isoSheafInverse M N h).hom) ≫
        (β_ (isoSheaf M L h) (isoSheaf N M h)).hom ≫
          isoSheafComposition N M L h := by
  ext U p
  rfl

/-- The identity section is a left unit for composition. -/
theorem isoSheafIdentity_composition :
    (isoSheafIdentity L h ⊗ₘ 𝟙 (isoSheaf L M h)) ≫ isoSheafComposition L L M h =
      (λ_ (isoSheaf L M h)).hom := by
  ext U p
  apply Subtype.ext
  exact Prod.ext (Category.id_comp _) (Category.comp_id _)

/-- The identity section is a right unit for composition. -/
theorem isoSheafComposition_identity :
    (𝟙 (isoSheaf L M h) ⊗ₘ isoSheafIdentity M h) ≫ isoSheafComposition L M M h =
      (ρ_ (isoSheaf L M h)).hom := by
  ext U p
  apply Subtype.ext
  exact Prod.ext (Category.comp_id _) (Category.id_comp _)

end AlgebraicGeometry.Scheme.Modules.Invertible.EtaleDescent

namespace AlgebraicGeometry.Scheme.Modules.Invertible.ScalarAutomorphisms

universe u
variable (X : Scheme.{u})

/-- Inversion changes positive scalar postcomposition into inverse scalar
postcomposition, on arbitrary module sheaves. -/
theorem inverse_scalarIso {M N : X.Modules} (φ : M ≅ N) (a : Γ(X, ⊤)ˣ) :
    (φ ≪≫ scalarIso X N a).symm = φ.symm ≪≫ scalarIso X M a⁻¹ := by
  apply Iso.ext
  exact scalarMap_naturality X (↑a⁻¹ : Γ(X, ⊤)) φ.inv

end AlgebraicGeometry.Scheme.Modules.Invertible.ScalarAutomorphisms
