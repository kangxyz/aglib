/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Mathlib.Algebra.Homology.DerivedCategory.KInjective
public import Mathlib.CategoryTheory.HomCongr


/-!
Source: `Quillen/Algebra/Homology/KInjectiveHom.lean` at frozen dirty Quillen
`6db56ddd3fdb898ef5de29d5fe51a0c61f9ba116`.
Source SHA-256: `21da1f4c7369e5a7798fe7d0ff21b1a3e0bedea933ef1ac6c2b7701bce5b44fc`.

# Original homotopy-to-derived Hom equivalence with K-injective target

The actual quotient-factor isomorphisms normalize the genuine homotopy-to-derived
map at original chain-complex endpoints. K-injectivity of the target proves this
exact map bijective and additive. Both directions retain the original chain-map
image. Object, morphism, and derived-category model universes are independent.
-/
@[expose] public section

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
universe u v w
open CategoryTheory CategoryTheory.Limits
namespace CochainComplex
variable {C : Type u} [Category.{v} C] [Abelian C] [HasDerivedCategory.{w} C]

/-- The original homotopy localization map with actual chain-derived endpoints. -/
def homotopyToDerivedHom (K L : CochainComplex C ℤ)
    (φ : (HomotopyCategory.quotient C (.up ℤ)).obj K ⟶
      (HomotopyCategory.quotient C (.up ℤ)).obj L) :
    DerivedCategory.Q.obj K ⟶ DerivedCategory.Q.obj L :=
  (DerivedCategory.quotientCompQhIso C).inv.app K ≫ DerivedCategory.Qh.map φ ≫
    (DerivedCategory.quotientCompQhIso C).hom.app L

/-- K-injectivity proves bijectivity of this exact original map. -/
lemma homotopyToDerivedHom_bijective (K L : CochainComplex C ℤ) [L.IsKInjective] :
    Function.Bijective (homotopyToDerivedHom K L) :=
  (Iso.homCongr ((DerivedCategory.quotientCompQhIso C).app K)
    ((DerivedCategory.quotientCompQhIso C).app L)).bijective.comp
      (_root_.CochainComplex.IsKInjective.Qh_map_bijective _ L)

/-- The original homotopy-to-derived Hom map is an additive equivalence at a K-injective target. -/
def homotopyDerivedHomEquiv (K L : CochainComplex C ℤ) [L.IsKInjective] :
    ((HomotopyCategory.quotient C (.up ℤ)).obj K ⟶
      (HomotopyCategory.quotient C (.up ℤ)).obj L) ≃+
    (DerivedCategory.Q.obj K ⟶ DerivedCategory.Q.obj L) :=
  { Equiv.ofBijective (homotopyToDerivedHom K L) (homotopyToDerivedHom_bijective K L) with
    map_add' f g := by
      simp [homotopyToDerivedHom, Preadditive.comp_add, Preadditive.add_comp] }

/-- Chain representatives are sent to their actual original derived image. -/
@[simp]
lemma homotopyDerivedHomEquiv_map (K L : CochainComplex C ℤ) [L.IsKInjective] (f : K ⟶ L) :
    homotopyDerivedHomEquiv K L ((HomotopyCategory.quotient C (.up ℤ)).map f) =
      DerivedCategory.Q.map f :=
  NatIso.naturality_1 (DerivedCategory.quotientCompQhIso C) f

/-- The inverse equivalence recovers the actual homotopy class of every chain representative. -/
@[simp]
lemma homotopyDerivedHomEquiv_symm_map (K L : CochainComplex C ℤ) [L.IsKInjective] (f : K ⟶ L) :
    (homotopyDerivedHomEquiv K L).symm (DerivedCategory.Q.map f) =
      (HomotopyCategory.quotient C (.up ℤ)).map f := by
  apply (homotopyDerivedHomEquiv K L).injective
  rw [AddEquiv.apply_symm_apply, homotopyDerivedHomEquiv_map]

end CochainComplex
