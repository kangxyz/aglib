/-
Copyright (c) 2026 kangxyz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.EtaleCohomology.ArtinSchreier.Frobenius
public import Mathlib.FieldTheory.Finite.Basic

/-!
# Original prime-field constants in the additive etale structure sheaf

The canonical residue homomorphism defines the original map from the constant
`ZMod p` sheaf to actual additive sections. Its composite with the literal
Artin--Schreier endomorphism is zero. Only the equation `p = 0` in global
sections is required, including on empty schemes and empty test objects.
-/

@[expose] public noncomputable section

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open CategoryTheory Opposite

namespace AlgebraicGeometry.Scheme.EtaleCohomology

universe u

/-- The original prime-field additive coefficient group, in the standard universe. -/
def primeFieldCoefficient (p : ℕ) : AddCommGrpCat.{u + 1} :=
  AddCommGrpCat.of (ULift.{u + 1} (ZMod p))

/-- The actual constant prime-field sheaf. -/
def primeFieldSheaf (X : Scheme.{u}) (p : ℕ) : AbelianSheaf.{u, u + 1} X :=
  (constantSheaf (Scheme.smallEtaleTopology X) AddCommGrpCat.{u + 1}).obj
    (primeFieldCoefficient p)

/-- Original residue constants, with the native coefficient universe lifts. -/
def primeFieldSectionHom {R : Type u} [CommRing R] (p : ℕ) (hR : (p : R) = 0) :
    ULift.{u + 1} (ZMod p) →+ ULift.{u + 1} R :=
  CategoryTheory.Sheaf.ArtinSchreier.primeFieldSectionHom (T := R) p hR

/-- The original constant-presheaf map sends every residue to its literal scalar. -/
def primeFieldPresheafMap (X : Scheme.{u}) (p : ℕ) (hX : (p : Γ(X, ⊤)) = 0) :
    (Functor.const X.Etaleᵒᵖ).obj (primeFieldCoefficient p) ⟶
      additiveStructurePresheaf X :=
  CategoryTheory.Sheaf.ArtinSchreier.primeFieldPresheafMap (structurePresheaf X) p
    (primeCast_eq_zero_on_test X p hX)

/-- The canonical map from the actual constant prime-field sheaf to additive sections. -/
def primeFieldToStructure (X : Scheme.{u}) (p : ℕ) (hX : (p : Γ(X, ⊤)) = 0) :
    primeFieldSheaf X p ⟶ additiveStructureSheaf X :=
  ((sheafificationAdjunction (Scheme.smallEtaleTopology X) AddCommGrpCat.{u + 1}).homEquiv
    ((Functor.const X.Etaleᵒᵖ).obj (primeFieldCoefficient p))
    (additiveStructureSheaf X)).symm (primeFieldPresheafMap X p hX)

/-- On the original constant presheaf, the sheaf map is the original residue scalar map. -/
theorem toSheafify_primeFieldToStructure (X : Scheme.{u}) (p : ℕ)
    (hX : (p : Γ(X, ⊤)) = 0) :
    toSheafify (Scheme.smallEtaleTopology X)
        ((Functor.const X.Etaleᵒᵖ).obj (primeFieldCoefficient p)) ≫
      (primeFieldToStructure X p hX).hom = primeFieldPresheafMap X p hX := by
  exact ((sheafificationAdjunction (Scheme.smallEtaleTopology X)
    AddCommGrpCat.{u + 1}).homEquiv _ _).apply_symm_apply _

/-- Prime-field scalars lie in the kernel of the literal Artin--Schreier map. -/
theorem primeFieldToStructure_artinSchreierMap (X : Scheme.{u}) (p : ℕ) (hp : p.Prime)
    (hX : (p : Γ(X, ⊤)) = 0) :
    primeFieldToStructure X p hX ≫ artinSchreierMap X p hp hX = 0 :=
  CategoryTheory.Sheaf.ArtinSchreier.primeFieldToAdditive_artinSchreierMap
    (structurePresheaf X) (Scheme.smallEtaleTopology X) (additiveStructurePresheaf_isSheaf X)
    p hp (primeCast_eq_zero_on_test X p hX)

end AlgebraicGeometry.Scheme.EtaleCohomology
