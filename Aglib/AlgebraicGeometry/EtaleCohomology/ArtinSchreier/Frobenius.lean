/-
Copyright (c) 2026 kangxyz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.Algebra.CharP.Frobenius
public import Aglib.AlgebraicGeometry.EtaleCohomology.StructureSheaf.Basic

/-!
# Frobenius and Artin--Schreier on actual additive etale sections

For a prime annihilating the original ring of global sections, the literal
prime-power maps define an endomorphism of the actual additive structure
sheaf. Its difference from the identity is the original Artin--Schreier map.
The hypothesis remains valid on empty etale test objects.
-/

@[expose] public noncomputable section

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open CategoryTheory Opposite

namespace AlgebraicGeometry.Scheme.EtaleCohomology

universe u

/-- The prime-cast equation restricts to every actual etale test scheme. -/
theorem primeCast_eq_zero_on_test (X : Scheme.{u}) (p : ℕ)
    (hX : (p : Γ(X, ⊤)) = 0) (U : X.Etaleᵒᵖ) :
    (p : (structurePresheaf X).obj U) = 0 := by
  change (p : Γ(((Scheme.Etale.forget X).obj U.unop).left, ⊤)) = 0
  have h := congrArg (((Scheme.Etale.forget X).obj U.unop).hom.appTop.hom) hX
  simpa only [map_natCast, map_zero] using h

/-- Frobenius on the actual additive etale structure sheaf. -/
def structureFrobenius (X : Scheme.{u}) (p : ℕ) (hp : p.Prime)
    (hX : (p : Γ(X, ⊤)) = 0) : additiveStructureSheaf X ⟶ additiveStructureSheaf X where
  hom := {
    app U := AddCommGrpCat.uliftFunctor.map (AddCommGrpCat.ofHom
      (RingHom.frobeniusOfPrimeCastEqZero p hp
        (primeCast_eq_zero_on_test X p hX U)).toAddMonoidHom)
    naturality {U V} f := by
      ext x
      apply ULift.ext
      let a : (structurePresheaf X).obj U := x.down
      change ((structurePresheaf X).map f).hom a ^ p =
        ((structurePresheaf X).map f).hom (a ^ p)
      exact (map_pow ((structurePresheaf X).map f).hom a p).symm }

/-- The original map `a ↦ a^p - a` on the actual additive structure sheaf. -/
def artinSchreierMap (X : Scheme.{u}) (p : ℕ) (hp : p.Prime)
    (hX : (p : Γ(X, ⊤)) = 0) : additiveStructureSheaf X ⟶ additiveStructureSheaf X :=
  structureFrobenius X p hp hX - 𝟙 _

/-- Its component is the literal power-minus-identity map on original sections. -/
theorem artinSchreierMap_apply (X : Scheme.{u}) (p : ℕ) (hp : p.Prime)
    (hX : (p : Γ(X, ⊤)) = 0) (U : X.Etaleᵒᵖ)
    (x : ULift.{u + 1} ((structurePresheaf X).obj U)) :
    ((artinSchreierMap X p hp hX).hom.app U x).down = x.down ^ p - x.down := rfl

end AlgebraicGeometry.Scheme.EtaleCohomology
