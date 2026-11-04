/-
Copyright (c) 2026 kangxyz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/

module

public import Aglib.AlgebraicGeometry.Group.CartierDuality.SpecUnits

/-!
# Naturality of the original unit map across coefficient bases

The Laurent coordinate of the same represented unit map is natural under
arbitrary ring maps. The relative bases may be different commutative rings.
No alternate multiplicative-group or unit representation is introduced.
-/

@[expose] public section

noncomputable section

open CategoryTheory AlgebraicGeometry Opposite

namespace AlgebraicGeometry.Scheme.Group.CartierDuality

universe u

/-- The original represented unit maps have natural Laurent coordinates under any ring map. -/
theorem specUnitMap_laurent_naturality {K L : Type u} [CommRing K] [CommRing L]
    (A : CommAlgCat.{u} K) (B : CommAlgCat.{u} L)
    (f : A →+* B) (u : Aˣ) :
    Spec.map (CommRingCat.ofHom f) ≫ (specUnitMap A u).left ≫
        CategoryTheory.Limits.prod.snd =
      (specUnitMap B (Units.map f.toMonoidHom u)).left ≫
        CategoryTheory.Limits.prod.snd := by
  have hA := specUnitMap_units A u
  have hB := specUnitMap_units B (Units.map f.toMonoidHom u)
  change MultiplicativeGroup.affineHomUnits (Spec (CommRingCat.of A))
      ((specUnitMap A u).left ≫ CategoryTheory.Limits.prod.snd) = _ at hA
  change MultiplicativeGroup.affineHomUnits (Spec (CommRingCat.of B))
      ((specUnitMap B (Units.map f.toMonoidHom u)).left ≫
        CategoryTheory.Limits.prod.snd) = _ at hB
  have hn := MultiplicativeGroup.affineHomUnits_comp
    (Spec.map (CommRingCat.ofHom f))
    ((specUnitMap A u).left ≫ CategoryTheory.Limits.prod.snd)
  have hL := hn.trans (congrArg
    (Units.map (Spec.map (CommRingCat.ofHom f)).appTop.hom.toMonoidHom) hA)
  have hunit :
      Units.map (Spec.map (CommRingCat.ofHom f)).appTop.hom.toMonoidHom
          (Units.map (Scheme.ΓSpecIso (CommRingCat.of A)).inv.hom.toMonoidHom u) =
        Units.map (Scheme.ΓSpecIso (CommRingCat.of B)).inv.hom.toMonoidHom
          (Units.map f.toMonoidHom u) := by
    apply Units.ext
    change (((Scheme.ΓSpecIso (CommRingCat.of A)).inv ≫
        (Spec.map (CommRingCat.ofHom f)).appTop).hom (u : A)) =
      ((CommRingCat.ofHom f ≫ (Scheme.ΓSpecIso (CommRingCat.of B)).inv).hom (u : A))
    exact congrArg
      (fun q : CommRingCat.of A ⟶ Γ(Spec (CommRingCat.of B), ⊤) => q.hom (u : A))
      (Scheme.ΓSpecIso_inv_naturality (CommRingCat.ofHom f)).symm
  exact (MultiplicativeGroup.affineHomUnits (Spec (CommRingCat.of B))).injective
    (hL.trans (hunit.trans hB.symm))

end AlgebraicGeometry.Scheme.Group.CartierDuality
