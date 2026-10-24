/-
Copyright (c) 2026 kangxyz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.Algebra.Homology.DerivedCategory.KInjective.Hom
public import Aglib.Algebra.Homology.HomotopyCategory.Adjunction
public import Mathlib.Algebra.Homology.DerivedCategory.KProjective
public import Mathlib.CategoryTheory.Adjunction.Additive

/-!
# Derived Hom from a K-projective source to a K-injective target

For an additive adjunction `F ⊣ G`, a K-projective complex `P` and a
K-injective complex `I`, the original chain adjunction induces the additive
comparison between `Hom(F(P), I)` and `Hom(P, G(I))` in the derived categories.
Neither `F(P)` nor `G(I)` needs an additional replacement property, and `F`
need not be exact. Both directions preserve the original chain adjoints.

The current consumer is the finite-source residue-field comparison for a
proper birational normal surface.
-/

@[expose] public noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true

open CategoryTheory CategoryTheory.Limits

universe u v w u' v' w'

namespace CochainComplex

variable {C : Type u} [Category.{v} C] [Abelian C] [HasDerivedCategory.{w} C]
  (P L : CochainComplex C ℤ) [P.IsKProjective]

/-- Localization is bijective on the original Hom group from a K-projective complex. -/
theorem homotopyToDerivedHom_bijective_of_isKProjective :
    Function.Bijective (homotopyToDerivedHom P L) :=
  (Iso.homCongr ((DerivedCategory.quotientCompQhIso C).app P)
    ((DerivedCategory.quotientCompQhIso C).app L)).bijective.comp
      (IsKProjective.Qh_map_bijective P
        ((HomotopyCategory.quotient C (.up ℤ)).obj L))

/-- The original localization Hom map as an additive equivalence. -/
def homotopyDerivedHomEquivOfKProjective :
    ((HomotopyCategory.quotient C (.up ℤ)).obj P ⟶
      (HomotopyCategory.quotient C (.up ℤ)).obj L) ≃+
    (DerivedCategory.Q.obj P ⟶ DerivedCategory.Q.obj L) :=
  { Equiv.ofBijective (homotopyToDerivedHom P L)
      (homotopyToDerivedHom_bijective_of_isKProjective P L) with
    map_add' f g := by
      simp [homotopyToDerivedHom, Preadditive.comp_add, Preadditive.add_comp] }

/-- Chain representatives retain their literal image under derived localization. -/
@[simp]
theorem homotopyDerivedHomEquivOfKProjective_map (f : P ⟶ L) :
    homotopyDerivedHomEquivOfKProjective P L
      ((HomotopyCategory.quotient C (.up ℤ)).map f) = DerivedCategory.Q.map f :=
  NatIso.naturality_1 (DerivedCategory.quotientCompQhIso C) f

/-- The inverse recovers the original homotopy class of a chain representative. -/
@[simp]
theorem homotopyDerivedHomEquivOfKProjective_symm_map (f : P ⟶ L) :
    (homotopyDerivedHomEquivOfKProjective P L).symm (DerivedCategory.Q.map f) =
      (HomotopyCategory.quotient C (.up ℤ)).map f := by
  apply (homotopyDerivedHomEquivOfKProjective P L).injective
  rw [AddEquiv.apply_symm_apply, homotopyDerivedHomEquivOfKProjective_map]

end CochainComplex

namespace CategoryTheory.Adjunction

variable {C : Type u} [Category.{v} C] [Abelian C] [HasDerivedCategory.{w} C]
  {D : Type u'} [Category.{v'} D] [Abelian D] [HasDerivedCategory.{w'} D]
  {F : C ⥤ D} {G : D ⥤ C} (adj : F ⊣ G) [F.Additive] [G.Additive]
  (P : CochainComplex C ℤ) (I : CochainComplex D ℤ)
  [P.IsKProjective] [I.IsKInjective]

/-- The original chain adjunction computes derived Hom using the two different
replacement conditions on the original endpoints. -/
def cochainDerivedHomEquivOfMixed :
    (DerivedCategory.Q.obj ((F.mapHomologicalComplex (.up ℤ)).obj P) ⟶
      DerivedCategory.Q.obj I) ≃+
    (DerivedCategory.Q.obj P ⟶
      DerivedCategory.Q.obj ((G.mapHomologicalComplex (.up ℤ)).obj I)) :=
  ((CochainComplex.homotopyDerivedHomEquiv
    ((F.mapHomologicalComplex (.up ℤ)).obj P) I).symm.trans
      (adj.mapCochainHomotopyCategory.homAddEquiv
        ((HomotopyCategory.quotient C (.up ℤ)).obj P)
        ((HomotopyCategory.quotient D (.up ℤ)).obj I))).trans
    (CochainComplex.homotopyDerivedHomEquivOfKProjective P
      ((G.mapHomologicalComplex (.up ℤ)).obj I))

/-- The comparison sends an original chain map to its original chain adjoint. -/
@[simp]
theorem cochainDerivedHomEquivOfMixed_map
    (f : (F.mapHomologicalComplex (.up ℤ)).obj P ⟶ I) :
    cochainDerivedHomEquivOfMixed adj P I (DerivedCategory.Q.map f) =
      DerivedCategory.Q.map ((adj.mapHomologicalComplex (.up ℤ)).homEquiv P I f) := by
  change CochainComplex.homotopyDerivedHomEquivOfKProjective P _
    (adj.cochainHomotopyHomEquiv P I
      ((CochainComplex.homotopyDerivedHomEquiv _ I).symm
        (DerivedCategory.Q.map f))) = _
  rw [CochainComplex.homotopyDerivedHomEquiv_symm_map,
    cochainHomotopyHomEquiv_map, CochainComplex.homotopyDerivedHomEquivOfKProjective_map]

/-- The inverse comparison retains the inverse original chain adjunction. -/
@[simp]
theorem cochainDerivedHomEquivOfMixed_symm_map
    (g : P ⟶ (G.mapHomologicalComplex (.up ℤ)).obj I) :
    (cochainDerivedHomEquivOfMixed adj P I).symm (DerivedCategory.Q.map g) =
      DerivedCategory.Q.map (((adj.mapHomologicalComplex (.up ℤ)).homEquiv P I).symm g) := by
  apply (cochainDerivedHomEquivOfMixed adj P I).injective
  rw [AddEquiv.apply_symm_apply, cochainDerivedHomEquivOfMixed_map, Equiv.apply_symm_apply]

end CategoryTheory.Adjunction
