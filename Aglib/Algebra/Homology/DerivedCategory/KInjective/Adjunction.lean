/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.Algebra.Homology.DerivedCategory.KInjective.Hom
public import Aglib.Algebra.Homology.HomotopyCategory.Adjunction
public import Mathlib.CategoryTheory.Adjunction.Additive

/-!
# Adjunction Hom equivalences at K-injective targets

The actual homotopy adjunction and the two native homotopy-to-derived Hom
bijections give an additive derived Hom equivalence when the supplied target I
and its actual right-adjoint image G(I) are K-injective. The original chain
adjoints are preserved. This does not assume that either additive functor is
exact, or construct a global adjunction of derived functors.

Source: `Quillen/Algebra/Homology/Adjunction.lean` at frozen dirty Quillen
`6db56ddd3fdb898ef5de29d5fe51a0c61f9ba116`.
Source SHA-256: `1b633acd4a4a8f7639b1946acdfd90261736255b077c863c324777b87b16ac60`.
Selected source lines: 123–163.
-/
@[expose] public section

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
universe u v u' v' w
open CategoryTheory CategoryTheory.Limits

universe w'
namespace CategoryTheory.Adjunction
variable {C : Type u} [Category.{v} C] [Abelian C] [HasDerivedCategory.{w} C]
  {D : Type u'} [Category.{v'} D] [Abelian D] [HasDerivedCategory.{w'} D]
  {F : C ⥤ D} {G : D ⥤ C} (adj : F ⊣ G) [F.Additive] [G.Additive]
  (K : CochainComplex C ℤ) (I : CochainComplex D ℤ)
  [I.IsKInjective] [_root_.CochainComplex.IsKInjective ((G.mapHomologicalComplex (.up ℤ)).obj I)]

/-- The genuine homotopy adjunction and both injective-target localization bijections give derived
  Hom transport. -/
def cochainDerivedHomEquivOfKInjective :
    (DerivedCategory.Q.obj ((F.mapHomologicalComplex (.up ℤ)).obj K) ⟶ DerivedCategory.Q.obj I) ≃+
      (DerivedCategory.Q.obj K ⟶ DerivedCategory.Q.obj ((G.mapHomologicalComplex (.up ℤ)).obj I)) :=
  ((CochainComplex.homotopyDerivedHomEquiv
    ((F.mapHomologicalComplex (.up ℤ)).obj K) I).symm.trans
    (adj.mapCochainHomotopyCategory.homAddEquiv
      ((HomotopyCategory.quotient C (.up ℤ)).obj K)
      ((HomotopyCategory.quotient D (.up ℤ)).obj I))).trans
    (CochainComplex.homotopyDerivedHomEquiv K ((G.mapHomologicalComplex (.up ℤ)).obj I))

/-- Actual chain adjoints are preserved by the original derived Hom equivalence. -/
@[simp]
lemma cochainDerivedHomEquivOfKInjective_map
    (f : (F.mapHomologicalComplex (.up ℤ)).obj K ⟶ I) :
    adj.cochainDerivedHomEquivOfKInjective K I (DerivedCategory.Q.map f) =
      DerivedCategory.Q.map ((adj.mapHomologicalComplex (.up ℤ)).homEquiv K I f) := by
  change CochainComplex.homotopyDerivedHomEquiv K _
    (adj.cochainHomotopyHomEquiv K I
      ((CochainComplex.homotopyDerivedHomEquiv _ I).symm (DerivedCategory.Q.map f))) = _
  rw [CochainComplex.homotopyDerivedHomEquiv_symm_map,
    cochainHomotopyHomEquiv_map, CochainComplex.homotopyDerivedHomEquiv_map]

/-- The inverse equivalence likewise retains the original chain adjoint. -/
@[simp]
lemma cochainDerivedHomEquivOfKInjective_symm_map
    (g : K ⟶ (G.mapHomologicalComplex (.up ℤ)).obj I) :
    (adj.cochainDerivedHomEquivOfKInjective K I).symm (DerivedCategory.Q.map g) =
      DerivedCategory.Q.map (((adj.mapHomologicalComplex (.up ℤ)).homEquiv K I).symm g) := by
  apply (adj.cochainDerivedHomEquivOfKInjective K I).injective
  rw [AddEquiv.apply_symm_apply, cochainDerivedHomEquivOfKInjective_map, Equiv.apply_symm_apply]

end CategoryTheory.Adjunction
