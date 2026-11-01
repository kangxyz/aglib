/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.Algebra.Homology.DerivedCategory.ExactFunctorHomology

/-!
# Joint conservativity of original exact derived functors

An exact family which jointly detects isomorphisms of abelian objects also
detects isomorphisms on the selected unbounded derived categories. The proof
uses the original exact homology comparisons. It detects invertibility of
the given arrow and makes no equality or faithfulness claim.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

namespace CategoryTheory.Functor

universe uI uA vA wA uB vB wB

variable {ι : Type uI}
  {A : Type uA} [Category.{vA} A] [Abelian A] [HasDerivedCategory.{wA} A]
  {B : ι → Type uB} [∀ i, Category.{vB} (B i)] [∀ i, Abelian (B i)]
  [∀ i, HasDerivedCategory.{wB} (B i)]
  (F : ∀ i, A ⥤ B i)
  [∀ i, (F i).Additive]
  [∀ i, PreservesFiniteLimits (F i)] [∀ i, PreservesFiniteColimits (F i)]

/-- Joint conservativity of the original exact coefficient functors passes
to their native derived localizations, with the same arrow as conclusion. -/
theorem isIso_of_mapDerivedCategory_family
    (hF : ∀ {M N : A} (a : M ⟶ N), (∀ i, IsIso ((F i).map a)) → IsIso a)
    {K L : DerivedCategory A} (a : K ⟶ L)
    (ha : ∀ i, IsIso ((F i).mapDerivedCategory.map a)) : IsIso a := by
  apply (DerivedCategory.isIso_iff A a).mpr
  intro n
  apply hF
  intro i
  let : IsIso ((F i).mapDerivedCategory.map a) := ha i
  exact (NatIso.isIso_map_iff ((F i).mapDerivedCategoryHomologyIso n) a).mp
    (show IsIso ((DerivedCategory.homologyFunctor (B i) n).map
      ((F i).mapDerivedCategory.map a)) from inferInstance)

end CategoryTheory.Functor
