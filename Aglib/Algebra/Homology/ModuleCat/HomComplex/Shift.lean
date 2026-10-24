/-
Copyright (c) 2026 kangxyz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.Algebra.Homology.ModuleCat.HomComplex.Derived

/-!
# The original signed source-shift comparison for module Hom complexes

The native left-shift linear equivalence retains its integer-unit sign.
It identifies the original source-shifted Hom complex with the opposite
shift of the original Hom complex. The derived comparison includes the
actual localization and shift isomorphisms; no global shift coherence
instance is asserted.
-/

@[expose] public section
noncomputable section


open CategoryTheory CategoryTheory.Limits Opposite

universe r u v w

namespace CochainComplex.HomComplex

section Linear

variable (R : Type r) [Ring R] {C : Type u} [Category.{v} C]
  [Preadditive C] [Linear R C]

/-- The original module Hom complex under a source shift, using the native
leftShiftLinearEquiv, including its original integer-unit sign. -/
def moduleComplexLeftShiftIso (K J : CochainComplex C ℤ) (s : ℤ) :
    (moduleComplex R K J)⟦-s⟧ ≅ moduleComplex R (K⟦s⟧) J :=
  HomologicalComplex.Hom.isoOfComponents
    (fun n => (moduleComplex R K J).shiftFunctorObjXIso (-s) n (n + (-s)) rfl ≪≫
      (Cochain.leftShiftLinearEquiv R K J (n + (-s)) s n (by omega)).toModuleIso)
    (by
      intro i j hij
      apply ConcreteCategory.hom_ext
      intro φ
      change δ i j ((show Cochain K J (i + (-s)) from φ).leftShift s i (by omega)) =
        ((-s).negOnePow • δ (i + (-s)) (j + (-s))
          (show Cochain K J (i + (-s)) from φ)).leftShift s j (by omega)
      rw [Cochain.δ_leftShift _ s i j (by omega) (j + (-s)) (by omega),
        Cochain.leftShift_units_smul, Int.negOnePow_neg])

/-- Each component is the original signed left-shift operation on cochains. -/
theorem moduleComplexLeftShiftIso_hom_f_apply (K J : CochainComplex C ℤ) (s n : ℤ)
    (φ : Cochain K J (n + (-s))) :
    (moduleComplexLeftShiftIso R K J s).hom.f n φ = φ.leftShift s n (by omega) := rfl

end Linear

variable {A : Type u} [CommRing A]
  [HasDerivedCategory.{w} (ModuleCat.{v} A)]

/-- A displayed universal object comparison for the existing derived dual,
retaining the native source shift and both original localization factors.
This does not assert a global CommShift coherence instance. -/
def derivedDualShiftObjIso (J K : CochainComplex (ModuleCat.{v} A) ℤ)
    [J.IsKInjective] (s : ℤ) :
    (derivedDual J).obj (op ((DerivedCategory.Q.obj K)⟦s⟧)) ≅
      ((derivedDual J).obj (op (DerivedCategory.Q.obj K)))⟦-s⟧ :=
  (derivedDual J).mapIso (((DerivedCategory.Q.commShiftIso s).app K).op) ≪≫
    (derivedDualFactors J).app (op (K⟦s⟧)) ≪≫
    DerivedCategory.Q.mapIso (moduleComplexLeftShiftIso A K J s).symm ≪≫
    (DerivedCategory.Q.commShiftIso (-s)).app (moduleComplex A K J) ≪≫
    (CategoryTheory.shiftFunctor (DerivedCategory (ModuleCat.{v} A)) (-s)).mapIso
      ((derivedDualFactors J).app (op K)).symm

end CochainComplex.HomComplex
