/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.Cohomology.Cech.DegreeZero
public import Aglib.AlgebraicGeometry.Cohomology.Cech.Finite.Vanishing
public import Mathlib.Algebra.Homology.Embedding.CochainComplex

/-!
# A bounded structural-ring model from actual Cech truncation

The original module-valued Cech complex is extended by zero to the integers
and canonically truncated at the sharp finite affine-cover bound. Its original
inclusion is a quasi-isomorphism. In every nonnegative degree the resulting
bounded complex computes the unchanged `Sheaf.H` linearly over the specified
structural ring.

Below the upper bound the terms are the original affine-intersection section
modules. The upper term is the actual cycle module of the untruncated complex;
this construction makes no flatness or finiteness assertion about that term.
-/

@[expose] public section

noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry TopologicalSpace Opposite
open HomologicalComplex CategoryTheory.Cech

universe u

namespace AlgebraicGeometry.Scheme.Cohomology

variable {R : Type u} [CommRing R] (X : Scheme.{u}) (α : R →+* Γ(X, ⊤))
  {ι : Type u} (U : ι → X.Opens)

/-- The original structural-ring Cech complex, extended by zero to the integers,
functorially in its actual module coefficient. -/
def moduleCechIntFunctor : X.Modules ⥤ CochainComplex (ModuleCat.{u} R) ℤ :=
  moduleSectionsPresheafFunctor X α ⋙ cechComplexFunctor U ⋙
    ComplexShape.embeddingUpNat.extendFunctor (ModuleCat.{u} R)

/-- The original Cech complex extended by zero in negative degrees. -/
abbrev moduleCechIntComplex (M : X.Modules) : CochainComplex (ModuleCat.{u} R) ℤ :=
  (moduleCechIntFunctor X α U).obj M

/-- Canonical finite upper truncation of the actual structural-ring Cech complex,
functorially in the original module coefficient. -/
def moduleFiniteCechFunctor (n : ℕ) : X.Modules ⥤ CochainComplex (ModuleCat.{u} R) ℤ :=
  moduleCechIntFunctor X α U ⋙
    (ComplexShape.embeddingUpIntLE (n : ℤ)).truncLEFunctor (ModuleCat.{u} R)

/-- The actual good truncation at degree `n`. Its upper term consists of cycles. -/
abbrev moduleFiniteCechComplex (M : X.Modules) (n : ℕ) :
    CochainComplex (ModuleCat.{u} R) ℤ :=
  (moduleFiniteCechFunctor X α U n).obj M

/-- The original inclusion of the bounded truncation into the unchanged Cech complex. -/
abbrev moduleFiniteCechInclusion (M : X.Modules) (n : ℕ) :
    moduleFiniteCechComplex X α U M n ⟶ moduleCechIntComplex X α U M :=
  (moduleCechIntComplex X α U M).ιTruncLE (n : ℤ)

instance (M : X.Modules) (n : ℕ) :
    CochainComplex.IsStrictlyGE (moduleFiniteCechComplex X α U M n) 0 := by
  change CochainComplex.IsStrictlyGE
    (CochainComplex.truncLE
      ((moduleCechComplex X α M U).extend ComplexShape.embeddingUpNat) (n : ℤ)) 0
  infer_instance

instance (M : X.Modules) (n : ℕ) :
    CochainComplex.IsStrictlyLE (moduleFiniteCechComplex X α U M n) (n : ℤ) := by
  change CochainComplex.IsStrictlyLE
    ((moduleCechIntComplex X α U M).truncLE (n : ℤ)) (n : ℤ)
  infer_instance

/-- Below the upper boundary the finite model retains the original section terms. -/
def moduleFiniteCechXIso (M : X.Modules) (n q : ℕ) (hq : q < n) :
    (moduleFiniteCechComplex X α U M n).X (q : ℤ) ≅ (moduleCechComplex X α M U).X q :=
  (moduleCechIntComplex X α U M).truncLEXIso (n : ℤ) (q : ℤ) (by omega) ≪≫
    (moduleCechComplex X α M U).extendXIso ComplexShape.embeddingUpNat rfl

/-- The boundary term is the actual cycle module, rather than a prescribed flat module. -/
def moduleFiniteCechTopIsoCycles (M : X.Modules) (n : ℕ) :
    (moduleFiniteCechComplex X α U M n).X (n : ℤ) ≅
      (moduleCechIntComplex X α U M).cycles (n : ℤ) :=
  (moduleCechIntComplex X α U M).truncLEXIsoCycles (n : ℤ)

/-- Coefficient maps commute with the literal truncation inclusion. -/
@[reassoc]
theorem moduleFiniteCechInclusion_naturality {M N : X.Modules} (f : M ⟶ N) (n : ℕ) :
    (moduleFiniteCechFunctor X α U n).map f ≫ moduleFiniteCechInclusion X α U N n =
      moduleFiniteCechInclusion X α U M n ≫ (moduleCechIntFunctor X α U).map f :=
  CochainComplex.ιTruncLE_naturality _ _

variable [X.IsSeparated] (M : X.Modules) [M.IsQuasicoherent]
  (n : ℕ) (e : ι ≃ Fin (n + 1)) (hU : ∀ i, IsAffineOpen (U i)) (hcover : iSup U = ⊤)

include e hU hcover

/-- The actual integer-indexed Cech complex obeys the sharp finite affine-cover bound. -/
theorem moduleCechIntComplex_isLE :
    CochainComplex.IsLE (moduleCechIntComplex X α U M) (n : ℤ) := by
  rw [CochainComplex.isLE_iff]
  intro i hi
  let q := i.toNat
  have hq : (q : ℤ) = i := Int.toNat_of_nonneg (by omega)
  have hqn : n < q := by omega
  have hq0 : q ≠ 0 := by omega
  obtain ⟨q, hq'⟩ := Nat.exists_eq_succ_of_ne_zero hq0
  have hcov : (⨆ j : Fin (n + 1), U (e.symm j)) = ⊤ :=
    e.symm.iSup_comp.trans hcover
  have hzero := subsingleton_sheafH_of_finite_affine_cover M n
    (fun j => U (e.symm j)) (fun j => hU (e.symm j)) hcov (q + 1) (by omega)
  let := moduleCohomologyModuleOfHom X α M (q + 1)
  let : Subsingleton (Sheaf.H.{u + 1} (moduleAddSheaf X M) (q + 1)) := hzero
  have : Subsingleton ((moduleCechComplex X α M U).homology (q + 1)) :=
    (moduleAffineCechCohomologyLinearEquiv X α M U hcover
      (injectiveResolution (moduleAddSheaf X M)) q hU).injective.subsingleton
  rw [exactAt_iff_isZero_homology]
  exact (ModuleCat.isZero_of_subsingleton ((moduleCechComplex X α M U).homology (q + 1))).of_iso
    ((moduleCechComplex X α M U).extendHomologyIso ComplexShape.embeddingUpNat
      (show ((q + 1 : ℕ) : ℤ) = i by omega))

/-- The original truncation inclusion is a quasi-isomorphism for a finite affine cover. -/
theorem moduleFiniteCechInclusion_quasiIso :
    QuasiIso (moduleFiniteCechInclusion X α U M n) := by
  have := moduleCechIntComplex_isLE X α U M n e hU hcover
  infer_instance

/-- Native homology comparison from the literal truncation inclusion and zero extension. -/
def moduleFiniteCechHomologyIso (q : ℕ) :
    (moduleFiniteCechComplex X α U M n).homology (q : ℤ) ≅
      (moduleCechComplex X α M U).homology q := by
  letI := moduleFiniteCechInclusion_quasiIso X α U M n e hU hcover
  exact asIso (homologyMap (moduleFiniteCechInclusion X α U M n) (q : ℤ)) ≪≫
    (moduleCechComplex X α M U).extendHomologyIso ComplexShape.embeddingUpNat rfl

/-- Every nonnegative degree of the bounded model computes the unchanged sheaf
cohomology, linearly over the original structural ring, including degree zero. -/
def moduleFiniteCechCohomologyLinearEquiv (q : ℕ) :
    letI := moduleCohomologyModuleOfHom X α M q
    (moduleFiniteCechComplex X α U M n).homology (q : ℤ) ≃ₗ[R]
      Sheaf.H.{u + 1} (moduleAddSheaf X M) q := by
  letI := moduleCohomologyModuleOfHom X α M q
  cases q with
  | zero =>
    exact (moduleFiniteCechHomologyIso X α U M n e hU hcover 0).toLinearEquiv.trans
      (moduleCechCohomologyLinearEquivZero X α M U hcover)
  | succ q =>
    exact (moduleFiniteCechHomologyIso X α U M n e hU hcover (q + 1)).toLinearEquiv.trans
      (moduleAffineCechCohomologyLinearEquiv X α M U hcover
        (injectiveResolution (moduleAddSheaf X M)) q hU)

end AlgebraicGeometry.Scheme.Cohomology
