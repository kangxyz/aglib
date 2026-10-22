/-
Copyright (c) 2026 kangxyz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.RingTheory.AdicCompletion.SameUniformizer
public import Aglib.RingTheory.DiscreteValuationRing.ParameterPoint
public import Aglib.RingTheory.DiscreteValuationRing.ParameterGenericResidue
public import Mathlib.RingTheory.AlgebraicIndependent.Basic

/-! # Canonical maps into the actual completed parameter DVR -/

@[expose] public noncomputable section

open IsLocalRing

universe u v

namespace ParameterLocalization

variable (R : Type u) [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]
  (ι : Type v) [Finite ι] (p : R) [Fact (Irreducible p)]

attribute [local instance] isDiscreteValuationRing algebraMap_isLocalHom

local notation "T" => Ring R ι p
local notation "A" => AdicCompletion (maximalIdeal R) R
local notation "B" => AdicCompletion (maximalIdeal T) T

/-- A map between the literal maximal-ideal completions of R and its parameter DVR. -/
def completionMap : A →+* B :=
  AdicCompletion.sameUniformizerMap (algebraMap R T) p
    (Fact.out : Irreducible p) (uniformizer_irreducible R ι p)

@[simp] theorem completionMap_algebraMap (r : R) :
    completionMap R ι p (algebraMap R A r) = algebraMap T B (algebraMap R T r) :=
  AdicCompletion.sameUniformizerMap_algebraMap _ _ _ _ r

theorem completionMap_injective : Function.Injective (completionMap R ι p) :=
  AdicCompletion.sameUniformizerMap_injective _ _ _ _

theorem completionMap_isLocalHom : IsLocalHom (completionMap R ι p) :=
  AdicCompletion.sameUniformizerMap_isLocalHom _ _ _ _

/-- Only this explicit map is used for the completed coefficient action. -/
abbrev completionAlgebra : Algebra A B := (completionMap R ι p).toAlgebra

attribute [local instance] completionAlgebra

theorem completionAlgebra_isLocalHom : IsLocalHom (algebraMap A B) :=
  completionMap_isLocalHom R ι p

attribute [local instance] completionAlgebra_isLocalHom

/-- The coefficient action agrees with the original R action on the target completion. -/
theorem completionAlgebra_tower : IsScalarTower R A B := by
  apply IsScalarTower.of_algebraMap_eq
  intro r
  change algebraMap R B r = completionMap R ι p (algebraMap R A r)
  rw [completionMap_algebraMap, ← IsScalarTower.algebraMap_apply R T B]

/-- The marked residue field uses the native completion and parameter residue equivalences. -/
def completionResidueEquiv :
    ResidueField B ≃+* FractionRing (MvPolynomial ι (ResidueField R)) :=
  (AdicCompletion.residueFieldEquiv T).trans (residueFieldRingEquiv R ι p)

/-- The completed coefficient residue map is the canonical inclusion k → k(Z). -/
theorem completionResidueEquiv_coeff (x : ResidueField A) :
    completionResidueEquiv R ι p (algebraMap (ResidueField A) (ResidueField B) x) =
      algebraMap (ResidueField R) (FractionRing (MvPolynomial ι (ResidueField R)))
        (AdicCompletion.residueFieldEquiv R x) := by
  let : IsLocalHom (completionMap R ι p) := completionMap_isLocalHom R ι p
  change residueFieldRingEquiv R ι p
    (AdicCompletion.residueFieldEquiv T (ResidueField.map (completionMap R ι p) x)) = _
  rw [show AdicCompletion.residueFieldEquiv T
      (ResidueField.map (completionMap R ι p) x) =
        ResidueField.map (algebraMap R T) (AdicCompletion.residueFieldEquiv R x) from
    AdicCompletion.residueFieldEquiv_sameUniformizerMap _ _ _ _ x]
  exact residueFieldAlgEquiv_coeff R ι p _

/-- The variables are the original polynomial variables, then mapped into the actual completion. -/
def completedVariable (i : ι) : B :=
  algebraMap T B (algebraMap (MvPolynomial ι R) T (MvPolynomial.X i))

/-- The marked completion residue retains the original rational variable. -/
theorem completionResidueEquiv_variable (i : ι) :
    completionResidueEquiv R ι p (residue B (completedVariable R ι p i)) =
      algebraMap (MvPolynomial ι (ResidueField R))
        (FractionRing (MvPolynomial ι (ResidueField R))) (MvPolynomial.X i) := by
  change residueFieldRingEquiv R ι p
    (AdicCompletion.residueFieldEquiv T
      (residue B (algebraMap T B (algebraMap (MvPolynomial ι R) T (MvPolynomial.X i))))) = _
  rw [← ResidueField.map_residue, AdicCompletion.residueFieldEquiv_map]
  exact residueFieldAlgEquiv_X R ι p i

/-- The residue scalar square is an equality of the actual maps, before using independence. -/
theorem completionResidue_scalar_square :
    (algebraMap (ResidueField A) (ResidueField B)).comp
        (ResidueField.map (algebraMap R A)) =
      (ResidueField.map (algebraMap T B)).comp
        (algebraMap (ResidueField R) (ResidueField T)) := by
  apply RingHom.ext
  intro x
  obtain ⟨r, rfl⟩ := residue_surjective x
  change residue B (completionMap R ι p (algebraMap R A r)) =
    residue B (algebraMap T B (algebraMap R T r))
  rw [completionMap_algebraMap]

/-- Independence is transported through the proved residue square, not assumed of the completion. -/
theorem algebraicIndependent_completedResidue :
    AlgebraicIndependent (ResidueField A)
      (fun i => residue B (completedVariable R ι p i)) := by
  have h := (algebraicIndependent_genericResidue R ι p).ringHom_of_comp_eq
    (ResidueField.map (algebraMap R A)) (ResidueField.map (algebraMap T B))
    (AdicCompletion.residueField_map_bijective R).2
    (RingHom.injective (ResidueField.map (algebraMap T B)))
    (completionResidue_scalar_square R ι p)
  simpa only [Function.comp_def, genericResidue, ResidueField.map_residue,
    completedVariable] using h

/-- The completed coefficient uniformizer remains the actual target uniformizer. -/
theorem irreducible_completionAlgebra_uniformizer :
    Irreducible (algebraMap A B (algebraMap R A p)) := by
  change Irreducible (completionMap R ι p (algebraMap R A p))
  rw [completionMap_algebraMap]
  exact AdicCompletion.irreducible_algebraMap T _ (uniformizer_irreducible R ι p)

/-- The original variables are already independent over the actual completed coefficient ring. -/
theorem algebraicIndependent_completedVariable :
    AlgebraicIndependent A (completedVariable R ι p) := by
  let : Fact (Irreducible (algebraMap R A p)) :=
    ⟨AdicCompletion.irreducible_algebraMap R p Fact.out⟩
  exact algebraicIndependent_of_residue (algebraMap R A p)
    (completedVariable R ι p) (algebraicIndependent_completedResidue R ι p)
    (irreducible_completionAlgebra_uniformizer R ι p)

/-- The actual polynomial evaluation on completed coefficients. -/
def completedPolynomialMap : MvPolynomial ι A →ₐ[A] B :=
  MvPolynomial.aeval (completedVariable R ι p)

theorem completedPolynomialMap_injective :
    Function.Injective (completedPolynomialMap R ι p) :=
  algebraicIndependent_completedVariable R ι p

/-- Evaluation on original polynomials retains the original T-to-completion map. -/
theorem completedPolynomialMap_map (q : MvPolynomial ι R) :
    completedPolynomialMap R ι p (MvPolynomial.map (algebraMap R A) q) =
      algebraMap T B (algebraMap (MvPolynomial ι R) T q) := by
  have he : (completedPolynomialMap R ι p).toRingHom.comp
      (MvPolynomial.map (algebraMap R A)) =
        (algebraMap T B).comp (algebraMap (MvPolynomial ι R) T) := by
    apply MvPolynomial.ringHom_ext
    · intro r
      change MvPolynomial.aeval (completedVariable R ι p)
        (MvPolynomial.map (algebraMap R A) (MvPolynomial.C r)) = _
      rw [MvPolynomial.map_C, MvPolynomial.aeval_C]
      change completionMap R ι p (algebraMap R A r) = _
      rw [completionMap_algebraMap]
      exact congrArg (algebraMap T B)
        (IsScalarTower.algebraMap_apply R (MvPolynomial ι R) T r)
    · intro i
      change MvPolynomial.aeval (completedVariable R ι p)
        (MvPolynomial.map (algebraMap R A) (MvPolynomial.X i)) = _
      rw [MvPolynomial.map_X, MvPolynomial.aeval_X]
      rfl
  exact RingHom.congr_fun he q

/-- The evaluation extends through the actual parameter localization over completed coefficients. -/
def completedParameterPoint :
    letI : Fact (Irreducible (algebraMap R A p)) :=
      ⟨AdicCompletion.irreducible_algebraMap R p Fact.out⟩
    Ring A ι (algebraMap R A p) →ₐ[A] B := by
  letI : Fact (Irreducible (algebraMap R A p)) :=
    ⟨AdicCompletion.irreducible_algebraMap R p Fact.out⟩
  exact point (algebraMap R A p) (completedVariable R ι p)
    (algebraicIndependent_completedResidue R ι p)

theorem completedParameterPoint_injective :
    Function.Injective (completedParameterPoint R ι p) := by
  let : Fact (Irreducible (algebraMap R A p)) :=
    ⟨AdicCompletion.irreducible_algebraMap R p Fact.out⟩
  exact point_injective (algebraMap R A p) (completedVariable R ι p)
    (algebraicIndependent_completedResidue R ι p)
    (irreducible_completionAlgebra_uniformizer R ι p)

/-- Actual polynomial inclusion induces a map of the actual fraction fields. -/
def completedPolynomialFractionMap : FractionRing (MvPolynomial ι A) →+* FractionRing B :=
  IsFractionRing.lift
    (g := (algebraMap B (FractionRing B)).comp (completedPolynomialMap R ι p).toRingHom)
    ((IsFractionRing.injective B (FractionRing B)).comp
      (completedPolynomialMap_injective R ι p))

@[simp] theorem completedPolynomialFractionMap_algebraMap (q : MvPolynomial ι A) :
    completedPolynomialFractionMap R ι p (algebraMap _ (FractionRing (MvPolynomial ι A)) q) =
      algebraMap B (FractionRing B) (completedPolynomialMap R ι p q) :=
  IsFractionRing.lift_algebraMap _ q

/-- The original scalar completion map extends to the actual coefficient fraction fields. -/
def completionFractionMap : FractionRing A →+* FractionRing B :=
  AdicCompletion.sameUniformizerFractionMap (algebraMap R T) p
    (Fact.out : Irreducible p) (uniformizer_irreducible R ι p)

@[simp] theorem completionFractionMap_algebraMap (a : A) :
    completionFractionMap R ι p (algebraMap A (FractionRing A) a) =
      algebraMap B (FractionRing B) (completionMap R ι p a) :=
  AdicCompletion.sameUniformizerFractionMap_algebraMap _ _ _ _ a

end ParameterLocalization
