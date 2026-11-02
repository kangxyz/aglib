/-
Copyright (c) 2026 kangxyz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.Morphisms.Finite.CompletedLocalModel
public import Aglib.AlgebraicGeometry.FunctionField.StalkMap
public import Aglib.RingTheory.AdicCompletion.FiniteSemilocalDegree

/-!
# Degree of the original completed stalk map

The entire finite local algebra supplies the completed factor and its generic-rank
embedding. Transport through the original stalk equivalence keeps the actual
source completion. Every finite quotient of its completed structural map is
identified with the quotient of the original stalk map.

No uncompleted selected stalk is assumed finite. A Noetherian target stalk gives
finiteness and locality after completion; regularity gives injectivity. Domainhood
of the actual source completion is used only for its fraction field and degree.
The surface consumer must prove that domainhood from its original geometry.
-/

@[expose] public noncomputable section

open CategoryTheory IsLocalRing
open scoped nonZeroDivisors

namespace AlgebraicGeometry.Scheme.Hom.LocalNormAlgebra

universe u

private theorem localPower_le_comap {A B : Type*} [CommRing A] [CommRing B]
    [IsLocalRing A] [IsLocalRing B] (g : A →+* B) [IsLocalHom g] (n : ℕ) :
    maximalIdeal A ^ n ≤ (maximalIdeal B ^ n).comap g := by
  apply Ideal.map_le_iff_le_comap.mp
  rw [Ideal.map_pow]
  exact Ideal.pow_right_mono (IsLocalRing.map_maximalIdeal_le g) n

private theorem eval_completionIdealEquiv {A : Type*} [CommRing A]
    (I J : Ideal A) (hIJ : I = J) (n : ℕ) (z : AdicCompletion I A) :
    AdicCompletion.evalₐ J n (Scheme.LocalRing.completionIdealEquiv I J hIJ z) =
      Ideal.quotientMap (J ^ n) (RingHom.id A)
        (by subst J; exact le_rfl) (AdicCompletion.evalₐ I n z) := by
  subst J
  change AdicCompletion.evalₐ I n z =
    Ideal.quotientMap (I ^ n) (RingHom.id A) _ (AdicCompletion.evalₐ I n z)
  obtain ⟨a, ha⟩ := Ideal.Quotient.mk_surjective (AdicCompletion.evalₐ I n z)
  rw [← ha]
  rfl

private theorem eval_completionCongr {A B : Type*} [CommRing A] [CommRing B]
    [IsLocalRing A] [IsLocalRing B] (e : A ≃+* B)
    (n : ℕ) (z : AdicCompletion (maximalIdeal A) A) :
    AdicCompletion.evalₐ (maximalIdeal B) n (Scheme.LocalRing.completionCongr e z) =
      Ideal.quotientMap (maximalIdeal B ^ n) (e : A →+* B)
        (by
          let : IsLocalHom (e : A →+* B) := IsLocalHom.of_surjective _ e.surjective
          exact localPower_le_comap (e : A →+* B) n)
        (AdicCompletion.evalₐ (maximalIdeal A) n z) := by
  have he : Function.Surjective (e : A →+* B) := e.surjective
  change AdicCompletion.evalₐ (maximalIdeal B) n
    (Scheme.LocalRing.completionIdealEquiv _ _
      (IsLocalRing.map_maximalIdeal_of_surjective (e : A →+* B) he)
      (AdicCompletion.congrRingEquiv e (maximalIdeal A) z)) = _
  rw [eval_completionIdealEquiv, AdicCompletion.evalₐ_congrRingEquiv]
  obtain ⟨a, ha⟩ := Ideal.Quotient.mk_surjective
    (AdicCompletion.evalₐ (maximalIdeal A) n z)
  rw [← ha]
  rfl

variable {X Y : Scheme.{u}} [IsIntegral X] [IsIntegral Y]
  (f : X ⟶ Y) [IsDominant f] [IsFinite f]
  (U : Y.Opens) (hU : IsAffineOpen U) (y : U) [Nonempty U]

attribute [local instance] chartAlgebra stalkAlgebra functionFieldAlgebra branchStalkAlgebra

local notation "R" => Y.presheaf.stalk y.val
local notation "S" => Ring f U hU y

variable (q : MaximalSpectrum (Ring f U hU y))

local notation "T" => X.presheaf.stalk (branchPoint f U hU y q)
local notation "Rhat" => AdicCompletion (maximalIdeal R) R
local notation "That" => AdicCompletion (maximalIdeal T) T
local notation "qh" => completionBranch f U hU y q
local notation "H" => AdicCompletion.FiniteSemilocal.Completed R S qh

/-- The canonical completed-base map transported through the completion of the
same original stalk equivalence. -/
def completedStalkMapAt : Rhat →+* That := by
  let := AdicCompletion.FiniteSemilocal.baseAlgebra R S qh
  exact (completedBranchStalkEquiv f U hU y q).toRingHom.comp (algebraMap Rhat H)

/-- The completed scalar action is induced by the original completed map. -/
@[instance_reducible]
def completedStalkAlgebraAt : Algebra Rhat That :=
  (completedStalkMapAt f U hU y q).toAlgebra

attribute [local instance] completedStalkAlgebraAt

/-- The actual completed-stalk comparison is linear for the original completed
structural map, not for a separately supplied algebra structure. -/
def completedBranchStalkAlgEquiv :
    let := AdicCompletion.FiniteSemilocal.baseAlgebra R S qh
    H ≃ₐ[Rhat] That := by
  let := AdicCompletion.FiniteSemilocal.baseAlgebra R S qh
  exact { completedBranchStalkEquiv f U hU y q with commutes' := fun _ => rfl }

/-- At every precision the completed map is induced by the original stalk map. -/
theorem completedStalkMapAt_eval (n : ℕ) (z : Rhat) :
    AdicCompletion.evalₐ (maximalIdeal T) n (completedStalkMapAt f U hU y q z) =
      Ideal.quotientMap (maximalIdeal T ^ n)
        (stalkMapAt f (branchPoint f U hU y q) y.val (branchPoint_map f U hU y q))
        (by
          apply Ideal.map_le_iff_le_comap.mp
          rw [Ideal.map_pow]
          exact Ideal.pow_right_mono (IsLocalRing.map_maximalIdeal_le _) n)
        (AdicCompletion.evalₐ (maximalIdeal R) n z) := by
  change AdicCompletion.evalₐ (maximalIdeal T) n
    (Scheme.LocalRing.completionCongr (completionBranchLocalEquiv f U hU y q)
      (AdicCompletion.FiniteLocalization.completionMap
        (AdicCompletion.FiniteSemilocal.branchIdeal R S qh)
        (AdicCompletion.FiniteSemilocal.branch_contraction R S qh) z)) = _
  rw [eval_completionCongr, AdicCompletion.FiniteLocalization.eval_completionMap]
  obtain ⟨r, hr⟩ := Ideal.Quotient.mk_surjective
    (AdicCompletion.evalₐ (maximalIdeal R) n z)
  rw [← hr]
  change Ideal.Quotient.mk (maximalIdeal T ^ n)
      (completionBranchLocalEquiv f U hU y q (algebraMap R _ r)) =
    Ideal.Quotient.mk (maximalIdeal T ^ n)
      (stalkMapAt f (branchPoint f U hU y q) y.val (branchPoint_map f U hU y q) r)
  exact congrArg (Ideal.Quotient.mk (maximalIdeal T ^ n))
    (RingHom.congr_fun (completionBranchLocalEquiv_stalkMap f U hU y q) r)

/-- The original stalk map is retained on original completion coefficients. -/
theorem completedStalkMapAt_algebraMap (r : R) :
    completedStalkMapAt f U hU y q (algebraMap R Rhat r) =
      algebraMap T That
        (stalkMapAt f (branchPoint f U hU y q) y.val (branchPoint_map f U hU y q) r) :=
  completedBranchStalkEquiv_base f U hU y q r

/-- The same-precision equations uniquely determine the original completed map. -/
theorem completedStalkMapAt_unique (c : Rhat →+* That)
    (hc : ∀ (n : ℕ) (z : Rhat), AdicCompletion.evalₐ (maximalIdeal T) n (c z) =
      Ideal.quotientMap (maximalIdeal T ^ n)
        (stalkMapAt f (branchPoint f U hU y q) y.val (branchPoint_map f U hU y q))
        (by
          apply Ideal.map_le_iff_le_comap.mp
          rw [Ideal.map_pow]
          exact Ideal.pow_right_mono (IsLocalRing.map_maximalIdeal_le _) n)
        (AdicCompletion.evalₐ (maximalIdeal R) n z)) :
    c = completedStalkMapAt f U hU y q := by
  apply RingHom.ext
  intro z
  apply AdicCompletion.ext_evalₐ
  intro n
  exact (hc n z).trans (completedStalkMapAt_eval f U hU y q n z).symm

section Noetherian

variable [IsNoetherianRing (Y.presheaf.stalk y.val)]

/-- Noetherianity of the source stalk comes from localization of the whole finite
algebra. Finiteness of this selected stalk is neither assumed nor asserted. -/
theorem completedSourceStalk_noetherian : IsNoetherianRing T := by
  let : IsNoetherianRing S := IsNoetherianRing.of_finite R S
  exact isNoetherianRing_of_ringEquiv
    (AdicCompletion.FiniteSemilocal.Local R S qh) (completionBranchLocalEquiv f U hU y q)

attribute [local instance] completedSourceStalk_noetherian

/-- The original completed source stalk is finite over the completed target. -/
theorem completedStalk_finite : Module.Finite Rhat That := by
  let := AdicCompletion.FiniteSemilocal.baseAlgebra R S qh
  let := AdicCompletion.FiniteSemilocal.baseFinite R S qh
  exact Module.Finite.equiv (completedBranchStalkAlgEquiv f U hU y q).toLinearEquiv

/-- The completed original structural map is local. -/
theorem completedStalkMapAt_isLocalHom : IsLocalHom (completedStalkMapAt f U hU y q) := by
  let : IsNoetherianRing S := IsNoetherianRing.of_finite R S
  let := AdicCompletion.FiniteSemilocal.baseAlgebra R S qh
  let := AdicCompletion.FiniteSemilocal.baseIsLocalHom R S qh
  let : IsLocalHom (completedBranchStalkEquiv f U hU y q).toRingHom :=
    IsLocalHom.of_surjective _ (completedBranchStalkEquiv f U hU y q).surjective
  change IsLocalHom
    ((completedBranchStalkEquiv f U hU y q).toRingHom.comp (algebraMap Rhat H))
  infer_instance

attribute [local instance] completedStalkMapAt_isLocalHom

/-- The original residue maps commute with the actual completed structural map. -/
theorem completedStalkMapAt_residue_square :
    (ResidueField.map (completedStalkMapAt f U hU y q)).comp
        (ResidueField.map (algebraMap R Rhat)) =
      (ResidueField.map (algebraMap T That)).comp
        (ResidueField.map
          (stalkMapAt f (branchPoint f U hU y q) y.val (branchPoint_map f U hU y q))) := by
  ext a
  obtain ⟨r, rfl⟩ := IsLocalRing.residue_surjective a
  change IsLocalRing.residue That
      (completedStalkMapAt f U hU y q (algebraMap R Rhat r)) =
    IsLocalRing.residue That (algebraMap T That
      (stalkMapAt f (branchPoint f U hU y q) y.val (branchPoint_map f U hU y q) r))
  exact congrArg (IsLocalRing.residue That)
    (completedStalkMapAt_algebraMap f U hU y q r)

end Noetherian

attribute [local instance] completedSourceStalk_noetherian
  AdicCompletion.FiniteSemilocal.baseCompletion_domain

section Regular

variable [IsRegularLocalRing (Y.presheaf.stalk y.val)]

/-- Injectivity follows from the existing torsion-free completed-factor embedding,
without any domain hypothesis on the source completion. -/
theorem completedStalkMapAt_injective : Function.Injective (completedStalkMapAt f U hU y q) := by
  let : IsNoetherianRing S := IsNoetherianRing.of_finite R S
  let := Scheme.functionFieldMapAlgebra f
  let := stalkFieldAlgebra f U y
  let := stalk_field_scalarTower f U y
  let := stalk_model_scalarTower f U hU y
  let := AdicCompletion.FiniteSemilocal.baseAlgebra R S qh
  exact (completedBranchStalkEquiv f U hU y q).injective.comp
    (AdicCompletion.FiniteSemilocal.base_injective R S Y.functionField X.functionField qh)

variable [IsDomain (AdicCompletion
  (maximalIdeal (X.presheaf.stalk (branchPoint f U hU y q)))
  (X.presheaf.stalk (branchPoint f U hU y q)))]

/-- The field map is the universal lift of the original injective completed map. -/
def completedFractionMapAt : FractionRing Rhat →+* FractionRing That :=
  IsFractionRing.lift (K := FractionRing Rhat)
    (g := (algebraMap That (FractionRing That)).comp (completedStalkMapAt f U hU y q))
    ((IsFractionRing.injective That (FractionRing That)).comp
      (completedStalkMapAt_injective f U hU y q))

theorem completedFractionMapAt_algebraMap (z : Rhat) :
    completedFractionMapAt f U hU y q (algebraMap Rhat (FractionRing Rhat) z) =
      algebraMap That (FractionRing That) (completedStalkMapAt f U hU y q z) :=
  IsFractionRing.lift_algebraMap
    (K := FractionRing Rhat)
    (g := (algebraMap That (FractionRing That)).comp (completedStalkMapAt f U hU y q))
    ((IsFractionRing.injective That (FractionRing That)).comp
      (completedStalkMapAt_injective f U hU y q)) z

/-- The completed fraction-field action is induced by that same original map. -/
@[instance_reducible]
def completedFractionAlgebraAt : Algebra (FractionRing Rhat) (FractionRing That) :=
  (completedFractionMapAt f U hU y q).toAlgebra

attribute [local instance] completedFractionAlgebraAt

theorem completedFraction_scalarTower :
    IsScalarTower Rhat (FractionRing Rhat) (FractionRing That) := by
  apply IsScalarTower.of_algebraMap_eq
  intro z
  exact (completedFractionMapAt_algebraMap f U hU y q z).symm

attribute [local instance] completedFraction_scalarTower

/-- The actual completed source fraction field is a finite extension of the
actual completed target fraction field. -/
theorem completedFraction_finite :
    FiniteDimensional (FractionRing Rhat) (FractionRing That) := by
  let := completedStalk_finite f U hU y q
  exact IsFractionRing.finite_of_finite_algebra Rhat That
    (FractionRing Rhat) (FractionRing That)

/-- The degree is bounded by the original scheme function-field degree. The
bound comes from the full finite algebra, not from counting completed factors. -/
theorem completedFraction_finrank_le :
    let := Scheme.functionFieldMapAlgebra f
    Module.finrank (FractionRing Rhat) (FractionRing That) ≤
      Module.finrank Y.functionField X.functionField := by
  let : IsNoetherianRing S := IsNoetherianRing.of_finite R S
  let := Scheme.functionFieldMapAlgebra f
  let := stalkFieldAlgebra f U y
  let := stalk_field_scalarTower f U y
  let := stalk_model_scalarTower f U hU y
  let := AdicCompletion.FiniteSemilocal.baseAlgebra R S qh
  obtain ⟨j, hj⟩ := AdicCompletion.FiniteSemilocal.exists_branch_embedding
    R S Y.functionField X.functionField qh
  let k := j.comp (completedBranchStalkAlgEquiv f U hU y q).symm.toLinearMap
  have hk : Function.Injective k :=
    hj.comp (completedBranchStalkAlgEquiv f U hU y q).symm.injective
  calc
    Module.finrank (FractionRing Rhat) (FractionRing That) = Module.finrank Rhat That :=
      IsFractionRing.finrank_eq Rhat (FractionRing Rhat) That (FractionRing That)
    _ ≤ Module.finrank Rhat (Fin (Module.finrank Y.functionField X.functionField) → Rhat) :=
      LinearMap.finrank_le_finrank_of_injective hk
    _ = Module.finrank Y.functionField X.functionField := by
      simp only [Module.finrank_pi, Fintype.card_fin]

/-- The original generic fields and the two literal completion fields form the
original commutative square. No independent generic embedding is selected. -/
theorem completedFraction_original_field_square :
    (AdicCompletion.FiniteSemilocal.originalBaseFractionMap T X.functionField).comp
        (Scheme.functionFieldMap f) =
      (completedFractionMapAt f U hU y q).comp
        (AdicCompletion.FiniteSemilocal.originalBaseFractionMap R Y.functionField) := by
  have hs (x : X) (v : Y) (hx : f x = v) (r : Y.presheaf.stalk v) :
      Scheme.functionFieldMap f (algebraMap (Y.presheaf.stalk v) Y.functionField r) =
        algebraMap (X.presheaf.stalk x) X.functionField (stalkMapAt f x v hx r) := by
    subst v
    simpa [stalkMapAt] using Scheme.functionFieldMap_stalk f x r
  apply IsLocalization.ringHom_ext (nonZeroDivisors R)
  ext r
  change AdicCompletion.FiniteSemilocal.originalBaseFractionMap T X.functionField
      (Scheme.functionFieldMap f (algebraMap R Y.functionField r)) =
    completedFractionMapAt f U hU y q
      (AdicCompletion.FiniteSemilocal.originalBaseFractionMap R Y.functionField
        (algebraMap R Y.functionField r))
  rw [hs _ _ (branchPoint_map f U hU y q),
    AdicCompletion.FiniteSemilocal.originalBaseFractionMap_algebraMap,
    AdicCompletion.FiniteSemilocal.originalBaseFractionMap_algebraMap,
    completedFractionMapAt_algebraMap, completedStalkMapAt_algebraMap]

end Regular

/-- Every actual closed source point is an actual branch with its canonical
completed map and the derived degree bound. The domain hypothesis is on that
literal source-stalk completion, and must be discharged by a surface consumer. -/
theorem exists_completedStalkMap_degree [IsRegularLocalRing R]
    (x : X) (hx : IsClosed ({x} : Set X)) (hfx : f x = y.val)
    [IsDomain (AdicCompletion (maximalIdeal (X.presheaf.stalk x)) (X.presheaf.stalk x))] :
    let := Scheme.functionFieldMapAlgebra f
    let C := AdicCompletion (maximalIdeal (X.presheaf.stalk x)) (X.presheaf.stalk x)
    ∃ q : MaximalSpectrum S, branchPoint f U hU y q = x ∧
      ∃ (c : Rhat →+* C) (d : FractionRing Rhat →+* FractionRing C),
        (∀ (n : ℕ) (z : Rhat),
          AdicCompletion.evalₐ (maximalIdeal (X.presheaf.stalk x)) n (c z) =
            Ideal.quotientMap (maximalIdeal (X.presheaf.stalk x) ^ n)
              (stalkMapAt f x y.val hfx) (by
                apply Ideal.map_le_iff_le_comap.mp
                rw [Ideal.map_pow]
                exact Ideal.pow_right_mono (IsLocalRing.map_maximalIdeal_le _) n)
              (AdicCompletion.evalₐ (maximalIdeal R) n z)) ∧
        Function.Injective c ∧
        (letI := c.toAlgebra; Module.Finite Rhat C) ∧
        (∀ z : Rhat, d (algebraMap Rhat (FractionRing Rhat) z) =
          algebraMap C (FractionRing C) (c z)) ∧
        (letI := d.toAlgebra
         FiniteDimensional (FractionRing Rhat) (FractionRing C) ∧
           Module.finrank (FractionRing Rhat) (FractionRing C) ≤
             Module.finrank Y.functionField X.functionField) := by
  let := Scheme.functionFieldMapAlgebra f
  obtain ⟨q, rfl⟩ := exists_branch f U hU y x hx hfx
  exact ⟨q, rfl, completedStalkMapAt f U hU y q, completedFractionMapAt f U hU y q,
    completedStalkMapAt_eval f U hU y q, completedStalkMapAt_injective f U hU y q,
    completedStalk_finite f U hU y q, completedFractionMapAt_algebraMap f U hU y q,
    completedFraction_finite f U hU y q, completedFraction_finrank_le f U hU y q⟩

end AlgebraicGeometry.Scheme.Hom.LocalNormAlgebra
