/-
Copyright (c) 2026 kangxyz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.RingTheory.Henselian.HenselizationFiniteLocalPoint

/-!
# The selected finite local factor is the actual henselization

Both maps are constructed from actual local universal maps and localization
lifts. Their inverses are verified by the henselization uniqueness property
and tensor/localization extensionality. The original henselization is then
finite over the henselized base, with its explicit induced base action.
-/

@[expose] public noncomputable section

open IsLocalRing
open scoped TensorProduct

universe u v w

namespace Henselization

/-- Uniqueness in the proved local universal property, as an extensionality lemma. -/
lemma local_algHom_ext
    (R : Type u) [CommRing R] [IsLocalRing R]
    (T : Type w) [CommRing T] [HenselianLocalRing T] [Algebra R T]
    [IsLocalHom (algebraMap R T)]
    (f g : Henselization R →ₐ[R] T)
    [IsLocalHom f.toRingHom] [IsLocalHom g.toRingHom] : f = g := by
  obtain ⟨h, hh, hu⟩ := existsUnique_local_algHom R T
  exact (hu f inferInstance).trans (hu g inferInstance).symm

namespace FiniteLocalFactor

variable (R : Type u) [CommRing R] [IsLocalRing R]
  (B : Type v) [CommRing B] [Algebra R B] [Module.Finite R B]
  (q : Ideal B) [q.IsMaximal]

local notation "S" => Localization.AtPrime q
local notation "H" => Henselization R
local notation "T" => H ⊗[R] B
local notation "C" => SelectedRing R B q
local notation "HS" => Henselization S

lemma residuePoint_surjective : Function.Surjective (residuePoint R B q) := by
  intro z
  obtain ⟨t, ht⟩ := point_surjective R B q z
  exact ⟨algebraMap T C t, (residuePoint_algebraMap R B q t).trans ht⟩

instance residuePoint_isLocalHom : IsLocalHom (residuePoint R B q).toRingHom :=
  IsLocalHom.of_surjective _ (residuePoint_surjective R B q)

instance selected_base_isLocalHom : IsLocalHom (algebraMap H C) := by
  apply ((IsLocalRing.local_hom_TFAE (algebraMap H C)).out 5 1).mp
  exact IsLocalRing.eq_maximalIdeal
    (Ideal.isMaximal_under_of_isIntegral_of_isMaximal (R := H) (maximalIdeal C))

instance selected_original_isLocalHom : IsLocalHom (algebraMap R C) := by
  rw [IsScalarTower.algebraMap_eq R H C]
  infer_instance

/-- The canonical original-local-ring action, defined by the actual source map. -/
instance sourceAlgebra : Algebra S C := (sourceMap R B q).toRingHom.toAlgebra

instance sourceTower : IsScalarTower R S C :=
  IsScalarTower.of_algebraMap_eq fun r => ((sourceMap R B q).commutes r).symm

instance source_algebraMap_isLocalHom : IsLocalHom (algebraMap S C) :=
  sourceMap_isLocalHom R B q

/-- The target henselization retains the actual original R-action through B_q. -/
instance targetAlgebra : Algebra R HS := Algebra.compHom HS (algebraMap R S)

instance targetTower : IsScalarTower R S HS := IsScalarTower.of_algebraMap_eq' rfl

instance target_original_isLocalHom : IsLocalHom (algebraMap R HS) := by
  rw [IsScalarTower.algebraMap_eq R S HS]
  infer_instance

instance source_residue_isLocalHom : IsLocalHom (algebraMap R (ResidueField S)) := by
  rw [IsScalarTower.algebraMap_eq R S (ResidueField S)]
  change IsLocalHom ((IsLocalRing.residue S).comp (algebraMap R S))
  infer_instance

/-- The actual local universal map from the desired henselization to the factor. -/
def forward : HS →ₐ[S] C := Classical.choose (existsUnique_local_algHom S C)

instance forward_isLocalHom : IsLocalHom (forward R B q).toRingHom :=
  (Classical.choose_spec (existsUnique_local_algHom S C)).1

/-- The actual local universal map on the henselized base. -/
def baseLift : H →ₐ[R] HS := Classical.choose (existsUnique_local_algHom R HS)

instance baseLift_isLocalHom : IsLocalHom (baseLift R B q).toRingHom :=
  (Classical.choose_spec (existsUnique_local_algHom R HS)).1

/-- The original-source residue map on its actual henselization. -/
def targetResidue : HS →ₐ[R] ResidueField S := (Henselization.residue S).restrictScalars R

instance targetResidue_isLocalHom : IsLocalHom (targetResidue R B q).toRingHom :=
  Henselization.residue_isLocalHom S

/-- The left factor of the selected tensor residue point. -/
def leftPoint : H →ₐ[R] ResidueField S :=
  (IsScalarTower.toAlgHom R (ResidueField R) (ResidueField S)).comp (Henselization.residue R)

instance leftPoint_isLocalHom : IsLocalHom (leftPoint R B q).toRingHom := by
  change IsLocalHom ((IsScalarTower.toAlgHom R (ResidueField R) (ResidueField S)).toRingHom.comp
    (Henselization.residue R).toRingHom)
  infer_instance

lemma targetResidue_comp_baseLift :
    (targetResidue R B q).comp (baseLift R B q) = leftPoint R B q := by
  let : IsLocalHom ((targetResidue R B q).comp (baseLift R B q)).toRingHom := by
    change IsLocalHom ((targetResidue R B q).toRingHom.comp (baseLift R B q).toRingHom)
    infer_instance
  apply Henselization.local_algHom_ext R (ResidueField S)

/-- The inverse on the original tensor algebra before localization. -/
def backwardTensor : T →ₐ[R] HS := Algebra.TensorProduct.lift
  (baseLift R B q)
  (((Algebra.ofId S HS).restrictScalars R).comp (IsScalarTower.toAlgHom R B S))
  (fun _ _ => .all _ _)

@[simp] lemma backwardTensor_tmul_one (h : H) :
    backwardTensor R B q (h ⊗ₜ[R] 1) = baseLift R B q h := by
  simp [backwardTensor]

@[simp] lemma backwardTensor_one_tmul (b : B) :
    backwardTensor R B q (1 ⊗ₜ[R] b) = algebraMap S HS (algebraMap B S b) := by
  simpa [backwardTensor] using IsScalarTower.algebraMap_apply B S HS b

lemma targetResidue_comp_backwardTensor :
    (targetResidue R B q).comp (backwardTensor R B q) = point R B q := by
  apply Algebra.TensorProduct.ext
  · apply AlgHom.ext
    intro h
    change targetResidue R B q (backwardTensor R B q (h ⊗ₜ[R] 1)) =
      point R B q (h ⊗ₜ[R] 1)
    rw [backwardTensor_tmul_one]
    simpa only [point, Algebra.TensorProduct.lift_tmul, map_one, mul_one,
      leftPoint, AlgHom.comp_apply] using
      AlgHom.congr_fun (targetResidue_comp_baseLift R B q) h
  · apply AlgHom.ext
    intro b
    change targetResidue R B q (backwardTensor R B q (1 ⊗ₜ[R] b)) =
      point R B q (1 ⊗ₜ[R] b)
    rw [backwardTensor_one_tmul, point_one_tmul]
    change Henselization.residue S (algebraMap S HS (algebraMap B S b)) =
      algebraMap B (ResidueField S) b
    rw [(Henselization.residue S).commutes]
    rfl

lemma backwardTensor_isUnit (t : (pointIdeal R B q).primeCompl) :
    IsUnit (backwardTensor R B q t) := by
  apply Henselization.isUnit_of_residue_ne_zero S
  have heq := AlgHom.congr_fun (targetResidue_comp_backwardTensor R B q) t
  change Henselization.residue S (backwardTensor R B q t) = point R B q t at heq
  rw [heq]
  exact t.property

/-- The actual inverse map from the selected factor. -/
def backward : C →ₐ[R] HS := IsLocalization.liftAlgHom (backwardTensor_isUnit R B q)

@[simp] lemma backward_algebraMap (t : T) :
    backward R B q (algebraMap T C t) = backwardTensor R B q t :=
  IsLocalization.lift_eq _ _

lemma targetResidue_comp_backward :
    (targetResidue R B q).comp (backward R B q) = residuePoint R B q := by
  apply IsLocalization.algHom_ext (pointIdeal R B q).primeCompl
  apply AlgHom.ext
  intro t
  change targetResidue R B q (backward R B q (algebraMap T C t)) =
    residuePoint R B q (algebraMap T C t)
  rw [backward_algebraMap, residuePoint_algebraMap]
  exact AlgHom.congr_fun (targetResidue_comp_backwardTensor R B q) t

instance backward_isLocalHom : IsLocalHom (backward R B q).toRingHom := by
  constructor
  intro c hc
  apply (isUnit_map_iff (residuePoint R B q).toRingHom c).mp
  have hu := hc.map (targetResidue R B q).toRingHom
  have heq := AlgHom.congr_fun (targetResidue_comp_backward R B q) c
  change IsUnit (targetResidue R B q (backward R B q c)) at hu
  change targetResidue R B q (backward R B q c) = residuePoint R B q c at heq
  rw [heq] at hu
  exact hu

lemma backward_comp_sourceMap :
    (backward R B q).comp (sourceMap R B q) = (Algebra.ofId S HS).restrictScalars R := by
  apply IsLocalization.algHom_ext q.primeCompl
  apply AlgHom.ext
  intro b
  change backward R B q (sourceMap R B q (algebraMap B S b)) =
    algebraMap S HS (algebraMap B S b)
  rw [sourceMap_algebraMap]
  change backward R B q (algebraMap T C (1 ⊗ₜ[R] b)) = _
  rw [backward_algebraMap]
  exact backwardTensor_one_tmul R B q b

/-- The inverse preserves the original B_q-algebra action, not just the R-action. -/
def backwardOverSource : C →ₐ[S] HS :=
  { (backward R B q).toRingHom with
    commutes' s := AlgHom.congr_fun (backward_comp_sourceMap R B q) s }

instance backwardOverSource_isLocalHom : IsLocalHom (backwardOverSource R B q).toRingHom :=
  backward_isLocalHom R B q

lemma forward_comp_baseLift :
    ((forward R B q).restrictScalars R).comp (baseLift R B q) =
      (Algebra.ofId H C).restrictScalars R := by
  let : IsLocalHom ((Algebra.ofId H C).restrictScalars R).toRingHom := by
    change IsLocalHom (algebraMap H C)
    infer_instance
  let : IsLocalHom
      (((forward R B q).restrictScalars R).comp (baseLift R B q)).toRingHom := by
    change IsLocalHom ((forward R B q).toRingHom.comp (baseLift R B q).toRingHom)
    infer_instance
  apply Henselization.local_algHom_ext R C

lemma forward_comp_backward :
    ((forward R B q).restrictScalars R).comp (backward R B q) = AlgHom.id R C := by
  apply IsLocalization.algHom_ext (pointIdeal R B q).primeCompl
  apply Algebra.TensorProduct.ext
  · apply AlgHom.ext
    intro h
    change forward R B q (backward R B q (algebraMap T C (h ⊗ₜ[R] 1))) =
      algebraMap T C (h ⊗ₜ[R] 1)
    rw [backward_algebraMap, backwardTensor_tmul_one]
    change forward R B q (baseLift R B q h) = algebraMap H C h
    exact AlgHom.congr_fun (forward_comp_baseLift R B q) h
  · apply AlgHom.ext
    intro b
    change forward R B q (backward R B q (algebraMap T C (1 ⊗ₜ[R] b))) =
      algebraMap T C (1 ⊗ₜ[R] b)
    rw [backward_algebraMap, backwardTensor_one_tmul]
    change forward R B q (algebraMap S HS (algebraMap B S b)) = rightMap R B q b
    rw [(forward R B q).commutes]
    exact sourceMap_algebraMap R B q b

lemma backwardOverSource_comp_forward :
    (backwardOverSource R B q).comp (forward R B q) = AlgHom.id S HS := by
  let : IsLocalHom (AlgHom.id S HS).toRingHom := by
    change IsLocalHom (RingHom.id HS)
    infer_instance
  let : IsLocalHom ((backwardOverSource R B q).comp (forward R B q)).toRingHom := by
    change IsLocalHom ((backwardOverSource R B q).toRingHom.comp (forward R B q).toRingHom)
    infer_instance
  apply Henselization.local_algHom_ext S HS

/-- The actual henselization is the specified actual finite local tensor factor. -/
def equiv : HS ≃ₐ[S] C := AlgEquiv.ofAlgHom (forward R B q) (backwardOverSource R B q)
  (by
    apply AlgHom.ext
    intro c
    exact AlgHom.congr_fun (forward_comp_backward R B q) c)
  (backwardOverSource_comp_forward R B q)

@[simp] lemma equiv_baseLift (h : H) :
    equiv R B q (baseLift R B q h) = algebraMap H C h :=
  AlgHom.congr_fun (forward_comp_baseLift R B q) h

/-- The actual induced henselized-base action on the desired henselization. -/
instance targetHenselizedBaseAlgebra : Algebra H HS := (baseLift R B q).toRingHom.toAlgebra

instance targetHenselizedBaseTower : IsScalarTower R H HS :=
  IsScalarTower.of_algebraMap_eq fun r => ((baseLift R B q).commutes r).symm

/-- The same actual equivalence respects the induced henselized-base action. -/
def equivOverBase : HS ≃ₐ[H] C :=
  { (equiv R B q).toRingEquiv with commutes' := equiv_baseLift R B q }

/-- The actual henselization of the original finite-algebra local ring is finite
 over the actual henselization of the base, with its canonical local action. -/
theorem finite_henselization : Module.Finite H HS :=
  Module.Finite.of_surjective (equivOverBase R B q).symm.toLinearMap
    (equivOverBase R B q).symm.surjective

end FiniteLocalFactor
end Henselization
