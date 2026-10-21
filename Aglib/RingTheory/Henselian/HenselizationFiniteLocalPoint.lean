/-
Copyright (c) 2026 kangxyz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.RingTheory.Henselian.FiniteAlgebraHenselian
public import Aglib.RingTheory.Henselian.HenselizationUniversal
public import Mathlib.RingTheory.TensorProduct.Finite

/-!
# The selected finite local factor after henselization

For a finite algebra B over a local ring R and a specified maximal ideal q,
the residue field of B_q specifies an actual maximal ideal in R^h tensor B.
Its localization is finite and Henselian over R^h, and receives the actual
local map from B_q. The henselization equivalence is a subsequent theorem.
-/

@[expose] public noncomputable section

open IsLocalRing
open scoped TensorProduct

universe u v

namespace Henselization.FiniteLocalFactor

variable (R : Type u) [CommRing R] [IsLocalRing R]
  (B : Type v) [CommRing B] [Algebra R B] [Module.Finite R B]
  (q : Ideal B) [q.IsMaximal]

/-- The original local base map at the chosen finite-algebra point. -/
instance source_isLocalHom : IsLocalHom (algebraMap R (Localization.AtPrime q)) := by
  constructor
  intro r hr
  apply IsLocalRing.notMem_maximalIdeal.mp
  have hq : q.comap (algebraMap R B) = maximalIdeal R :=
    IsLocalRing.eq_maximalIdeal
      (Ideal.isMaximal_under_of_isIntegral_of_isMaximal (R := R) q)
  have hnot : algebraMap R B r ∉ q := by
    apply (IsLocalization.AtPrime.isUnit_to_map_iff (Localization.AtPrime q) q _).mp
    simpa only [← IsScalarTower.algebraMap_apply R B (Localization.AtPrime q)] using hr
  intro hm
  apply hnot
  change r ∈ q.comap (algebraMap R B)
  rwa [hq]

/-- The chosen residue point of the actual tensor algebra. -/
def point : Henselization R ⊗[R] B →ₐ[R] ResidueField (Localization.AtPrime q) :=
  Algebra.TensorProduct.lift
    ((IsScalarTower.toAlgHom R (ResidueField R) (ResidueField (Localization.AtPrime q))).comp
      (Henselization.residue R))
    (IsScalarTower.toAlgHom R B (ResidueField (Localization.AtPrime q)))
    (fun _ _ => .all _ _)

@[simp] lemma point_one_tmul (b : B) :
    point R B q (1 ⊗ₜ[R] b) = algebraMap B (ResidueField (Localization.AtPrime q)) b := by
  simp [point]

/-- Surjectivity uses maximality of the original q, not a residue separability assumption. -/
lemma point_surjective : Function.Surjective (point R B q) := by
  intro y
  let E := IsLocalization.AtPrime.equivQuotMaximalIdeal q (Localization.AtPrime q)
  obtain ⟨b, hb⟩ := Ideal.Quotient.mk_surjective (E.symm y)
  refine ⟨1 ⊗ₜ[R] b, ?_⟩
  rw [point_one_tmul]
  change E (Ideal.Quotient.mk q b) = y
  rw [hb]
  exact E.apply_symm_apply y

/-- The specified tensor prime is the kernel of its actual residue point. -/
def pointIdeal : Ideal (Henselization R ⊗[R] B) := RingHom.ker (point R B q).toRingHom

instance pointIdeal_isMaximal : (pointIdeal R B q).IsMaximal :=
  RingHom.ker_isMaximal_of_surjective (point R B q) (point_surjective R B q)

lemma point_one_tmul_eq_zero_iff (b : B) : point R B q (1 ⊗ₜ[R] b) = 0 ↔ b ∈ q := by
  rw [point_one_tmul]
  change IsLocalRing.residue (Localization.AtPrime q) (algebraMap B (Localization.AtPrime q) b)
    = 0 ↔ b ∈ q
  rw [IsLocalRing.residue_eq_zero_iff,
    IsLocalization.AtPrime.to_map_mem_maximal_iff (Localization.AtPrime q) q b]

/-- The actual chosen local factor, with no abstract factor witness. -/
abbrev SelectedRing := Localization.AtPrime (pointIdeal R B q)

instance selected_finite : Module.Finite (Henselization R) (SelectedRing R B q) :=
  HenselianLocalRing.finite_localizationAtPrime (Henselization R)
    (Henselization R ⊗[R] B) (pointIdeal R B q)

instance selected_henselian : HenselianLocalRing (SelectedRing R B q) :=
  HenselianLocalRing.of_finite_local_algebra (Henselization R) (SelectedRing R B q)

/-- The actual residue point extends to the selected localization. -/
def residuePoint : SelectedRing R B q →ₐ[R] ResidueField (Localization.AtPrime q) :=
  IsLocalization.liftAlgHom (f := point R B q) (fun s : (pointIdeal R B q).primeCompl =>
    isUnit_iff_ne_zero.mpr s.property)

@[simp] lemma residuePoint_algebraMap (t : Henselization R ⊗[R] B) :
    residuePoint R B q (algebraMap (Henselization R ⊗[R] B) (SelectedRing R B q) t) =
      point R B q t := IsLocalization.lift_eq _ _

/-- The original B-map into the selected factor. -/
def rightMap : B →ₐ[R] SelectedRing R B q :=
  (IsScalarTower.toAlgHom R (Henselization R ⊗[R] B) (SelectedRing R B q)).comp
    Algebra.TensorProduct.includeRight

lemma rightMap_isUnit (b : q.primeCompl) : IsUnit (rightMap R B q b) := by
  change IsUnit (algebraMap (Henselization R ⊗[R] B) (SelectedRing R B q) (1 ⊗ₜ[R] (b : B)))
  apply IsLocalization.map_units (SelectedRing R B q)
    (⟨1 ⊗ₜ[R] (b : B), ?_⟩ : (pointIdeal R B q).primeCompl)
  change point R B q (1 ⊗ₜ[R] (b : B)) ≠ 0
  exact fun hz => b.property ((point_one_tmul_eq_zero_iff R B q b).mp hz)

/-- The actual map from the original prime localization to the selected factor. -/
def sourceMap : Localization.AtPrime q →ₐ[R] SelectedRing R B q :=
  IsLocalization.liftAlgHom (rightMap_isUnit R B q)

@[simp] lemma sourceMap_algebraMap (b : B) :
    sourceMap R B q (algebraMap B (Localization.AtPrime q) b) = rightMap R B q b :=
  IsLocalization.lift_eq _ _

/-- The source map preserves the specified residue point literally. -/
lemma residuePoint_comp_sourceMap :
    (residuePoint R B q).comp (sourceMap R B q) =
      (Algebra.ofId (Localization.AtPrime q)
        (ResidueField (Localization.AtPrime q))).restrictScalars R := by
  apply IsLocalization.algHom_ext q.primeCompl
  apply AlgHom.ext
  intro b
  change residuePoint R B q (sourceMap R B q (algebraMap B (Localization.AtPrime q) b)) =
    algebraMap B (ResidueField (Localization.AtPrime q)) b
  rw [sourceMap_algebraMap]
  change residuePoint R B q
    (algebraMap (Henselization R ⊗[R] B) (SelectedRing R B q) (1 ⊗ₜ[R] b)) = _
  rw [residuePoint_algebraMap, point_one_tmul]

instance sourceMap_isLocalHom : IsLocalHom (sourceMap R B q).toRingHom := by
  constructor
  intro s hs
  apply (IsLocalRing.residue_ne_zero_iff_isUnit s).mp
  have hu := hs.map (residuePoint R B q).toRingHom
  have heq := AlgHom.congr_fun (residuePoint_comp_sourceMap R B q) s
  change residuePoint R B q (sourceMap R B q s) =
    IsLocalRing.residue (Localization.AtPrime q) s at heq
  change IsUnit (residuePoint R B q (sourceMap R B q s)) at hu
  rw [heq] at hu
  exact isUnit_iff_ne_zero.mp hu

end Henselization.FiniteLocalFactor
