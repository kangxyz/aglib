/-
Copyright (c) 2026 algebraic-geometry contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.ProjectiveSpace.SectionExtension.Overlap
public import Aglib.AlgebraicGeometry.Modules.Invertible.Gluing.Morphisms

/-!
# Extending a local section by an actual negative-twist morphism

Over a finite projective coordinate cover, clearing denominators and correcting overlap
torsion produce compatible local target sections. The original internal-Hom sheaf glues
them into an actual map `O(-N) ⟶ M`. Its restriction to the distinguished chart is exactly
multiplication by the original section in the standard frame. No Noetherian or finite-type
hypothesis on the quasicoherent coefficient is required.
-/

@[expose] public section

noncomputable section

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open CategoryTheory Opposite
open AlgebraicGeometry.Scheme.Modules.Invertible

universe u

namespace AlgebraicGeometry.ProjectiveSpace

variable (R : Type u) [CommRing R] (ι : Type u)
  (M : (ProjectiveSpace R ι).Modules)

/-- Original overlap transition equations remain unchanged on every common subopen. -/
theorem coordinateNumerators_compatible_restrict (N : ℕ)
    (t : ∀ j, Γ(M, coordinateOpen R ι j))
    (ht : ∀ j k,
      let W := coordinateOpen R ι j ⊓ coordinateOpen R ι k
      M.presheaf.map (homOfLE (inf_le_right : W ≤ coordinateOpen R ι k)).op (t k) =
        (coordinateTransitionOn R ι j k (V := W) inf_le_left inf_le_right ^ N).val •
          M.presheaf.map (homOfLE (inf_le_left : W ≤ coordinateOpen R ι j)).op (t j))
    (j k : ι) (V : (ProjectiveSpace R ι).Opens)
    (hj : V ≤ coordinateOpen R ι j) (hk : V ≤ coordinateOpen R ι k) :
    M.presheaf.map (homOfLE hk).op (t k) =
      (coordinateTransitionOn R ι j k hj hk ^ N).val •
        M.presheaf.map (homOfLE hj).op (t j) := by
  let W := coordinateOpen R ι j ⊓ coordinateOpen R ι k
  let hVW : V ≤ W := le_inf hj hk
  have h := congrArg (M.presheaf.map (homOfLE hVW).op) (ht j k)
  rw [Scheme.Modules.map_smul] at h
  have hu : (ProjectiveSpace R ι).presheaf.map (homOfLE hVW).op
      ((coordinateTransitionOn R ι j k (V := W) inf_le_left inf_le_right ^ N).val) =
    (coordinateTransitionOn R ι j k hj hk ^ N).val :=
    coordinateTransitionOn_pow_restrict R ι j k N hVW inf_le_left inf_le_right
  rw [hu] at h
  have hleft : M.presheaf.map (homOfLE hVW).op
      (M.presheaf.map (homOfLE (inf_le_right : W ≤ coordinateOpen R ι k)).op (t k)) =
      M.presheaf.map (homOfLE hk).op (t k) :=
    (M.presheaf.map_comp_apply
      (homOfLE (inf_le_right : W ≤ coordinateOpen R ι k)).op (homOfLE hVW).op (t k)).symm
  have hright : M.presheaf.map (homOfLE hVW).op
      (M.presheaf.map (homOfLE (inf_le_left : W ≤ coordinateOpen R ι j)).op (t j)) =
      M.presheaf.map (homOfLE hj).op (t j) :=
    (M.presheaf.map_comp_apply
      (homOfLE (inf_le_left : W ≤ coordinateOpen R ι j)).op (homOfLE hVW).op (t j)).symm
  rw [hleft, hright] at h
  exact h

variable [M.IsQuasicoherent] [Finite ι]

/-- Every local section admits actual compatible target coefficients for a negative twist,
with the original section retained on its distinguished chart. -/
theorem exists_coordinateCompatibleNumerators (i : ι)
    (s : Γ(M, coordinateOpen R ι i)) :
    ∃ (N : ℕ) (t : ∀ j, Γ(M, coordinateOpen R ι j)), t i = s ∧
      ∀ (j k : ι) (V : (ProjectiveSpace R ι).Opens)
        (hj : V ≤ coordinateOpen R ι j) (hk : V ≤ coordinateOpen R ι k),
        M.presheaf.map (homOfLE hk).op (t k) =
          (coordinateTransitionOn R ι j k hj hk ^ N).val •
            M.presheaf.map (homOfLE hj).op (t j) := by
  obtain ⟨N, t, ht⟩ := exists_coordinateChartNumerators R ι M i s
  obtain ⟨K, hK⟩ := exists_coordinateNumeratorCorrection R ι M i N s t ht
  have hti : t i = s := by
    simpa [sectionRestrict] using coordinateChartNumerator_restrict R ι M i i N s
      (t i) (ht i) (coordinateOpen R ι i) le_rfl le_rfl
  refine ⟨N + K, fun j => coordinateRatioSection R ι j i ^ K • t j, ?_, ?_⟩
  · simp only [coordinateRatioSection_self, one_pow, one_smul, hti]
  · exact coordinateNumerators_compatible_restrict R ι M (N + K) _ hK

/-- A local section of an arbitrary quasicoherent module on finite-coordinate projective
space extends to an actual map from a negative twist. On every subopen of the original chart,
the map is precisely multiplication by the original restricted section in the standard frame. -/
theorem exists_negativeTwistHom_of_section (i : ι)
    (s : Γ(M, coordinateOpen R ι i)) :
    ∃ (N : ℕ) (φ : twistingSheaf R ι (-(N : ℤ)) ⟶ M),
      ∀ (V : (ProjectiveSpace R ι).Opens) (hi : V ≤ coordinateOpen R ι i)
        (x : Γ(twistingSheaf R ι (-(N : ℤ)), V)),
        φ.val.app (op V) x = twistingSectionsEquiv R ι (-(N : ℤ)) i hi x •
          M.presheaf.map (homOfLE hi).op s := by
  obtain ⟨N, t, hti, ht⟩ := exists_coordinateCompatibleNumerators R ι M i s
  let c := (coordinateUnitCocycle R ι).zpow (-(-(N : ℤ)))
  have hc : ∀ (j k : ι) (V : (ProjectiveSpace R ι).Opens)
      (hj : V ≤ coordinateOpen R ι j) (hk : V ≤ coordinateOpen R ι k),
      M.val.map (homOfLE hk).op (t k) =
        (c.transitionOn j k hj hk).val • M.val.map (homOfLE hj).op (t j) := by
    intro j k V hj hk
    change M.presheaf.map (homOfLE hk).op (t k) =
      (c.transitionOn j k hj hk).val • M.presheaf.map (homOfLE hj).op (t j)
    simpa only [c, UnitCocycle.zpow_transitionOn, coordinateUnitCocycle_transitionOn,
      neg_neg, zpow_natCast] using ht j k V hj hk
  let φ : twistingSheaf R ι (-(N : ℤ)) ⟶ M :=
    c.homOfLocalSections M (iSup_coordinateOpen_eq_top R ι) t hc
  refine ⟨N, φ, ?_⟩
  intro V hi x
  change (c.homOfLocalSections M (iSup_coordinateOpen_eq_top R ι) t hc).val.app (op V) x =
    c.localSectionsEquiv i hi x • M.val.map (homOfLE hi).op s
  rw [c.homOfLocalSections_apply M (iSup_coordinateOpen_eq_top R ι) t hc i V hi x, hti]

/-- In particular, the extension sends the actual standard local generator to the original
section, with no scalar rescaling. -/
theorem exists_negativeTwistHom_generator (i : ι)
    (s : Γ(M, coordinateOpen R ι i)) :
    ∃ (N : ℕ) (φ : twistingSheaf R ι (-(N : ℤ)) ⟶ M),
      φ.val.app (op (coordinateOpen R ι i))
        ((twistingSectionsEquiv R ι (-(N : ℤ)) i le_rfl).symm 1) = s := by
  obtain ⟨N, φ, hφ⟩ := exists_negativeTwistHom_of_section R ι M i s
  refine ⟨N, φ, ?_⟩
  simpa using hφ (coordinateOpen R ι i) le_rfl
    ((twistingSectionsEquiv R ι (-(N : ℤ)) i le_rfl).symm 1)

end AlgebraicGeometry.ProjectiveSpace
