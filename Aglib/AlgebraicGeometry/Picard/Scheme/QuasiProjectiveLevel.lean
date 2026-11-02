/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.Morphisms.OpenImmersion.CompactFactorization
public import Aglib.AlgebraicGeometry.Picard.Representability.FineStrata

/-!
# Quasi-projective levels on a chosen Picard representative

For a flat, geometrically integral closed subscheme of finite projective space over a Noetherian
ring, the coarse-condition opens on any given locally Noetherian fppf Picard representative are
H-quasi-projective. The comparison uses the native representing isomorphism and identifies the
whole fibre-condition open by inverse image before applying it to the levels. Thus no second
Picard representative is selected at a consumer boundary.

A compact-image immersion into an Euler-polynomial stratum factors through one increasing level
and is H-quasi-projective over the original base. The current consumer is the proper identity
component of the Picard scheme of a curve over an algebraically closed field.
-/

@[expose] public section

noncomputable section

universe u

open CategoryTheory CategoryTheory.Limits Opposite AlgebraicGeometry
open AlgebraicGeometry.ProjectiveSpace

namespace AlgebraicGeometry.Scheme.RelativePicard

namespace FiberCondition

variable {S X : Scheme.{u}} {p : X ⟶ S} (C : FiberCondition p)
  {P Q : LocallyNoetherianOver S}
  (R : ((locallyNoetherianOverInclusion S).op ⋙ (fppfPicardSheaf p).obj ⋙
    CategoryTheory.forget AddCommGrpCat.{u + 1}).RepresentableBy P)
  (R' : ((locallyNoetherianOverInclusion S).op ⋙ (fppfPicardSheaf p).obj ⋙
    CategoryTheory.forget AddCommGrpCat.{u + 1}).RepresentableBy Q)

/-- The native representing isomorphism identifies the entire open of a fibre condition,
including its scheme structure as an inverse-image open. -/
theorem preimage_opens_uniqueUpToIso :
    (R.uniqueUpToIso R').hom.hom.left ⁻¹ᵁ C.opens (T := Q.obj) (R'.homEquiv (𝟙 Q)) =
      C.opens (T := P.obj) (R.homEquiv (𝟙 P)) := by
  have h : R'.homEquiv (R.uniqueUpToIso R').hom = R.homEquiv (𝟙 P) := by
    change R'.homEquiv (R'.homEquiv.symm (R.homEquiv (𝟙 P))) = R.homEquiv (𝟙 P)
    exact Equiv.apply_symm_apply _ _
  have hmap : (fppfPicardSheaf p).obj.map (R.uniqueUpToIso R').hom.hom.op
      (R'.homEquiv (𝟙 Q)) = R.homEquiv (𝟙 P) := by
    have hm := R'.homEquiv_comp (R.uniqueUpToIso R').hom (𝟙 Q)
    rw [Category.comp_id] at hm
    exact hm.symm.trans h
  ext x
  change C.HoldsAt (R'.homEquiv (𝟙 Q)) ((R.uniqueUpToIso R').hom.hom.left x) ↔
    C.HoldsAt (R.homEquiv (𝟙 P)) x
  rw [← hmap]
  exact (C.holdsAt_map (R.uniqueUpToIso R').hom.hom (R'.homEquiv (𝟙 Q)) x).symm

end FiberCondition

open Strata

variable {A : Type u} [CommRing A] [IsNoetherianRing A] {ι : Type u} {X : Scheme.{u}}
  (i : X ⟶ ProjectiveSpace A ι) [IsClosedImmersion i] [Flat (i ≫ toSpec A ι)]
  [GeometricallyIntegral (i ≫ toSpec A ι)] {N : ℕ} (e : ι ≃ Fin (N + 1))
  (P : LocallyNoetherianOver (Spec (.of A)))
  (R : ((locallyNoetherianOverInclusion (Spec (.of A))).op ⋙
    (fppfPicardSheaf (i ≫ toSpec A ι)).obj ⋙
      CategoryTheory.forget AddCommGrpCat.{u + 1}).RepresentableBy P)

/-- Each coarse-condition level is H-quasi-projective on the supplied Picard representative.
The fine-stratum representability and rank-finiteness premises are discharged by `FineStrata`.
-/
theorem isHQuasiProjective_opens_coarseCondition (φ : Polynomial ℚ) (m : ℤ) :
    IsHQuasiProjective
      (((coarseCondition i N e φ m).opens (T := P.obj) (R.homEquiv (𝟙 P))).ι ≫ P.obj.hom) := by
  let h := fineStrataRepresentableByHQuasiProjective i e
  let Q := picardScheme h
  let R' := picardSchemeRepresentableBy h
  let a : P ≅ Q := R.uniqueUpToIso R'
  have : IsIso a.hom.hom.left := by
    change IsIso ((locallyNoetherianOverInclusion (Spec (.of A)) ⋙
      Over.forget (Spec (.of A))).map a.hom)
    infer_instance
  let V := picardLevelOpens h φ m
  have hV : a.hom.hom.left ⁻¹ᵁ V =
      (coarseCondition i N e φ m).opens (T := P.obj) (R.homEquiv (𝟙 P)) := by
    simpa only [a, V, R', picardLevelOpens, picardSchemeRepresentableBy_homEquiv_id] using
      (coarseCondition i N e φ m).preimage_opens_uniqueUpToIso R R'
  have : IsHQuasiProjective (V.ι ≫ Q.obj.hom) :=
    isHQuasiProjective_picardLevelOpens_of_finiteFineStrataRanks h
      (finiteFineStrataRanks i e) φ m
  rw [← hV]
  have hrestrict : IsImmersion ((a.hom.hom.left ∣_ V) ≫ V.ι) := by
    rw [morphismRestrict_ι]
    infer_instance
  have : IsImmersion (a.hom.hom.left ∣_ V) :=
    IsImmersion.of_comp _ V.ι
  have hqp := IsHQuasiProjective.comp_of_isImmersion (a.hom.hom.left ∣_ V)
    (V.ι ≫ Q.obj.hom)
  convert hqp using 1
  rw [← Category.assoc, morphismRestrict_ι, Category.assoc, Over.w a.hom.hom]

/-- A compact-image immersion into one Euler-polynomial stratum of the chosen Picard scheme
is H-quasi-projective: its original morphism factors through one increasing coarse level. -/
theorem isHQuasiProjective_comp_of_isCompact_range_of_range_subset_eulerCondition
    {Y : Scheme.{u}} (j : Y ⟶ P.obj.left) [IsImmersion j]
    (hcompact : IsCompact (Set.range j)) (φ : Polynomial ℚ)
    (hstratum : Set.range j ⊆
      (eulerCondition i N e φ).opens (T := P.obj) (R.homEquiv (𝟙 P))) :
    IsHQuasiProjective (j ≫ P.obj.hom) := by
  let U : ℤ → P.obj.left.Opens :=
    fun m => (coarseCondition i N e φ m).opens (T := P.obj) (R.homEquiv (𝟙 P))
  have hU : Monotone U := fun _ _ h =>
    opens_coarseCondition_mono (T := P.obj) (R.homEquiv (𝟙 P)) φ h
  have hcover : Set.range j ⊆ (⨆ m, U m : P.obj.left.Opens) := by
    rw [show (⨆ m, U m) =
        (eulerCondition i N e φ).opens (T := P.obj) (R.homEquiv (𝟙 P)) from
      iSup_opens_coarseCondition (T := P.obj) (R.homEquiv (𝟙 P)) φ]
    exact hstratum
  obtain ⟨m, g, hg, -⟩ := j.exists_lift_opens_of_isCompact_range U
    (fun m n => ⟨max m n, hU (le_max_left _ _), hU (le_max_right _ _)⟩) hcompact hcover
  have : IsImmersion (g ≫ (U m).ι) := by
    rw [hg]
    infer_instance
  have : IsImmersion g := IsImmersion.of_comp g (U m).ι
  have : IsHQuasiProjective ((U m).ι ≫ P.obj.hom) :=
    isHQuasiProjective_opens_coarseCondition i e P R φ m
  have hqp := IsHQuasiProjective.comp_of_isImmersion g ((U m).ι ≫ P.obj.hom)
  simpa only [← Category.assoc, hg] using hqp

end AlgebraicGeometry.Scheme.RelativePicard
