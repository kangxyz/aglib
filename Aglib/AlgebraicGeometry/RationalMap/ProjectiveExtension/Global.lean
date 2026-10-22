/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.RationalMap.ProjectiveExtension.PrincipalRestriction
public import Aglib.AlgebraicGeometry.Blowup.Extension.FiniteCover
public import Aglib.AlgebraicGeometry.Blowup.UnitLocus.BoundaryCover
public import Aglib.AlgebraicGeometry.ProjectiveSpace.Structure

/-!
# Projective extension from an arbitrary open of a Noetherian scheme

First blow up the complement to obtain schematic density. The original
saturated affine blowup charts make that complement principal. Extend the
original tuple on each such chart, extend the centres, take a finite actual
admissible refinement, and glue using schematic density and separatedness.
The original sections and the structural morphism are retained throughout.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open CategoryTheory CategoryTheory.Limits
open AlgebraicGeometry.ProjectiveSpace.FromSections

universe u v

namespace AlgebraicGeometry.Scheme.RationalCoordinates

variable {R I : Type u} [CommRing R] [Finite I]

/-- Restricting the original tuple uses exactly its pulled global sections. -/
theorem affineTuple_map_restrict {X Y : Scheme.{u}} (q : Y ⟶ X) (U : X.Opens)
    (p : X ⟶ Spec (.of R)) (s : I → Γ(U.toScheme, ⊤)) :
    AffineTuple.map ((q ⁻¹ᵁ U).ι ≫ q ≫ p) ((q ∣_ U).appTop ∘ s) =
      (q ∣_ U) ≫ AffineTuple.map (U.ι ≫ p) s := by
  rw [AffineTuple.map_naturality]
  congr 1
  exact (morphismRestrict_ι_assoc q U p).symm

/-- A finite affine cover on which the protected open is principal supplies
an actual global projective extension. The local centres and maps are
constructed, not assumed as an additional theorem hypothesis. -/
theorem exists_extension_of_principal_affine_cover {X : Scheme.{u}}
    [IsLocallyNoetherian X] (C : X.AffineOpenCover.{v}) [Finite C.I₀]
    (U : X.Opens) [QuasiCompact U.ι] [IsSchemeTheoreticallyDominant U.ι]
    (f : ∀ i, C.X i) (hf : ∀ i, C.f i ⁻¹ᵁ U = PrimeSpectrum.basicOpen (f i))
    (p : X ⟶ Spec (.of R)) (s : I → Γ(U.toScheme, ⊤)) :
    ∃ (Y : Scheme.{u}) (β : Y ⟶ X) (G : Y ⟶ ProjectiveSpace R (Option I)),
      IsProper β ∧ IsIso (β ∣_ U) ∧
      IsSchemeTheoreticallyDominant (β ⁻¹ᵁ U).ι ∧
      G ≫ ProjectiveSpace.toSpec R (Option I) = β ≫ p ∧
      (β ⁻¹ᵁ U).ι ≫ G = (β ∣_ U) ≫ AffineTuple.map (U.ι ≫ p) s := by
  let : ∀ i, IsLocallyNoetherian (Spec (C.X i)) := fun i ↦
    LocallyOfFiniteType.isLocallyNoetherian (C.f i)
  let : ∀ i, IsNoetherianRing (C.X i) := fun i ↦
    isLocallyNoetherian_Spec.mp inferInstance
  have hlocal := fun i ↦ exists_principalRestriction_extension (C.X i)
    (C.f i ⁻¹ᵁ U) (f i) (hf i) (C.f i ≫ p) ((C.f i ∣_ U).appTop ∘ s)
  choose J B F hJ hbase hagree using hlocal
  let : Finite C.openCover.I₀ := inferInstanceAs (Finite C.I₀)
  apply Blowup.exists_extension_of_finite_cover C.openCover U p
    (ProjectiveSpace.toSpec R (Option I)) (AffineTuple.map (U.ι ≫ p) s) J B F hJ
  · intro i
    exact hbase i
  · intro i
    exact (hagree i).trans
      (congrArg (fun k ↦ ((B i).map ∣_ (C.f i ⁻¹ᵁ U)) ≫ k)
        (affineTuple_map_restrict (C.f i) U p s))

/-- Every finite tuple on any prescribed open of a Noetherian scheme extends
into projective space after a proper morphism that is an isomorphism on
that entire open. The source may be nonreduced or reducible, in any dimension.
The proper morphism is the actual composite constructed by finite blowups. -/
theorem exists_projective_extension {X : Scheme.{u}} [IsNoetherian X]
    (U : X.Opens) (p : X ⟶ Spec (.of R)) (s : I → Γ(U.toScheme, ⊤)) :
    ∃ (Y : Scheme.{u}) (β : Y ⟶ X) (G : Y ⟶ ProjectiveSpace R (Option I)),
      IsProper β ∧ IsIso (β ∣_ U) ∧
      IsSchemeTheoreticallyDominant (β ⁻¹ᵁ U).ι ∧
      G ≫ ProjectiveSpace.toSpec R (Option I) = β ≫ p ∧
      (β ⁻¹ᵁ U).ι ≫ G = (β ∣_ U) ≫ AffineTuple.map (U.ι ≫ p) s := by
  classical
  let K := IdealSheafData.vanishingIdeal U.compl
  let B := Blowup.blowupDatum K
  have hsupp : K.support.compl = U := by
    change U.compl.compl = U
    exact TopologicalSpace.Opens.compl_compl U
  let : IsProper B.map := B.isProper_of_isLocallyNoetherian
  let : IsLocallyNoetherian B.Y := LocallyOfFiniteType.isLocallyNoetherian B.map
  let : CompactSpace B.Y := QuasiCompact.compactSpace_of_compactSpace B.map
  let : IsNoetherian B.Y := ⟨⟩
  let V := B.map ⁻¹ᵁ U
  have hV : B.exceptionalComplement = V := congrArg (fun W ↦ B.map ⁻¹ᵁ W) hsupp
  let : IsSchemeTheoreticallyDominant V.ι := by
    rw [← hV]
    exact B.exceptionalComplement_isSchemeTheoreticallyDominant
  have hBU : IsIso (B.map ∣_ U) := B.restrict_isIso_of_disjoint U (by
    change Disjoint (U : Set X) (U.compl : Set X)
    exact Set.disjoint_left.mpr (fun _ hx hnot ↦ hnot hx))
  obtain ⟨t, ht⟩ := Blowup.BoundaryCover.exists_finite_cover_of_isNoetherian K B
  choose idx hidx hcover using ht
  let C : B.Y.AffineOpenCover := {
    I₀ := {k // k ∈ t}
    X := fun k ↦ Blowup.BoundaryCover.ring K k.val
    f := fun k ↦ Blowup.BoundaryCover.chart K B k.val
    idx := fun y ↦ ⟨idx y, hidx y⟩
    covers := hcover }
  let f : ∀ i, C.X i := fun i ↦ algebraMap Γ(X, i.val.1) (C.X i) i.val.2
  have hf : ∀ i, C.f i ⁻¹ᵁ V = PrimeSpectrum.basicOpen (f i) := by
    intro i
    have h := Blowup.BoundaryCover.chart_preimage_complement K B i.val
    rw [hsupp, Scheme.Hom.comp_preimage] at h
    exact h
  obtain ⟨Y, β, G, hβ, hβU, hd, hGp, hG⟩ :=
    exists_extension_of_principal_affine_cover C V f hf (B.map ≫ p)
      ((B.map ∣_ U).appTop ∘ s)
  let : IsProper β := hβ
  refine ⟨Y, β ≫ B.map, G, inferInstance, ?_, hd, ?_, ?_⟩
  · rw [morphismRestrict_comp]
    exact IsIso.comp_isIso' hβU hBU
  · exact hGp.trans (Category.assoc β B.map p).symm
  · change (β ⁻¹ᵁ V).ι ≫ G = ((β ≫ B.map) ∣_ U) ≫ _
    rw [hG, morphismRestrict_comp]
    exact congrArg (fun k ↦ (β ∣_ V) ≫ k) (affineTuple_map_restrict B.map U p s)

end AlgebraicGeometry.Scheme.RationalCoordinates
