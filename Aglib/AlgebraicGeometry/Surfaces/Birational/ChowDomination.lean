/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.Morphisms.Proper.Chow.Projective
public import Aglib.AlgebraicGeometry.RationalMap.ProjectiveExtension
public import Mathlib.AlgebraicGeometry.Morphisms.Separated

/-!
# Actual point-blowup domination of the original Chow modification

The inverse over the original dense isomorphism open gives a generic map to
the original projective Chow embedding. Native point principalization extends
that map. Its lift through the original closed immersion follows from a
dominant closed immersion onto a reduced scheme. Separatedness then proves
the original comparison triangle over the source.

The consumer is projective descent along actual point-blowup chains. No
normality or regularity of the Chow modification, and no projectivity of the
original source, is assumed.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits TopologicalSpace

universe u

namespace AlgebraicGeometry.Scheme.Birational

/-- A morphism from a reduced scheme factors through a closed immersion if
its pullback to a dominant source does. Both original triangles are retained. -/
theorem exists_closedImmersion_factor_of_dominant
    {D X W P : Scheme.{u}} [IsReduced X]
    (η : D ⟶ X) [IsDominant η] (h : X ⟶ P) (j : W ⟶ P)
    [IsClosedImmersion j] (aη : D ⟶ W) (H : η ≫ h = aη ≫ j) :
    ∃ a : X ⟶ W, a ≫ j = h ∧ η ≫ a = aη := by
  let p : pullback h j ⟶ X := pullback.fst h j
  let t : D ⟶ pullback h j := pullback.lift η aη H
  have htp : t ≫ p = η := pullback.lift_fst η aη H
  have : IsDominant (t ≫ p) := by rw [htp]; infer_instance
  have : IsDominant p := IsDominant.of_comp t p
  have : Surjective p :=
    surjective_of_isDominant_of_isClosed_range p p.isClosedEmbedding.isClosed_range
  have : IsIso p := isIso_of_isClosedImmersion_of_surjective p
  let a : X ⟶ W := inv p ≫ pullback.snd h j
  have ha : a ≫ j = h := by
    dsimp only [a, p]
    rw [Category.assoc, ← pullback.condition]
    exact IsIso.inv_hom_id_assoc (pullback.fst h j) h
  refine ⟨a, ha, (cancel_mono j).mp ?_⟩
  rw [Category.assoc, ha]
  exact H

variable {Z W : Scheme.{u}} [IsIntegral Z]

/-- The actual generic inverse formed on the supplied dense isomorphism open. -/
def modificationGenericInverse (π : W ⟶ Z) (V : Z.Opens)
    (hV : Dense (V : Set Z)) (hiso : IsIso (π ∣_ V)) :
    Spec Z.functionField ⟶ W :=
  letI := hiso
  V.fromSpecStalkOfMem (genericPoint Z)
      ((genericPoint_spec Z).mem_open_set_iff V.isOpen |>.mpr (by simpa using hV.nonempty)) ≫
    inv (π ∣_ V) ≫ (π ⁻¹ᵁ V).ι

/-- This generic inverse composes to the original generic-point morphism. -/
@[reassoc]
theorem modificationGenericInverse_comp (π : W ⟶ Z) (V : Z.Opens)
    (hV : Dense (V : Set Z)) (hiso : IsIso (π ∣_ V)) :
    modificationGenericInverse π V hV hiso ≫ π = Z.fromSpecStalk (genericPoint Z) := by
  let := hiso
  simp only [modificationGenericInverse, Category.assoc, ← morphismRestrict_ι,
    IsIso.inv_hom_id_assoc, Opens.fromSpecStalkOfMem_ι]

variable {R : Type u} [CommRing R]

/-- Actual point blowups dominate the given closed projective modification.
The comparison, embedding, base and generic triangles use the original maps. -/
theorem exists_pointBlowupChain_dominating_projectiveModification
    [IsNoetherian Z] (hZ : RegularStalks Z) (hd : topologicalKrullDim Z ≤ 2)
    (q : Z ⟶ Spec (.of R)) [IsSeparated q]
    (π : W ⟶ Z) {I : Type u} [Finite I]
    (j : W ⟶ ProjectiveSpace R I) [IsClosedImmersion j]
    (hbase : j ≫ ProjectiveSpace.toSpec R I = π ≫ q)
    (V : Z.Opens) (hV : Dense (V : Set Z)) (hiso : IsIso (π ∣_ V)) :
    ∃ (Y : Scheme.{u}) (β : Y ⟶ Z) (c : Blowup.PointBlowupChain β),
      letI : IsIntegral Y := c.isIntegral inferInstance
      letI : IsDominant β := c.isDominant inferInstance
      ∃ (a : Y ⟶ W) (h : Y ⟶ ProjectiveSpace R I),
        IsProper β ∧ BirationalOver β (𝟙 Z) ∧ IsNoetherian Y ∧ RegularStalks Y ∧
        (∀ y : Y, ringKrullDim (Y.presheaf.stalk y) ≤ 2) ∧
        a ≫ π = β ∧ a ≫ j = h ∧
        h ≫ ProjectiveSpace.toSpec R I = β ≫ q ∧
        a ≫ (π ≫ q) = β ≫ q ∧
        (Y.fromSpecStalk (genericPoint Y)) ≫ a =
          Spec.map (CommRingCat.ofHom (Scheme.functionFieldMap β)) ≫
            modificationGenericInverse π V hV hiso ∧
        (Y.fromSpecStalk (genericPoint Y)) ≫ h =
          Spec.map (CommRingCat.ofHom (Scheme.functionFieldMap β)) ≫
            (modificationGenericInverse π V hV hiso ≫ j) := by
  let KZ : Scheme.{u} := Spec Z.functionField
  let P : Scheme.{u} := ProjectiveSpace R I
  let gη : KZ ⟶ W := modificationGenericInverse π V hV hiso
  have hgη : (gη ≫ j) ≫ ProjectiveSpace.toSpec R I =
      (Z.fromSpecStalk (genericPoint Z)) ≫ q := by
    rw [Category.assoc, hbase, ← Category.assoc]
    exact congrArg (fun t ↦ t ≫ q) (modificationGenericInverse_comp π V hV hiso)
  obtain ⟨Y, β, c, hout⟩ :=
    RationalCoordinates.exists_pointBlowupChain_projectiveExtension
      (X := Z) hZ hd q (gη ≫ j) hgη
  let : IsIntegral Y := c.isIntegral inferInstance
  let : IsDominant β := c.isDominant inferInstance
  obtain ⟨h, hβ, hbir, hreg, hdim, hhbase, hhη⟩ := hout
  let : IsProper β := hβ
  let : IsLocallyNoetherian Y := LocallyOfFiniteType.isLocallyNoetherian β
  let : CompactSpace Y := QuasiCompact.compactSpace_of_compactSpace β
  have hN : IsNoetherian Y := ⟨⟩
  let KY : Scheme.{u} := Spec Y.functionField
  let ηY : KY ⟶ Y := Y.fromSpecStalk (genericPoint Y)
  let κ : KY ⟶ KZ := Spec.map (CommRingCat.ofHom (Scheme.functionFieldMap β))
  have hfactor : ηY ≫ h = (κ ≫ gη) ≫ j :=
    hhη.trans (Category.assoc κ gη j).symm
  obtain ⟨a, haj, haη⟩ := exists_closedImmersion_factor_of_dominant
    (D := KY) (P := P) ηY h j (κ ≫ gη) hfactor
  have habase : (a ≫ π) ≫ q = β ≫ q := by
    rw [Category.assoc, ← hbase, ← Category.assoc, haj, hhbase]
  have haπ : a ≫ π = β := by
    apply ext_of_isDominant_of_isSeparated q habase ηY
    calc
      _ = (ηY ≫ a) ≫ π := (Category.assoc ηY a π).symm
      _ = (κ ≫ gη) ≫ π := congrArg (fun t : KY ⟶ W ↦ t ≫ π) haη
      _ = κ ≫ (gη ≫ π) := Category.assoc κ gη π
      _ = κ ≫ Z.fromSpecStalk (genericPoint Z) :=
        congrArg (fun t : KZ ⟶ Z ↦ κ ≫ t) (modificationGenericInverse_comp π V hV hiso)
      _ = _ := (Scheme.fromSpecStalk_genericPoint_naturality β).symm
  exact ⟨Y, β, c, a, h, hβ, hbir, hN, hreg, hdim, haπ, haj, hhbase,
    by simpa only [Category.assoc] using habase, haη, hhη⟩

/-- The original proper map over a Noetherian affine base has an actual
projective Chow modification dominated by actual regular point blowups.
The original dense open, embedding, base map and generic inverse are retained. -/
theorem exists_pointBlowupChain_chowDomination [IsNoetherianRing R]
    [IsNoetherian Z] (hZ : RegularStalks Z) (hd : topologicalKrullDim Z ≤ 2)
    (q : Z ⟶ Spec (.of R)) [IsProper q] :
    ∃ (W : Scheme.{u}) (π : W ⟶ Z) (n : ℕ)
      (j : W ⟶ ProjectiveSpace R (ULift.{u} (Fin (n + 1)))) (V : Z.Opens)
      (hV : Dense (V : Set Z)) (hiso : IsIso (π ∣_ V)),
      IsProper π ∧ Surjective π ∧ IsClosedImmersion j ∧
      j ≫ ProjectiveSpace.toSpec R (ULift.{u} (Fin (n + 1))) = π ≫ q ∧
      ∃ (Y : Scheme.{u}) (β : Y ⟶ Z) (c : Blowup.PointBlowupChain β),
        letI : IsIntegral Y := c.isIntegral inferInstance
        letI : IsDominant β := c.isDominant inferInstance
        ∃ (a : Y ⟶ W) (h : Y ⟶ ProjectiveSpace R (ULift.{u} (Fin (n + 1)))),
          IsProper β ∧ BirationalOver β (𝟙 Z) ∧ IsNoetherian Y ∧ RegularStalks Y ∧
          (∀ y : Y, ringKrullDim (Y.presheaf.stalk y) ≤ 2) ∧
          a ≫ π = β ∧ a ≫ j = h ∧
          h ≫ ProjectiveSpace.toSpec R (ULift.{u} (Fin (n + 1))) = β ≫ q ∧
          a ≫ (π ≫ q) = β ≫ q ∧
          (Y.fromSpecStalk (genericPoint Y)) ≫ a =
            Spec.map (CommRingCat.ofHom (Scheme.functionFieldMap β)) ≫
              modificationGenericInverse π V hV hiso ∧
          (Y.fromSpecStalk (genericPoint Y)) ≫ h =
            Spec.map (CommRingCat.ofHom (Scheme.functionFieldMap β)) ≫
              (modificationGenericInverse π V hV hiso ≫ j) := by
  obtain ⟨W, π, n, j, V, hπ, hπsurj, hj, hjbase, hV, hiso⟩ :=
    Chow.exists_projective_modification R q
  let : IsClosedImmersion j := hj
  exact ⟨W, π, n, j, V, hV, hiso, hπ, hπsurj, hj, hjbase,
    exists_pointBlowupChain_dominating_projectiveModification hZ hd q π j hjbase V hV hiso⟩

end AlgebraicGeometry.Scheme.Birational
