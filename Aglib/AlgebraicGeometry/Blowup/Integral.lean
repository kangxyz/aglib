/-
Copyright (c) 2026 kangxyz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.Blowup.Construction
public import Aglib.AlgebraicGeometry.FunctionField.Map
public import Mathlib.AlgebraicGeometry.Birational.Birational
public import Mathlib.AlgebraicGeometry.ResidueField

/-!
# Integrality and the original generic comparison for a blowup

If an actual ideal sheaf on an integral scheme misses the generic point, its
native constructed blowup is integral and its original structural map is
dominant. Its restriction off the original centre is the existing literal
restriction isomorphism. This gives a partial isomorphism over the original
scheme and an equivalence whose ring homomorphism is the original generic-point
stalk map.

No Noetherian, regularity, finite-generation or dimension hypothesis is needed.
For a closed-point centre the condition is exactly that the closed point differ
from the original generic point. In particular, the zero centre on a nonempty
integral scheme is excluded.
-/

@[expose] public section

noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open CategoryTheory Limits AlgebraicGeometry TopologicalSpace

universe u

namespace AlgebraicGeometry.Scheme.Blowup

variable {X : Scheme.{u}}

/-- The actual open complement of the support of the centre ideal sheaf. -/
def centreComplement (I : X.IdealSheafData) : X.Opens :=
  ⟨(I.support : Set X)ᶜ, I.support.isClosed.isOpen_compl⟩

@[simp]
lemma mem_centreComplement (I : X.IdealSheafData) (x : X) :
    x ∈ centreComplement I ↔ x ∉ (I.support : Set X) := Iff.rfl

/-- The centre complement is disjoint from the actual support of the centre. -/
lemma centreComplement_disjoint (I : X.IdealSheafData) :
    Disjoint (centreComplement I : Set X) (I.support : Set X) :=
  Set.disjoint_left.mpr fun _ hx hx' => hx hx'

namespace BlowupDatum

variable {I : X.IdealSheafData} (B : BlowupDatum I)

/-- Every original point outside the centre has an actual preimage under the
specified blowup map, using its universal lift of the centre complement. -/
lemma mem_range_of_not_mem_support {x : X} (hx : x ∉ (I.support : Set X)) :
    x ∈ Set.range B.map := by
  let U := centreComplement I
  have hc : I.comap U.ι = ⊤ :=
    comap_eq_top_of_disjoint U (centreComplement_disjoint I)
  let h := cartier_of_comap_eq_top I U.ι hc
  refine ⟨B.lift U.ι h ⟨x, hx⟩, ?_⟩
  change (B.lift U.ι h ≫ B.map) ⟨x, hx⟩ = x
  rw [B.lift_map]
  rfl

/-- The original blowup map is injective on the inverse image of the complement
of its actual centre. -/
lemma map_injective_away {a b : B.Y}
    (ha : B.map a ∉ (I.support : Set X))
    (hb : B.map b ∉ (I.support : Set X)) (hab : B.map a = B.map b) : a = b := by
  let U := centreComplement I
  let : IsIso (B.map ∣_ U) := B.restrict_isIso_of_disjoint U (centreComplement_disjoint I)
  let a' : (B.map ⁻¹ᵁ U).toScheme := ⟨a, ha⟩
  let b' : (B.map ⁻¹ᵁ U).toScheme := ⟨b, hb⟩
  have h : (B.map ∣_ U) a' = (B.map ∣_ U) b' := by
    apply Subtype.ext
    simpa only [morphismRestrict_base_coe] using hab
  exact congrArg Subtype.val ((B.map ∣_ U).isOpenEmbedding.injective h)

/-- Missing the generic point makes the actual centre complement dense, hence
makes the specified blowup map dominant. No source-integrality premise is used. -/
theorem isDominant_of_genericPoint_not_mem_support [IsIntegral X]
    (hI : genericPoint X ∉ (I.support : Set X)) : IsDominant B.map := by
  constructor
  exact ((centreComplement I).isOpen.dense ⟨genericPoint X, hI⟩).mono
    (fun _ hx => B.mem_range_of_not_mem_support hx)

end BlowupDatum

private lemma affineProj_isReduced {A : Type u} [CommRing A] [IsDomain A] (J : Ideal A) :
    IsReduced (affineProj J) := by
  let (x : affineProj J) : _root_.IsReduced ((affineProj J).presheaf.stalk x) := by
    let p := x.asHomogeneousIdeal.toIdeal
    let : _root_.IsReduced (HomogeneousLocalization.AtPrime (reesAlgebra.grading J) p) := by
      constructor
      intro f hf
      apply HomogeneousLocalization.val_injective p.primeCompl
      rw [HomogeneousLocalization.val_zero]
      have hv : IsNilpotent (HomogeneousLocalization.val f) := by
        obtain ⟨n, hn⟩ := hf
        refine ⟨n, ?_⟩
        simpa only [HomogeneousLocalization.val_pow, HomogeneousLocalization.val_zero] using
          congrArg HomogeneousLocalization.val hn
      exact hv.eq_zero
    exact isReduced_of_injective (Proj.stalkIso (reesAlgebra.grading J) x).hom.hom
      (Proj.stalkIso (reesAlgebra.grading J) x).commRingCatIsoToRingEquiv.injective
  exact isReduced_of_isReduced_stalk _

private lemma affineProj_isIntegral {A : Type u} [CommRing A] [IsDomain A] (J : Ideal A)
    [Nonempty (affineProj J)] : IsIntegral (affineProj J) := by
  let p : affineProj J := Classical.choice inferInstance
  let z : ProjectiveSpectrum (reesAlgebra.grading J) :=
    { asHomogeneousIdeal := ⊥
      isPrime := by change (⊥ : Ideal (reesAlgebra J)).IsPrime; infer_instance
      not_irrelevant_le := fun h => p.not_irrelevant_le (h.trans bot_le) }
  have hz : IsGenericPoint z (Set.univ : Set (affineProj J)) := by
    change closure ({z} : Set (ProjectiveSpectrum (reesAlgebra.grading J))) = Set.univ
    rw [← ProjectiveSpectrum.zeroLocus_vanishingIdeal_eq_closure,
      ProjectiveSpectrum.vanishingIdeal_singleton]
    exact ProjectiveSpectrum.zeroLocus_bot _
  let : IsReduced (affineProj J) := affineProj_isReduced J
  let : IrreducibleSpace (affineProj J) := (irreducibleSpace_def _).mpr hz.isIrreducible
  exact isIntegral_of_irreducibleSpace_of_isReduced _

private lemma localDatum_isIntegral [IsIntegral X] (I : X.IdealSheafData)
    (U : X.affineOpens) [Nonempty (Construction.localDatum I U).Y] :
    IsIntegral (Construction.localDatum I U).Y := by
  let v := (Construction.localDatum I U).map (Classical.choice inferInstance)
  let : IsAffine U.1.toScheme := U.2
  let : Nonempty U.1 := ⟨v⟩
  let : IsIntegral U.1.toScheme := isIntegral_of_isOpenImmersion U.1.ι
  let : Nonempty (⊤ : U.1.toScheme.Opens) := ⟨⟨v, trivial⟩⟩
  let : IsDomain Γ(U.1.toScheme, ⊤) := IsIntegral.component_integral ⊤
  change IsIntegral (affineProj (spectrumIdeal
    ((I.comap U.1.ι).comap U.1.toScheme.isoSpec.inv)))
  let : Nonempty (affineProj (spectrumIdeal
      ((I.comap U.1.ι).comap U.1.toScheme.isoSpec.inv))) := by
    change Nonempty (Construction.localDatum I U).Y
    infer_instance
  exact affineProj_isIntegral (A := Γ(U.1.toScheme, ⊤)) _

private lemma localDatum_isReduced [IsIntegral X] (I : X.IdealSheafData)
    (U : X.affineOpens) : IsReduced (Construction.localDatum I U).Y := by
  classical
  by_cases hU : Nonempty U.1
  · let := hU
    let : IsAffine U.1.toScheme := U.2
    let : IsIntegral U.1.toScheme := isIntegral_of_isOpenImmersion U.1.ι
    let : Nonempty (⊤ : U.1.toScheme.Opens) := ⟨⟨Classical.choice hU, trivial⟩⟩
    let : IsDomain Γ(U.1.toScheme, ⊤) := IsIntegral.component_integral ⊤
    change IsReduced (affineProj (spectrumIdeal
      ((I.comap U.1.ι).comap U.1.toScheme.isoSpec.inv)))
    exact affineProj_isReduced (A := Γ(U.1.toScheme, ⊤)) _
  · let (z : (Construction.localDatum I U).Y) :
        _root_.IsReduced ((Construction.localDatum I U).Y.presheaf.stalk z) :=
      False.elim (hU ⟨(Construction.localDatum I U).map z⟩)
    exact isReduced_of_isReduced_stalk _

/-- The native globally glued Rees blowup of an integral scheme is integral if
its actual centre misses the original generic point. -/
theorem blowup_isIntegral [IsIntegral X] (I : X.IdealSheafData)
    (hI : genericPoint X ∉ (I.support : Set X)) : IsIntegral (blowupDatum I).Y := by
  let B := blowupDatum I
  obtain ⟨η, hη⟩ := B.mem_range_of_not_mem_support hI
  let C := Scheme.IsLocallyDirected.openCover (Construction.diagram I)
  have hC : ∀ i, IsReduced (C.X i) := by
    intro U
    change IsReduced (Construction.localDatum I U).Y
    exact localDatum_isReduced I U
  let : IsReduced B.Y := @IsReduced.of_openCover B.Y C hC
  have hgen : IsGenericPoint η (Set.univ : Set B.Y) := by
    apply Set.Subset.antisymm (Set.subset_univ _)
    intro y _
    obtain ⟨U, z, rfl⟩ := Scheme.IsLocallyDirected.ι_jointly_surjective (Construction.diagram I) y
    let D := Construction.localDatum I U
    let j := colimit.ι (Construction.diagram I) U
    let : Nonempty D.Y := ⟨z⟩
    let : IsIntegral D.Y := localDatum_isIntegral I U
    let : Nonempty U.1 := ⟨D.map z⟩
    let : IsIntegral U.1.toScheme := isIntegral_of_isOpenImmersion U.1.ι
    let : IsDominant U.1.ι :=
      Opens.isDominant_ι (U.1.isOpen.dense ⟨(D.map z).1, (D.map z).2⟩)
    have hUη : U.1.ι (genericPoint U.1.toScheme) = genericPoint X :=
      Scheme.map_genericPoint_of_isDominant _ _
    have hlocal : genericPoint U.1.toScheme ∉
        ((I.comap U.1.ι).support : Set U.1.toScheme) := by
      rw [Scheme.IdealSheafData.support_comap]
      change U.1.ι (genericPoint U.1.toScheme) ∉ (I.support : Set X)
      rwa [hUη]
    let : IsDominant D.map := D.isDominant_of_genericPoint_not_mem_support hlocal
    have hDη : D.map (genericPoint D.Y) = genericPoint U.1.toScheme :=
      Scheme.map_genericPoint_of_isDominant _ _
    have hjη : B.map (j (genericPoint D.Y)) = genericPoint X := by
      change (colimit.ι (Construction.diagram I) U ≫ Construction.map I)
        (genericPoint D.Y) = genericPoint X
      rw [Construction.ι_map]
      change U.1.ι (D.map (genericPoint D.Y)) = genericPoint X
      rw [hDη, hUη]
    have heq : j (genericPoint D.Y) = η :=
      B.map_injective_away (by rwa [hjη]) (by rwa [hη]) (hjη.trans hη.symm)
    have hclosure : j z ∈ closure ({j (genericPoint D.Y)} : Set B.Y) := by
      rw [((genericPoint_spec D.Y).image j.continuous).def]
      exact subset_closure ⟨z, trivial, rfl⟩
    simpa only [heq] using hclosure
  let : IrreducibleSpace B.Y := (irreducibleSpace_def _).mpr hgen.isIrreducible
  exact isIntegral_of_irreducibleSpace_of_isReduced _

namespace BlowupDatum

variable [IsIntegral X] {I : X.IdealSheafData} (B : BlowupDatum I)

/-- Integrality transfers from the actual native construction through the
unique comparison over the original base. -/
theorem isIntegral_of_genericPoint_not_mem_support
    (hI : genericPoint X ∉ (I.support : Set X)) : IsIntegral B.Y := by
  let : IsIntegral (blowupDatum I).Y := blowup_isIntegral I hI
  exact IsIntegral.of_isIso ((blowupDatum I).comparisonIso B).hom

/-- The actual restriction of the specified blowup map gives a dense partial
isomorphism to the original scheme. -/
def awayPartialIso (hI : genericPoint X ∉ (I.support : Set X)) :
    letI : IsIntegral B.Y := B.isIntegral_of_genericPoint_not_mem_support hI
    B.Y.PartialIso X := by
  letI : IsIntegral B.Y := B.isIntegral_of_genericPoint_not_mem_support hI
  let U := centreComplement I
  letI : IsIso (B.map ∣_ U) := B.restrict_isIso_of_disjoint U (centreComplement_disjoint I)
  have hs : (B.map ⁻¹ᵁ U : Set B.Y).Nonempty := by
    obtain ⟨η, hη⟩ := B.mem_range_of_not_mem_support hI
    exact ⟨η, by change B.map η ∉ _; rwa [hη]⟩
  exact
    { source := B.map ⁻¹ᵁ U
      dense_source := (B.map ⁻¹ᵁ U).isOpen.dense hs
      target := U
      dense_target := U.isOpen.dense ⟨genericPoint X, hI⟩
      iso := asIso (B.map ∣_ U) }

/-- The preceding partial isomorphism is over the original base with the
specified structural map, rather than an unrelated birational identification. -/
theorem birationalOver (hI : genericPoint X ∉ (I.support : Set X)) :
    BirationalOver B.map (𝟙 X) := by
  refine ⟨B.awayPartialIso hI, ?_⟩
  simpa only [PartialIso.IsOver, awayPartialIso, asIso_hom, Category.comp_id] using
    morphismRestrict_ι B.map (centreComplement I)

omit [IsIntegral X] in
private lemma stalkMap_isIso_away {y : B.Y} (hy : B.map y ∉ (I.support : Set X)) :
    IsIso (B.map.stalkMap y) := by
  let U := centreComplement I
  let : IsIso (B.map ∣_ U) := B.restrict_isIso_of_disjoint U (centreComplement_disjoint I)
  exact (Arrow.isIso_iff_isIso_of_isIso
    (morphismRestrictStalkMap B.map U ⟨y, hy⟩).hom).mp inferInstance

private lemma stalkSpecializes_isIso_of_eq {Y : Scheme.{u}} {a b : Y} (h : a = b) :
    IsIso (Y.presheaf.stalkSpecializes (specializes_of_eq h)) := by
  subst b
  simpa only [TopCat.Presheaf.stalkSpecializes_refl] using
    (inferInstance : IsIso (𝟙 (Y.presheaf.stalk a)))

/-- The ring homomorphism induced by the original blowup map on its actual
generic-point stalks is an isomorphism. Source integrality and dominance are
derived here from the centre condition. -/
theorem functionFieldMap_isIso (hI : genericPoint X ∉ (I.support : Set X)) :
    let : IsIntegral B.Y := B.isIntegral_of_genericPoint_not_mem_support hI
    let : IsDominant B.map := B.isDominant_of_genericPoint_not_mem_support hI
    IsIso (CommRingCat.ofHom (Scheme.functionFieldMap B.map)) := by
  let : IsIntegral B.Y := B.isIntegral_of_genericPoint_not_mem_support hI
  let : IsDominant B.map := B.isDominant_of_genericPoint_not_mem_support hI
  have hη := Scheme.map_genericPoint_of_isDominant B.Y B.map
  let : IsIso (B.map.stalkMap (genericPoint B.Y)) :=
    B.stalkMap_isIso_away (by rwa [hη])
  let : IsIso (X.presheaf.stalkSpecializes (specializes_of_eq hη)) :=
    stalkSpecializes_isIso_of_eq hη
  change IsIso (X.presheaf.stalkSpecializes (specializes_of_eq hη) ≫
    B.map.stalkMap (genericPoint B.Y))
  infer_instance

/-- The canonical equivalence on the original function fields. Its underlying
homomorphism is exactly `Scheme.functionFieldMap B.map`. -/
def functionFieldEquiv (hI : genericPoint X ∉ (I.support : Set X)) :
    letI : IsIntegral B.Y := B.isIntegral_of_genericPoint_not_mem_support hI
    X.functionField ≃+* B.Y.functionField := by
  letI : IsIntegral B.Y := B.isIntegral_of_genericPoint_not_mem_support hI
  letI : IsDominant B.map := B.isDominant_of_genericPoint_not_mem_support hI
  letI := B.functionFieldMap_isIso hI
  exact (asIso (CommRingCat.ofHom (Scheme.functionFieldMap B.map))).commRingCatIsoToRingEquiv

lemma functionFieldEquiv_toRingHom (hI : genericPoint X ∉ (I.support : Set X)) :
    let : IsIntegral B.Y := B.isIntegral_of_genericPoint_not_mem_support hI
    let : IsDominant B.map := B.isDominant_of_genericPoint_not_mem_support hI
    (B.functionFieldEquiv hI : X.functionField →+* B.Y.functionField) =
      Scheme.functionFieldMap B.map := rfl

end BlowupDatum

/-- The ideal of a closed nongeneric point misses the original generic point. -/
lemma genericPoint_not_mem_pointCentre [IsIntegral X] (x : X)
    (hx : IsClosed ({x} : Set X)) (hne : x ≠ genericPoint X) :
    genericPoint X ∉ ((X.fromSpecResidueField x).ker.support : Set X) := by
  let : IsClosedImmersion (X.fromSpecResidueField x) :=
    isClosed_singleton_iff_isClosedImmersion.mp hx
  rw [Scheme.Hom.support_ker, Scheme.range_fromSpecResidueField, hx.closure_eq]
  simpa only [Set.mem_singleton_iff] using Ne.symm hne

/-- The actual native blowup at a closed point distinct from the original
generic point has integral source. -/
theorem pointBlowup_isIntegral (X : Scheme.{u}) [IsIntegral X] (x : X)
    (hx : IsClosed ({x} : Set X)) (hne : x ≠ genericPoint X) :
    IsIntegral (blowupDatum (X.fromSpecResidueField x).ker).Y :=
  blowup_isIntegral _ (genericPoint_not_mem_pointCentre x hx hne)

/-- The original map of the actual native closed nongeneric point blowup is dominant. -/
theorem pointBlowup_isDominant (X : Scheme.{u}) [IsIntegral X] (x : X)
    (hx : IsClosed ({x} : Set X)) (hne : x ≠ genericPoint X) :
    IsDominant (blowupDatum (X.fromSpecResidueField x).ker).map :=
  (blowupDatum _).isDominant_of_genericPoint_not_mem_support
    (genericPoint_not_mem_pointCentre x hx hne)

/-- The point blowup's dense partial isomorphism retains its actual map to the original scheme. -/
theorem pointBlowup_birationalOver (X : Scheme.{u}) [IsIntegral X] (x : X)
    (hx : IsClosed ({x} : Set X)) (hne : x ≠ genericPoint X) :
    BirationalOver (blowupDatum (X.fromSpecResidueField x).ker).map (𝟙 X) :=
  (blowupDatum _).birationalOver (genericPoint_not_mem_pointCentre x hx hne)

end AlgebraicGeometry.Scheme.Blowup
