/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import
  Aglib.AlgebraicGeometry.Normalization.GenericFiniteEtale.FractionWholePointedExtension
public import
  Aglib.AlgebraicGeometry.EtaleCohomology.Fields.TwoFieldEffacement.NormalMarkedCoverTransport
public import Aglib.AlgebraicGeometry.EtaleCohomology.Continuity.WholeCoefficientZeroSpreading

/-! # The original fraction-field zeros on one whole marked source model

The source cover and mark remain over their specified fraction field. Each
original nested coefficient-cover zero is transported through the actual
original direct/nested fibre comparison. Whole pointed extension is invoked
once, and coefficient continuity restricts only each original coefficient
base. No native function-field presentation or generic zero is silently
substituted for the original one.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits CategoryTheory.PreGaloisCategory
open AlgebraicGeometry.Scheme.FiniteEtale
open AlgebraicGeometry.Scheme.FiniteEtale.GenericNormalization.OpenRecovery
open AlgebraicGeometry.Scheme.PrincipalNeighborhoodLimit
open IsLocalization.PrincipalDiagram
open scoped nonZeroDivisors

namespace AlgebraicGeometry.Scheme.EtaleCohomology.TwoFieldEffacement

universe u v eX
attribute [local instance] hasSheafifyLarge HasExt.standard

section CoefficientMaps

variable (A B F E : Type u) [CommRing A] [CommRing B]
    [Field F] [Field E] [Algebra A B] [Algebra A F]
    [Algebra A E] [Algebra B E] [IsScalarTower A B E]
    (a : F →ₐ[A] E) {X : Scheme.{u}} (p : X ⟶ Spec (.of A))

local notation "pF" => pullback.snd p (Spec.algebraMap A F)
local notation "aE" => Spec.map (CommRingCat.ofHom a.toRingHom)
local notation "b" => pullback.snd p (Spec.algebraMap A B)
local notation "δ" => pullback.fst b (Spec.algebraMap B E)
local notation "ε" => pullback.snd b (Spec.algebraMap B E)

/-- The original chosen-field embedding has its actual coefficient scalar square. -/
theorem fractionCoefficient_square :
    aE ≫ Spec.algebraMap A F = Spec.algebraMap B E ≫ Spec.algebraMap A B := by
  rw [Spec.map_algHom_algebraMap]
  simp only [Spec.algebraMap, ← Spec.map_comp]
  exact congrArg Spec.map (CommRingCat.hom_ext (IsScalarTower.algebraMap_eq A B E))

/-- The direct original coefficient generic fibre maps to the original chosen-field fibre. -/
def fractionCoefficientGenericMap : pullback b (Spec.algebraMap B E) ⟶
    pullback p (Spec.algebraMap A F) :=
  Continuity.WholeCoefficient.genericMap A B E p (Spec.algebraMap A F) aE
    (fractionCoefficient_square A B F E a)

/-- The direct coefficient fibre and the original nested coefficient fibre
are compared by the already constructed original two-fibre isomorphism. -/
def fractionCoefficientDirectNestedIso :
    pullback b (Spec.algebraMap B E) ≅ pullback pF aE :=
  normalGenericFibreIso p (Spec.algebraMap A F) (Spec.algebraMap A B)
    aE (Spec.algebraMap B E) (fractionCoefficient_square A B F E a).symm

@[reassoc]
theorem fractionCoefficientDirectNestedIso_source :
    (fractionCoefficientDirectNestedIso A B F E a p).hom ≫ pullback.fst pF aE =
      fractionCoefficientGenericMap A B F E a p := by
  apply pullback.hom_ext
  · rw [Category.assoc]
    exact (normalGenericFibreIso_source p (Spec.algebraMap A F) (Spec.algebraMap A B)
      aE (Spec.algebraMap B E) (fractionCoefficient_square A B F E a).symm).trans
        (Continuity.WholeCoefficient.genericMap_source A B E p (Spec.algebraMap A F)
          aE (fractionCoefficient_square A B F E a)).symm
  · rw [Category.assoc, pullback.condition, ← Category.assoc]
    have he : (fractionCoefficientDirectNestedIso A B F E a p).hom ≫
        pullback.snd pF aE = ε :=
      normalGenericFibreIso_field p (Spec.algebraMap A F) (Spec.algebraMap A B)
        aE (Spec.algebraMap B E) (fractionCoefficient_square A B F E a).symm
    rw [he]
    exact (Continuity.WholeCoefficient.genericMap_field A B E p (Spec.algebraMap A F)
      aE (fractionCoefficient_square A B F E a)).symm

/-- The original map to the coefficient family becomes its literal direct
projection under the same fibre isomorphism. -/
@[reassoc]
theorem fractionCoefficientDirectNestedIso_family :
    (fractionCoefficientDirectNestedIso A B F E a p).hom ≫
      genericCoefficientFamilyMap A B F E a p = δ := by
  have hf : genericCoefficientFamilyMap A B F E a p ≫
      pullback.fst p (Spec.algebraMap A B) =
        pullback.fst pF aE ≫ pullback.fst p (Spec.algebraMap A F) := pullback.lift_fst ..
  have hb : genericCoefficientFamilyMap A B F E a p ≫ b =
      pullback.snd pF aE ≫ Spec.algebraMap B E := pullback.lift_snd ..
  apply pullback.hom_ext
  · rw [Category.assoc, hf]
    exact normalGenericFibreIso_source p (Spec.algebraMap A F) (Spec.algebraMap A B)
      aE (Spec.algebraMap B E) (fractionCoefficient_square A B F E a).symm
  · rw [Category.assoc, hb, ← Category.assoc]
    have he : (fractionCoefficientDirectNestedIso A B F E a p).hom ≫
        pullback.snd pF aE = ε :=
      normalGenericFibreIso_field p (Spec.algebraMap A F) (Spec.algebraMap A B)
        aE (Spec.algebraMap B E) (fractionCoefficient_square A B F E a).symm
    rw [he]
    exact (pullback.condition (f := b) (g := Spec.algebraMap B E)).symm

variable (Z : FiniteEtale (pullback p (Spec.algebraMap A F)))
local notation "ZD" => Functor.obj (baseChange (fractionCoefficientGenericMap A B F E a p)) Z
local notation "ZN" => Functor.obj (baseChange (pullback.fst pF aE)) Z

/-- The actual direct pullback of the unchanged original cover maps to its
original nested coefficient pullback, retaining the original covering leg. -/
def fractionCoefficientCoverToNested : (ZD).obj.left ⟶ (ZN).obj.left :=
  pullback.lift (pullback.fst Z.obj.hom (fractionCoefficientGenericMap A B F E a p))
    ((ZD).obj.hom ≫ (fractionCoefficientDirectNestedIso A B F E a p).hom) (by
      exact (pullback.condition (f := Z.obj.hom)
        (g := fractionCoefficientGenericMap A B F E a p)).trans
          ((congrArg (fun m => (ZD).obj.hom ≫ m)
            (fractionCoefficientDirectNestedIso_source A B F E a p).symm).trans
              (Category.assoc ..).symm))

/-- Both reconstructed cover maps have the same original target composite. -/
@[reassoc]
theorem fractionCoefficientCoverToNested_family {T : Scheme.{u}}
    (h : pullback p (Spec.algebraMap A B) ⟶ T) :
    fractionCoefficientCoverToNested A B F E a p Z ≫
      (ZN).obj.hom ≫ genericCoefficientFamilyMap A B F E a p ≫ h =
        (ZD).obj.hom ≫ δ ≫ h := by
  have hl : fractionCoefficientCoverToNested A B F E a p Z ≫ (ZN).obj.hom =
      (ZD).obj.hom ≫ (fractionCoefficientDirectNestedIso A B F E a p).hom :=
    pullback.lift_snd ..
  have ht := fractionCoefficientDirectNestedIso_family A B F E a p
  exact (Category.assoc ..).symm.trans
    ((congrArg (fun m => m ≫ (genericCoefficientFamilyMap A B F E a p ≫ h)) hl).trans
      (by simpa only [Category.assoc] using congrArg (fun m => (ZD).obj.hom ≫ m ≫ h) ht))

end CoefficientMaps

section Family

variable (A F : Type u) [CommRing A] [IsDomain A] [Field F]
    [Algebra A F] [IsFractionRing A F] [IsNoetherianRing A] [IsIntegrallyClosed A]
    {X T : Scheme.{u}} [CompactSpace X] [QuasiSeparatedSpace X]
    (p : X ⟶ Spec (.of A)) [Smooth p] [GeometricallyConnected p]
    [QuasiCompact p] [QuasiSeparated p]

local instance fractionFamily_generic_connected :
    ConnectedSpace (pullback p (Spec.algebraMap A F) : Scheme.{u}) :=
  GeometricallyConnected.connectedSpace_of_subsingleton (pullback.snd p (Spec.algebraMap A F))

variable {ι : Type v} (B E : ι → Type u)
    [∀ i, CommRing (B i)] [∀ i, IsDomain (B i)] [∀ i, Field (E i)]
    [∀ i, Algebra A (B i)] [∀ i, Algebra A (E i)] [∀ i, Algebra (B i) (E i)]
    [∀ i, IsScalarTower A (B i) (E i)] [∀ i, IsFractionRing (B i) (E i)]
    (a : ∀ i, F →ₐ[A] E i)
    (σ : Spec (.of A) ⟶ X) (hσ : σ ≫ p = 𝟙 _)
    (Z : FiniteEtale (pullback p (Spec.algebraMap A F))) [IsGalois Z]
    (z : Spec (.of F) ⟶ Z.obj.left)
    (hz : z ≫ Z.obj.hom ≫ pullback.fst p (Spec.algebraMap A F) =
      Spec.algebraMap A F ≫ σ)
    (h : ∀ i, pullback p (Spec.algebraMap A (B i)) ⟶ T)
    [HasExt.{eX} (AbelianSheaf.{u, u + 1} T)]
    (M : AbelianSheaf.{u, u + 1} T) (degree : ℕ) (c : Sheaf.H.{eX} M degree)

include hσ hz in
/-- All original nested coefficient generic zeros give one whole marked
source model and actual coefficient-open zeros. The specified fraction field,
cover, mark, embeddings, target sheaf and class are unchanged. -/
theorem exists_fraction_whole_marked_coefficient_family
    (N : ℕ) (hN : 0 < N) (hunit : IsUnit (N : A))
    (hcard : Nat.card (Aut Z) ∣ N)
    (hc : ∀ i, cohomologyPullback.{u, eX, u + 2}
      (((baseChange (pullback.fst (pullback.snd p (Spec.algebraMap A F))
        (Spec.map (CommRingCat.ofHom (a i).toRingHom)))).obj Z).obj.hom ≫
          genericCoefficientFamilyMap A (B i) F (E i) (a i) p ≫ h i) M degree c = 0) :
    letI : ConnectedSpace X := GeometricallyConnected.connectedSpace p p.isOpenMap
    ∃ (G : FiniteEtale X), IsIntegral G.obj.left ∧ IsGalois G ∧
      Nat.card (Aut G) = Nat.card (Aut Z) ∧
      ∃ (ρ : Spec (.of A) ⟶ G.obj.left), ρ ≫ G.obj.hom = σ ∧
      ∃ (r : (baseChange (pullback.fst p (Spec.algebraMap A F))).obj G ≅ Z)
        (w : Spec (.of F) ⟶
          ((baseChange (pullback.fst p (Spec.algebraMap A F))).obj G).obj.left),
        w ≫ pullback.fst G.obj.hom (pullback.fst p (Spec.algebraMap A F)) =
          Spec.algebraMap A F ≫ ρ ∧ w ≫ r.hom.hom.left = z ∧
        ∀ i,
          let C := (baseChange (pullback.fst p (Spec.algebraMap A (B i)))).obj G
          let b := pullback.snd p (Spec.algebraMap A (B i))
          ∃ t : Finset (B i)⁰, denominator (B i)⁰ t ≠ 0 ∧
            Nonempty (stageBaseOpen (B i)⁰ t) ∧
            cohomologyPullback.{u, eX, u + 2}
              ((stageSourceOpen (B i)⁰ (C.obj.hom ≫ b) t).ι ≫ C.obj.hom ≫ h i)
              M degree c = 0 := by
  obtain ⟨G, hGI, hGG, hGc, ρ, hρ, r, w, hw, hwz⟩ :=
    exists_fraction_whole_galoisPointedExtension A F p Z σ hσ
      N hN hunit hcard z hz
  refine ⟨G, hGI, hGG, hGc, ρ, hρ, r, w, hw, hwz, ?_⟩
  intro i
  have hzero : cohomologyPullback.{u, eX, u + 2}
      (((baseChange
        (fractionCoefficientGenericMap A (B i) F (E i) (a i) p)).obj Z).obj.hom ≫
        pullback.fst (pullback.snd p (Spec.algebraMap A (B i)))
          (Spec.algebraMap (B i) (E i)) ≫ h i) M degree c = 0 :=
    original_class_zero_of_map_law
      (fractionCoefficientCoverToNested A (B i) F (E i) (a i) p Z) _ _
      (fractionCoefficientCoverToNested_family A (B i) F (E i) (a i) p Z (h i))
      M degree c (hc i)
  exact Continuity.WholeCoefficient.exists_open_zero_of_reconstruction
    A (B i) (E i) p (Spec.algebraMap A F) (Spec.map (CommRingCat.ofHom (a i).toRingHom))
    (fractionCoefficient_square A (B i) F (E i) (a i)) G Z r
    (h i) M degree c hzero

end Family

end AlgebraicGeometry.Scheme.EtaleCohomology.TwoFieldEffacement
