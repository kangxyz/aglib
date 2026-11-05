/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.EtaleCohomology.Fields.TwoFieldEffacement.FractionWholeCoefficientFamily

/-! # Whole marked source extension with the original coefficient-open zero

This single-coefficient endpoint retains the original fraction field, cover,
mark, reconstruction and class. The source base is never restricted at a
selected prime. The generic-zero input belongs to the internal extension
stage; the original H1 producer supplies it before this theorem is used.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits CategoryTheory.PreGaloisCategory
open AlgebraicGeometry.Scheme.FiniteEtale
open AlgebraicGeometry.Scheme.FiniteEtale.GenericNormalization.OpenRecovery
open AlgebraicGeometry.Scheme.PrincipalNeighborhoodLimit
open IsLocalization.PrincipalDiagram
open scoped nonZeroDivisors

namespace AlgebraicGeometry.Scheme.EtaleCohomology.TwoFieldEffacement

universe u eX

attribute [local instance] hasSheafifyLarge HasExt.standard

variable (A B F : Type u) [CommRing A] [IsDomain A] [CommRing B] [IsDomain B]
  [Field F] [Algebra A B] [Algebra A F] [IsFractionRing A F]
  {X T : Scheme.{u}} (p : X ⟶ Spec (CommRingCat.of A))
  (σ : Spec (CommRingCat.of A) ⟶ X) (hσ : σ ≫ p = 𝟙 _)
  (Z : FiniteEtale (pullback p (Spec.algebraMap A F)))
  (z : Fiber (fractionSectionPoint A F p σ hσ) Z)
  (h : pullback p (Spec.algebraMap A B) ⟶ T)
  [HasExt.{eX} (AbelianSheaf.{u, u + 1} T)]
  (M : AbelianSheaf.{u, u + 1} T) (degree : ℕ) (c : Sheaf.H.{eX} M degree)

/-- The unchanged cover extends over the whole source base, with an actual
whole section and generic reconstruction. Only the coefficient is restricted
to a nonempty principal open. No source prime is part of this result. -/
def WholeMarkedOpenClassZero : Prop :=
  ∃ (G : FiniteEtale X), IsIntegral G.obj.left ∧
    Nat.card (Aut G) = Nat.card (Aut Z) ∧
    ∃ (ρ : Spec (CommRingCat.of A) ⟶ G.obj.left), ρ ≫ G.obj.hom = σ ∧
    ∃ (r : (baseChange (pullback.fst p (Spec.algebraMap A F))).obj G ≅ Z)
      (w : Spec (CommRingCat.of F) ⟶
        ((baseChange (pullback.fst p (Spec.algebraMap A F))).obj G).obj.left),
      w ≫ pullback.fst G.obj.hom (pullback.fst p (Spec.algebraMap A F)) =
        Spec.algebraMap A F ≫ ρ ∧ w ≫ r.hom.hom.left = z.left ∧
      let C := (baseChange (pullback.fst p (Spec.algebraMap A B))).obj G
      ∃ t : Finset B⁰, denominator B⁰ t ≠ 0 ∧ Nonempty (stageBaseOpen B⁰ t) ∧
        cohomologyPullback.{u, eX, u + 2}
          ((stageSourceOpen B⁰ (C.obj.hom ≫ pullback.snd p (Spec.algebraMap A B)) t).ι ≫
            C.obj.hom ≫ h) M degree c = 0

/-- The existing whole-family extension supplies this endpoint on one
coefficient model without reselecting its source cover or original mark. -/
theorem whole_marked_open_class_zero
    [IsNoetherianRing A] [IsIntegrallyClosed A]
    [CompactSpace X] [QuasiSeparatedSpace X] [Smooth p] [GeometricallyConnected p]
    [QuasiCompact p] [QuasiSeparated p] [IsGalois Z]
    (E : Type u) [Field E] [Algebra A E] [Algebra B E]
    [IsScalarTower A B E] [IsFractionRing B E] (a : F →ₐ[A] E)
    (N : ℕ) (hN : 0 < N) (hunit : IsUnit (N : A)) (hcard : Nat.card (Aut Z) ∣ N)
    (hc : cohomologyPullback.{u, eX, u + 2}
      (((baseChange (pullback.fst (pullback.snd p (Spec.algebraMap A F))
        (Spec.map (CommRingCat.ofHom a.toRingHom)))).obj Z).obj.hom ≫
        genericCoefficientFamilyMap A B F E a p ≫ h) M degree c = 0) :
    WholeMarkedOpenClassZero A B F p σ hσ Z z h M degree c := by
  have hz : z.left ≫ Z.obj.hom ≫ pullback.fst p (Spec.algebraMap A F) =
      Spec.algebraMap A F ≫ σ := by
    rw [← Category.assoc, Over.w z]
    change fractionSectionPoint A F p σ hσ ≫ pullback.fst p (Spec.algebraMap A F) = _
    exact fractionSectionPoint_fst A F p σ hσ
  obtain ⟨G, hGI, _hGG, hcardG, ρ, hρ, r, w, hw, hwz, hzero⟩ :=
    exists_fraction_whole_marked_coefficient_family (ι := PUnit.{1}) A F p
      (fun _ : PUnit.{1} => B) (fun _ : PUnit.{1} => E) (fun _ => a)
      σ hσ Z z.left hz (fun _ => h) M degree c N hN hunit hcard (fun _ => hc)
  exact ⟨G, hGI, hcardG, ρ, hρ, r, w, hw, hwz, hzero PUnit.unit⟩

end AlgebraicGeometry.Scheme.EtaleCohomology.TwoFieldEffacement
