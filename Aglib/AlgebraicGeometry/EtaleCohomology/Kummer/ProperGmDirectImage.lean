/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.Cohomology.Proper.StructureSheaf.Pushforward
public import Aglib.AlgebraicGeometry.EtaleCohomology.DirectImage
public import Aglib.AlgebraicGeometry.EtaleCohomology.Kummer.CoefficientBaseChange
public import Aglib.AlgebraicGeometry.EtaleCohomology.Kummer.RootCover

/-! Universal functions and power epimorphisms for the original relative units. -/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite
open GroupCohomology.Kummer.Coefficients GroupCohomology.Kummer.CoefficientBaseChange

namespace AlgebraicGeometry.Scheme.EtaleCohomology.Kummer

universe u

attribute [local instance] hasSheafifyLarge

variable {X S : Scheme.{u}} (p : X ⟶ S)
  [IsLocallyNoetherian S] [IsProper p] [Flat p] [GeometricallyIntegral p]

/-- Universal functions identify the original multiplicative sheaf with the
actual direct image, by the original unit on every étale chart. -/
theorem gmUnit_isIso_of_proper_flat_geometricallyIntegral : IsIso (gmUnit p) := by
  let P := sheafToPresheaf S.smallEtaleTopology AddCommGrpCat.{u + 1}
  let : IsIso (P.map (gmUnit p)) := by
    change IsIso (gmUnit p).hom
    let : ∀ U, IsIso ((gmUnit p).hom.app U) := fun U => by
      apply (ConcreteCategory.isIso_iff_bijective _).mpr
      let q := pullback.fst U.unop.hom p
      let e := pullbackSymmetry U.unop.hom p
      have he : e.hom ≫ pullback.snd p U.unop.hom = q :=
        pullbackSymmetry_hom_comp_snd _ _
      have h₁ := bijective_app_pullback_snd_of_isProper_of_flat_of_geometricallyIntegral
        p U.unop.hom ⊤
      have h₂ : Function.Bijective (Scheme.Γ.map e.hom.op) :=
        ConcreteCategory.bijective_of_isIso _
      have hq : Function.Bijective q.appTop.hom := by
        change Function.Bijective (Scheme.Γ.map q.op)
        rw [← he, op_comp, Functor.map_comp]
        exact h₂.comp h₁
      let u := (Units.mapEquiv (RingEquiv.ofBijective q.appTop.hom hq).toMulEquiv).toEquiv
      let a := (unitsSections S U).toEquiv.trans Additive.toMul
      let b := (unitsSections X ((siteBaseChange p).op.obj U)).toEquiv.trans Additive.toMul
      have h : (fun x => (gmUnit p).hom.app U x) = a.trans (u.trans b.symm) := by
        funext x
        apply b.injective
        change b ((gmUnit p).hom.app U x) = b (b.symm (u (a x)))
        exact (gmUnit_sections p U x).trans (b.apply_symm_apply (u (a x))).symm
      change Function.Bijective (fun x => (gmUnit p).hom.app U x)
      rw [h]
      exact Equiv.bijective _
    exact NatIso.isIso_of_isIso_app (gmUnit p).hom
  exact isIso_of_reflects_iso (gmUnit p) P

/-- Positive invertible multiplication on the original direct image of units
is an epimorphism in the original small-étale abelian category. -/
theorem epi_nsmul_gmDirectImage (n : ℕ) (hn : 0 < n) (hinv : IsUnit (n : Γ(S, ⊤))) :
    Epi (n • 𝟙 ((directImage p).obj (gm X))) := by
  let : IsIso (gmUnit p) := gmUnit_isIso_of_proper_flat_geometricallyIntegral p
  let : Epi (power S n) := GroupCohomology.Kummer.RootCover.power_epi S n hn hinv
  have h : power S n ≫ gmUnit p = gmUnit p ≫ (n • 𝟙 ((directImage p).obj (gm X))) := by
    simp only [power, Preadditive.nsmul_comp, Preadditive.comp_nsmul,
      Category.id_comp, Category.comp_id]
  have hEpi : Epi (power S n ≫ gmUnit p) := inferInstance
  rw [h] at hEpi
  let := hEpi
  exact epi_of_epi (gmUnit p) _

variable [HasDerivedCategory (AbelianSheaf.{u, u + 1} X)]
  [HasDerivedCategory (AbelianSheaf.{u, u + 1} S)]

/-- Multiplication on the original degree-zero derived units image is an epimorphism. -/
theorem epi_derivedDirectImage_homologyZero_power (n : ℕ) (hn : 0 < n)
    (hinv : IsUnit (n : Γ(S, ⊤))) :
    Epi ((DerivedCategory.Plus.homologyFunctor (AbelianSheaf.{u, u + 1} S) 0).map
      ((derivedDirectImage p).map
        ((DerivedCategory.Plus.singleFunctor (AbelianSheaf.{u, u + 1} X) 0).map (power X n)))) := by
  let H := DerivedCategory.Plus.homologyFunctor (AbelianSheaf.{u, u + 1} S) 0
  let F := derivedDirectImage p
  let L := DerivedCategory.Plus.singleFunctor (AbelianSheaf.{u, u + 1} X) 0
  let e := derivedDirectImageSingleHomologyZeroIso p
  let m := H.map (F.map (L.map (power X n)))
  let : Epi ((directImage p).map (power X n)) := by
    rw [power, Functor.map_nsmul, (directImage p).map_id]
    exact epi_nsmul_gmDirectImage p n hn hinv
  let : Epi (e.hom.app (gm X) ≫ (directImage p).map (power X n)) := inferInstance
  have h : m ≫ e.hom.app (gm X) = e.hom.app (gm X) ≫ (directImage p).map (power X n) :=
    e.hom.naturality (power X n)
  exact (epi_comp_iff_of_isIso m (e.hom.app (gm X))).mp (h.symm ▸ inferInstance)

end AlgebraicGeometry.Scheme.EtaleCohomology.Kummer
