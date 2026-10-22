/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.SchemeTheoreticImage.ClosedIdentification
public import Aglib.AlgebraicGeometry.Limits.Range
public import Aglib.AlgebraicGeometry.Morphisms.SchemeTheoreticallyDominant.OpenFactor
public import Mathlib.AlgebraicGeometry.Morphisms.OpenImmersion

/-!
# Uniqueness of domains of closed partial graphs

Two actual closed graphs with a common schematically dense parametrization
have canonically isomorphic domains, preserving both projections and the
original source. For open domains their ranges in the ambient scheme agree.
No reducedness or additional separatedness hypothesis is needed.
-/

@[expose] public noncomputable section
set_option autoImplicit false
open CategoryTheory Limits
universe u

namespace AlgebraicGeometry

namespace Scheme.QuasiDomination

variable {T D₁ D₂ M X S : Scheme.{u}}
variable (d₁ : D₁ ⟶ M) (d₂ : D₂ ⟶ M)
    (h₁ : D₁ ⟶ X) (h₂ : D₂ ⟶ X) (pM : M ⟶ S) (pX : X ⟶ S)
    (w₁ : d₁ ≫ pM = h₁ ≫ pX) (w₂ : d₂ ≫ pM = h₂ ≫ pX)
    (t₁ : T ⟶ D₁) (t₂ : T ⟶ D₂)
    [ht₁ : IsSchemeTheoreticallyDominant t₁] [ht₂ : IsSchemeTheoreticallyDominant t₂]
    [hc₁ : IsClosedImmersion (pullback.lift d₁ h₁ w₁)]
    [hc₂ : IsClosedImmersion (pullback.lift d₂ h₂ w₂)]
    (wd : t₁ ≫ d₁ = t₂ ≫ d₂) (wh : t₁ ≫ h₁ = t₂ ≫ h₂)

include w₁ w₂ wd wh ht₁ ht₂ hc₁ hc₂ in
/-- Closed partial graphs agreeing on a common schematically dense source
identify their actual domains and both projections, as well as that source. -/
theorem exists_domainIso_of_common_schematicallyDense_source :
    ∃ e : D₁ ≅ D₂, e.hom ≫ d₂ = d₁ ∧ e.hom ≫ h₂ = h₁ ∧ t₁ ≫ e.hom = t₂ := by
  have wg : t₁ ≫ pullback.lift d₁ h₁ w₁ = t₂ ≫ pullback.lift d₂ h₂ w₂ := by
    apply pullback.hom_ext
    · simpa only [Category.assoc, pullback.lift_fst] using wd
    · simpa only [Category.assoc, pullback.lift_snd] using wh
  let e := closedIsoOfCommonDenseSource
    (pullback.lift d₁ h₁ w₁) (pullback.lift d₂ h₂ w₂) t₁ t₂ wg
  have he : e.hom ≫ pullback.lift d₂ h₂ w₂ = pullback.lift d₁ h₁ w₁ :=
    closedIsoOfCommonDenseSource_hom_comp _ _ _ _ _
  refine ⟨e, ?_, ?_, comp_closedIsoOfCommonDenseSource_hom _ _ _ _ _⟩
  · simpa only [Category.assoc, pullback.lift_fst] using
      congrArg (fun f => f ≫ pullback.fst pM pX) he
  · simpa only [Category.assoc, pullback.lift_snd] using
      congrArg (fun f => f ≫ pullback.snd pM pX) he

include w₁ w₂ wd wh ht₁ ht₂ hc₁ hc₂ in
/-- In particular, two open domains carrying the same dense closed graph
have the same actual open range in the ambient scheme. -/
theorem opensRange_eq_of_common_schematicallyDense_source
    [IsOpenImmersion d₁] [IsOpenImmersion d₂] : d₁.opensRange = d₂.opensRange := by
  obtain ⟨e, he, _, _⟩ := exists_domainIso_of_common_schematicallyDense_source
    d₁ d₂ h₁ h₂ pM pX w₁ w₂ t₁ t₂ wd wh
  apply SetLike.coe_injective
  change Set.range d₁ = Set.range d₂
  calc
    Set.range d₁ = Set.range (e.hom ≫ d₂) :=
      congrArg (fun f : D₁ ⟶ M => Set.range f) he.symm
    _ = Set.range d₂ := Hom.Range.range_iso_comp e d₂

end Scheme.QuasiDomination
end AlgebraicGeometry
