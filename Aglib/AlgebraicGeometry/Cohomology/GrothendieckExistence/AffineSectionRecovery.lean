/-
Copyright (c) 2026 algebraic-geometry contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.Cohomology.GrothendieckExistence.CompleteSections
public import Aglib.AlgebraicGeometry.Modules.Locality.AffineGluing

/-! # Recovery from compatible affine quotient sections -/

@[expose] public noncomputable section
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open CategoryTheory Opposite

namespace AlgebraicGeometry.Scheme.Cohomology

universe u
variable {A : Type u} [CommRing A] [IsNoetherianRing A]
  (I : Ideal A) [IsAdicComplete I A] {X : Scheme.{u}}
  (f : X ⟶ Spec (CommRingCat.of A)) [IsProper f] (F : X.Modules)
  (hF : Modules.QuasiCoherent.affineLocallyFiniteType X F)

local notation "α" => Modules.idealThickeningBaseScalar f
local notation "Q" n => Modules.idealQuotient X α F (I ^ n)

include hF in
/-- Affine-local quotient sections compatible in the open and adic directions
recover a unique original global section. -/
theorem existsUnique_section_of_affineQuotientSections
    (s : ∀ (n : ℕ) (U : X.affineOpens), Γ(Q n, U.val))
    (hres : ∀ (n : ℕ) (U V : X.affineOpens) (i : V.val ⟶ U.val),
      (Q n).val.map i.op (s n U) = s n V)
    (hstep : ∀ (m n : ℕ) (h : m ≤ n) (U : X.affineOpens),
      (Modules.idealPowerQuotientMap X α F I h).app U.val (s n U) = s m U) :
    ∃! t : Γ(F, ⊤), ∀ (n : ℕ) (U : X.affineOpens),
      (Q n).val.map (homOfLE le_top : U.val ⟶ ⊤).op
        ((Modules.idealQuotientπ X α F (I ^ n)).app ⊤ t) = s n U := by
  have hg (n : ℕ) := Modules.existsUnique_section_of_affineSubopens (Q n) ⊤
    (fun U => s n U.val) (fun U V i => hres n U.val V.val i)
  let g (n : ℕ) : Γ(Q n, ⊤) := (hg n).choose
  have hgprop (n : ℕ) (U : X.affineOpens) :
      (Q n).val.map (homOfLE le_top : U.val ⟶ ⊤).op (g n) = s n U :=
    (hg n).choose_spec.1 ⟨U, le_top⟩
  have gstep (m n : ℕ) (h : m ≤ n) :
      (Modules.idealPowerQuotientMap X α F I h).app ⊤ (g n) = g m := by
    apply Modules.section_ext_affineSubopens (Q m) ⊤
    intro U i
    erw [← PresheafOfModules.naturality_apply]
    change (Modules.idealPowerQuotientMap X α F I h).app U.val
      ((Q n).val.map (homOfLE le_top : U.val ⟶ ⊤).op (g n)) =
        (Q m).val.map (homOfLE le_top : U.val ⟶ ⊤).op (g m)
    rw [hgprop, hgprop, hstep]
  obtain ⟨t, ht, huniq⟩ := existsUnique_section_of_quotientSections X I f F hF g gstep
  refine ⟨t, ?_, ?_⟩
  · intro n U
    rw [ht, hgprop]
  · intro t' ht'
    apply huniq t'
    intro n
    apply Modules.section_ext_affineSubopens (Q n) ⊤
    intro U i
    exact (ht' n U).trans (hgprop n U).symm

end AlgebraicGeometry.Scheme.Cohomology
