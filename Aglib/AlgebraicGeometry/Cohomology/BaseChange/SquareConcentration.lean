/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.Cohomology.BaseChange.ResidueFieldConcentration

/-!
# Original fibre cohomology through an actual cartesian square

Paste the given square with the original field-fibre square. Its canonical
pullback isomorphism retains both projection equations. Pullback composition
and the one given coefficient isomorphism produce the actual fibre
coefficient comparison, and the structural field maps give its K-linear
cohomology equivalence. Its forward map is the original geometric cohomology
map, before dimensions or concentration are considered.

No flatness or properness is needed for this isomorphism-of-fibres argument.
It asserts no nonflat base change for higher direct images, and introduces
no second fibre or evaluation realization.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open Scheme.Modules.QuasiCoherent

universe u

namespace AlgebraicGeometry.Scheme.Cohomology

variable {X S X' T : Scheme.{u}} {f : X ⟶ S} {g : T ⟶ S}
  {b : X' ⟶ X} {p : X' ⟶ T} (H : IsPullback b p f g)

/-- The canonical isomorphism of the actual fibres from the pasted
ORIGINAL cartesian square. -/
def fibreSquareIso {K : Type u} [Field K] (t : Spec (.of K) ⟶ T) :
    pullback p t ≅ pullback f (t ≫ g) :=
  ((IsPullback.of_hasPullback p t).paste_horiz H).isoPullback

@[reassoc (attr := simp)]
theorem fibreSquareIso_hom_fst {K : Type u} [Field K] (t : Spec (.of K) ⟶ T) :
    (fibreSquareIso H t).hom ≫ pullback.fst f (t ≫ g) = pullback.fst p t ≫ b :=
  ((IsPullback.of_hasPullback p t).paste_horiz H).isoPullback_hom_fst

@[reassoc (attr := simp)]
theorem fibreSquareIso_hom_snd {K : Type u} [Field K] (t : Spec (.of K) ⟶ T) :
    (fibreSquareIso H t).hom ≫ pullback.snd f (t ≫ g) = pullback.snd p t :=
  ((IsPullback.of_hasPullback p t).paste_horiz H).isoPullback_hom_snd

variable (M : X.Modules) (N : X'.Modules) (C : (Scheme.Modules.pullback b).obj M ≅ N)

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
/-- The original coefficient comparison through the same canonical fibre
isomorphism, using only pullback composition and the given coefficient iso. -/
def fibreSquareCoefficientIso {K : Type u} [Field K] (t : Spec (.of K) ⟶ T) :
    (Scheme.Modules.pullback (fibreSquareIso H t).hom).obj
      ((Scheme.Modules.pullback (pullback.fst f (t ≫ g))).obj M) ≅
        (Scheme.Modules.pullback (pullback.fst p t)).obj N :=
  (Scheme.Modules.pullbackComp (fibreSquareIso H t).hom (pullback.fst f (t ≫ g))).app M ≪≫
    (Scheme.Modules.pullbackCongr (fibreSquareIso_hom_fst H t)).app M ≪≫
      ((Scheme.Modules.pullbackComp (pullback.fst p t) b).app M).symm ≪≫
        (Scheme.Modules.pullback (pullback.fst p t)).mapIso C

omit M N C in
/-- The original structural field action is preserved by the same fibre
isomorphism; this is the literal projection equation on global sections. -/
theorem fibreSquareIso_appTop {K : Type u} [Field K] (t : Spec (.of K) ⟶ T) :
    (fibreSquareIso H t).hom.appTop.hom.comp
      ((pullback.snd f (t ≫ g)).appTop.hom.comp (Scheme.ΓSpecIso (.of K)).inv.hom) =
      ((pullback.snd p t).appTop.hom.comp (Scheme.ΓSpecIso (.of K)).inv.hom).comp
        (RingHom.id K) := by
  rw [← fibreSquareIso_hom_snd H t, Scheme.Hom.comp_appTop]
  rfl

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
/-- The K-linear equivalence of the ORIGINAL actual fibre cohomology,
through the original geometric map and marked coefficient iso. -/
def fibreCohomologyEquivOfSquare {K : Type u} [Field K]
    (t : Spec (.of K) ⟶ T) (n : ℕ) :
    fibreCohomology f M K (t ≫ g) n ≃ₗ[K] fibreCohomology p N K t n := by
  let e := fibreSquareIso H t
  let P := (Scheme.Modules.pullback (pullback.fst f (t ≫ g))).obj M
  let Q := (Scheme.Modules.pullback (pullback.fst p t)).obj N
  let α := (pullback.snd f (t ≫ g)).appTop.hom.comp (Scheme.ΓSpecIso (.of K)).inv.hom
  let β := (pullback.snd p t).appTop.hom.comp (Scheme.ΓSpecIso (.of K)).inv.hom
  let := moduleCohomologyModuleOfHom _ α P n
  let := moduleCohomologyModuleOfHom _ β Q n
  exact (moduleCohomologyRestrictionIsoOfPullbackIso e.hom (RingHom.id K) α β
    (fibreSquareIso_appTop H t) P (fibreSquareCoefficientIso H M N C t) n ≪≫
      ModuleCat.restrictScalarsId'App (RingHom.id K) rfl _).toLinearEquiv

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
/-- The equivalence's forward map is the original cohomology map with
the original adjunction unit and the same coefficient comparison. -/
theorem fibreCohomologyEquivOfSquare_apply {K : Type u} [Field K]
    (t : Spec (.of K) ⟶ T) (n : ℕ) (x : fibreCohomology f M K (t ≫ g) n) :
    fibreCohomologyEquivOfSquare H M N C t n x =
      moduleCohomologyMapAlong (fibreSquareIso H t).hom
        ((Scheme.Modules.pullbackPushforwardAdjunction (fibreSquareIso H t).hom).unit.app
            ((Scheme.Modules.pullback (pullback.fst f (t ≫ g))).obj M) ≫
          (Scheme.Modules.pushforward (fibreSquareIso H t).hom).map
            (fibreSquareCoefficientIso H M N C t).hom) n x := rfl

include H C in
/-- Dimension and vanishing are consequences of that actual K-linear
equivalence, not substitutes for its geometric map. -/
theorem fibreCohomology_square_comparison {K : Type u} [Field K]
    (t : Spec (.of K) ⟶ T) (n : ℕ) :
    Module.finrank K (fibreCohomology p N K t n) =
      Module.finrank K (fibreCohomology f M K (t ≫ g) n) ∧
    (Subsingleton (fibreCohomology p N K t n) ↔
      Subsingleton (fibreCohomology f M K (t ≫ g) n)) :=
  ⟨(fibreCohomologyEquivOfSquare H M N C t n).finrank_eq.symm,
    (fibreCohomologyEquivOfSquare H M N C t n).toEquiv.subsingleton_congr.symm⟩

include H C in
/-- Geometric concentration transports along the original cartesian
square and the actual coefficient isomorphism, with arbitrary base map. -/
theorem FibreCohomologyConcentrated.of_isPullback (r : ℕ)
    (hM : FibreCohomologyConcentrated f M r) : FibreCohomologyConcentrated p N r := by
  intro K _ _ t
  have h := hM K (t ≫ g)
  exact ⟨(fibreCohomology_square_comparison H M N C t 0).1.trans h.1,
    fun n hn => (fibreCohomology_square_comparison H M N C t n).2.mpr (h.2 n hn)⟩

end AlgebraicGeometry.Scheme.Cohomology
