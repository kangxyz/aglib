/-
Copyright (c) 2026 algebraic-geometry contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.Cohomology.BaseChange.Modules.Sections
public import Aglib.AlgebraicGeometry.Cohomology.FormalFunctions.ReesSections
public import Aglib.AlgebraicGeometry.Properties.FiniteCoverOpenInduction
public import Aglib.Algebra.Category.ModuleCat.ChangeOfRings.Flat
public import Aglib.Topology.Sheaves.FiniteCoverComparison
public import Mathlib.Topology.Sheaves.Functors

/-! # Native degree-zero flat base change

The original tensor section comparison is invertible on every compact open
of a quasi-separated scheme. This uses only affine sections, finite sheaf
limits, and flatness, not cohomology or Mayer--Vietoris connecting maps.
-/

@[expose] public noncomputable section

universe u

open CategoryTheory Limits Opposite TopologicalSpace

namespace AlgebraicGeometry.Scheme.Cohomology

variable {X Y : Scheme.{u}} {A B : Type u} [CommRing A] [CommRing B]

/-- Flat base change for the original section comparison on a compact open.
The supplied cartesian square, ring map, unit map and coefficient module are
unchanged throughout the finite-cover argument. -/
theorem moduleSectionsTensorComparison_isIso_app_of_flat_of_isPullback
    [QuasiSeparatedSpace X]
    (p : Y ⟶ X) (q : Y ⟶ Spec (.of B)) (f : X ⟶ Spec (.of A))
    (σ : A →+* B) (h : IsPullback p q f (Spec.map (CommRingCat.ofHom σ)))
    (hflat : σ.Flat) (M : X.Modules) [M.IsQuasicoherent]
    (U : X.Opens) (hU : IsCompact (U : Set X)) :
    IsIso ((moduleSectionsTensorComparison p
      (f.appTop.hom.comp (ΓSpecIso (.of A)).inv.hom)
      (q.appTop.hom.comp (ΓSpecIso (.of B)).inv.hom) σ
      (moduleSectionsBaseChangeScalars p q f σ h.w) M).app (op U)) := by
  let α := f.appTop.hom.comp (ΓSpecIso (.of A)).inv.hom
  let β := q.appTop.hom.comp (ΓSpecIso (.of B)).inv.hom
  let η := moduleSectionsTensorComparison p α β σ
    (moduleSectionsBaseChangeScalars p q f σ h.w) M
  let := ModuleCat.extendScalars_preservesFiniteLimits_of_flat σ hflat
  have hF := moduleSectionsPresheaf_isSheaf X α M
  have hG : TopCat.Presheaf.IsSheaf (((Opens.map p.base).op) ⋙
      moduleSectionsPresheaf Y β ((Modules.pullback p).obj M)) :=
    TopCat.Sheaf.pushforward_sheaf_of_sheaf p.base
      (moduleSectionsPresheaf_isSheaf Y β ((Modules.pullback p).obj M))
  apply of_compact_open_of_finiteCover (fun V => IsIso (η.app (op V)))
    (fun V hV => moduleSectionsTensorComparison_isIso_app_of_isPullback p q f σ h M V hV)
    ?_ U hU
  intro ι _ V hV hVV
  exact TopCat.Presheaf.isIso_app_iSup_of_finite hF hG
    (ModuleCat.extendScalars σ) η V hV hVV

end AlgebraicGeometry.Scheme.Cohomology
