/-
Copyright (c) 2026 algebraic-geometry contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.Cohomology.Cech.ModuleBaseChange

/-! # The original Cech tensor comparison for a supplied fibre square

The affine section comparison proves invertibility for the actual supplied
cartesian square over spectra. The Cech map keeps those original forward
maps, its native finite-product comparison and the original geometric unit.
No chosen pullback object, flatness or finiteness of cohomology is needed.
-/

@[expose] public section

noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry TopologicalSpace Opposite
open HomologicalComplex CategoryTheory.Cech

namespace AlgebraicGeometry.Scheme.Cohomology

variable {X Y : Scheme.{u}} {A B : Type u} [CommRing A] [CommRing B]

/-- In a supplied fibre square, the original section tensor comparison is invertible on
all tuple intersections of an affine family in a separated scheme. -/
theorem moduleCechTensorComparison_isIso_of_isPullback [X.IsSeparated]
    (p : Y ⟶ X) (q : Y ⟶ Spec (CommRingCat.of B))
    (f : X ⟶ Spec (CommRingCat.of A)) (σ : A →+* B)
    (h : IsPullback p q f (Spec.map (CommRingCat.ofHom σ)))
    (M : X.Modules) [M.IsQuasicoherent] {ι : Type u} (U : ι → X.Opens)
    (hU : ∀ i, IsAffineOpen (U i)) :
    IsIso ((cechComplexFunctor U).map (moduleSectionsTensorComparison p
      (f.appTop.hom.comp (Scheme.ΓSpecIso (CommRingCat.of A)).inv.hom)
      (q.appTop.hom.comp (Scheme.ΓSpecIso (CommRingCat.of B)).inv.hom) σ
      (moduleSectionsBaseChangeScalars p q f σ h.w) M)) := by
  let α := f.appTop.hom.comp (Scheme.ΓSpecIso (CommRingCat.of A)).inv.hom
  let β := q.appTop.hom.comp (Scheme.ΓSpecIso (CommRingCat.of B)).inv.hom
  let τ := moduleSectionsTensorComparison p α β σ
    (moduleSectionsBaseChangeScalars p q f σ h.w) M
  have hn (n : ℕ) : IsIso (((cechComplexFunctor U).map τ).f n) := by
    have hi (a : Fin (n + 1) → ι) : IsIso (τ.app (op (∏ᶜ fun k => U (a k)))) := by
      apply moduleSectionsTensorComparison_isIso_app_of_isPullback p q f σ h M
      have he : (∏ᶜ fun k => U (a k)) = ⨅ k, U (a k) := by
        apply le_antisymm
        · exact le_iInf fun k => leOfHom (Pi.π _ k)
        · exact leOfHom (Pi.lift fun k => homOfLE (iInf_le _ k))
      rw [he]
      exact IsAffineOpen.iInf (fun k => hU (a k))
    let := hi
    change IsIso (Limits.Pi.map (fun a : Fin (n + 1) → ι =>
      τ.app (op (∏ᶜ fun k => U (a k)))))
    infer_instance
  let := hn
  exact HomologicalComplex.Hom.isIso_of_components _

/-- The original finite Cech tensor map is invertible for the actual supplied cartesian
square, with the original module pullback unit as coefficient arrow. -/
theorem moduleCechTensorMapAlong_isIso_of_isPullback [X.IsSeparated]
    (p : Y ⟶ X) (q : Y ⟶ Spec (CommRingCat.of B))
    (f : X ⟶ Spec (CommRingCat.of A)) (σ : A →+* B)
    (h : IsPullback p q f (Spec.map (CommRingCat.ofHom σ)))
    (M : X.Modules) [M.IsQuasicoherent] {ι : Type u} [Finite ι]
    (U : ι → X.Opens) (hU : ∀ i, IsAffineOpen (U i)) :
    IsIso (moduleCechTensorMapAlong p σ
      (f.appTop.hom.comp (Scheme.ΓSpecIso (CommRingCat.of A)).inv.hom)
      (q.appTop.hom.comp (Scheme.ΓSpecIso (CommRingCat.of B)).inv.hom)
      (moduleSectionsBaseChangeScalars p q f σ h.w)
      ((Scheme.Modules.pullbackPushforwardAdjunction p).unit.app M) U) := by
  let α := f.appTop.hom.comp (Scheme.ΓSpecIso (CommRingCat.of A)).inv.hom
  let β := q.appTop.hom.comp (Scheme.ΓSpecIso (CommRingCat.of B)).inv.hom
  have := moduleCechTensorComparison_isIso_of_isPullback p q f σ h M U hU
  change IsIso ((finiteCechComplexCoefficientIso (ModuleCat.extendScalars σ) U
    (moduleSectionsPresheaf X α M)).hom ≫
      (cechComplexFunctor U).map (moduleSectionsTensorComparison p α β σ
        (moduleSectionsBaseChangeScalars p q f σ h.w) M) ≫
      (moduleCechGeometricIso p β ((Scheme.Modules.pullback p).obj M) U).hom)
  infer_instance

end AlgebraicGeometry.Scheme.Cohomology
