/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.Cohomology.Cech.Finite.FlatModel
public import Aglib.AlgebraicGeometry.Cohomology.Cech.Finite.GeometricHomology
public import Aglib.AlgebraicGeometry.Cohomology.Cech.DegreeZero.Geometric
public import Aglib.AlgebraicGeometry.Cohomology.Cech.Geometric
public import Aglib.AlgebraicGeometry.Cohomology.BaseChange.Modules.Map.Spec

/-!
# Geometric normalization of the bounded Cech base-change model

The all-base-change computation from the original bounded flat Cech complex
retains the original geometric pullback on a unit pure tensor. Consequently
its native homology mate represents the original cohomology base-change map,
rather than merely some isomorphism between the cohomology modules.
-/

@[expose] public section

noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry TopologicalSpace Opposite
open HomologicalComplex CategoryTheory.Cech
open scoped TensorProduct ChangeOfRings

namespace AlgebraicGeometry.Scheme.Cohomology

variable {R B : Type u} [CommRing R] [CommRing B] {X : Scheme.{u}} [X.IsSeparated]
  (f : X ⟶ Spec (CommRingCat.of R)) (M : X.Modules) [M.IsQuasicoherent]
  (hflat : Scheme.Modules.relativeFlat f M) {ι : Type u} (U : ι → X.Opens)
  (n : ℕ) (e : ι ≃ Fin (n + 1)) (hU : ∀ i, IsAffineOpen (U i))
  (hcover : iSup U = ⊤) (σ : R →+* B)

/-- The all-base-change bounded Cech computation sends the native homology
mate of a unit pure tensor to the original ordinary geometric pullback on
unchanged sheaf cohomology. -/
theorem moduleFiniteCechBaseChangeCohomologyLinearEquiv_one_tmul (q : ℕ)
    (x : (moduleFiniteCechComplex X
      (f.appTop.hom.comp (Scheme.ΓSpecIso (CommRingCat.of R)).inv.hom) U M n).homology
      (q : ℤ)) :
    moduleFiniteCechBaseChangeCohomologyLinearEquiv f M hflat U n e hU hcover σ q
        (extendScalarsHomologyMap σ
          (moduleFiniteCechComplex X
            (f.appTop.hom.comp (Scheme.ΓSpecIso (CommRingCat.of R)).inv.hom) U M n)
          (q : ℤ) ((1 : B) ⊗ₜ[R,σ] x)) =
      moduleCohomologyPullback (pullback.fst f (Spec.map (CommRingCat.ofHom σ))) M q
        (moduleFiniteCechCohomologyLinearEquiv X
          (f.appTop.hom.comp (Scheme.ΓSpecIso (CommRingCat.of R)).inv.hom)
          U M n e hU hcover q x) := by
  let : Fintype ι := Fintype.ofEquiv (Fin (n + 1)) e.symm
  let Y := pullback f (Spec.map (CommRingCat.ofHom σ))
  let p : Y ⟶ X := pullback.fst f (Spec.map (CommRingCat.ofHom σ))
  let r : Y ⟶ Spec (CommRingCat.of B) := pullback.snd f (Spec.map (CommRingCat.ofHom σ))
  let α := f.appTop.hom.comp (Scheme.ΓSpecIso (CommRingCat.of R)).inv.hom
  let β := r.appTop.hom.comp (Scheme.ΓSpecIso (CommRingCat.of B)).inv.hom
  let N := (Scheme.Modules.pullback p).obj M
  let V : ι → Y.Opens := fun i => p ⁻¹ᵁ U i
  let : IsAffineHom p := MorphismProperty.pullback_fst f
    (Spec.map (CommRingCat.ofHom σ))
    (inferInstance : IsAffineHom (Spec.map (CommRingCat.ofHom σ)))
  let : Y.IsSeparated := ⟨by rw [← terminal.comp_from p]; infer_instance⟩
  let : N.IsQuasicoherent := Scheme.Modules.quasicoherent_pullback p M
  let K := moduleFiniteCechComplex X α U M n
  let L := moduleFiniteCechComplex Y β V N n
  let C := moduleCechIntComplex X α U M
  let D := moduleCechIntComplex Y β V N
  let a : K ⟶ C := moduleFiniteCechInclusion X α U M n
  let b : L ⟶ D := moduleFiniteCechInclusion Y β V N n
  let δ : ((ModuleCat.extendScalars σ).mapHomologicalComplex (.up ℤ)).obj K ⟶ L :=
    (moduleFiniteCechBaseChangeIso f M hflat U n e hU hcover σ).hom
  let z := extendScalarsHomologyMap σ K (q : ℤ) ((1 : B) ⊗ₜ[R,σ] x)
  let xInt := homologyMap a (q : ℤ) x
  let yInt := homologyMap b (q : ℤ) (homologyMap δ (q : ℤ) z)
  let xNat := ((moduleCechComplex X α M U).extendHomologyIso
    ComplexShape.embeddingUpNat (j := q) (j' := (q : ℤ)) rfl).hom xInt
  let yNat := ((moduleCechComplex Y β N V).extendHomologyIso
    ComplexShape.embeddingUpNat (j := q) (j' := (q : ℤ)) rfl).hom yInt
  have hy : yInt = homologyMap (moduleCechIntBaseChangeMap f σ M U) (q : ℤ)
      (extendScalarsHomologyMap σ C (q : ℤ) ((1 : B) ⊗ₜ[R,σ] xInt)) := by
    have hc := congrArg (fun φ => homologyMap φ (q : ℤ))
      (moduleFiniteCechBaseChangeIso_hom_ιTruncLE f M hflat U n e hU hcover σ)
    simp only [homologyMap_comp] at hc
    have hn := ModuleCat.homologyBaseChangeMap_naturality σ
      ((shortComplexFunctor (ModuleCat.{u} R) (.up ℤ) (q : ℤ)).map a)
    have hx := ConcreteCategory.congr_hom hn ((1 : B) ⊗ₜ[R,σ] x)
    simp only [ConcreteCategory.comp_apply] at hx
    exact (ConcreteCategory.congr_hom hc z).trans
      (congrArg (homologyMap (moduleCechIntBaseChangeMap f σ M U) (q : ℤ)) hx.symm)
  have hxy := moduleCechIntBaseChangeHomologyMap_one_tmul M U f σ q xInt
  dsimp only at hxy
  rw [← hy] at hxy
  simp only [moduleCechIntAdditiveHomologyIso_hom, ConcreteCategory.comp_apply] at hxy
  change (moduleCechAdditiveHomologyIso Y β N V q).hom yNat =
    homologyMap
      (additiveCechGeometricMap p U (moduleAddSheaf X M) (moduleAddSheaf Y N)
        (moduleCoefficientPullback p
          ((Scheme.Modules.pullbackPushforwardAdjunction p).unit.app M))) q
      ((moduleCechAdditiveHomologyIso X α M U q).hom xNat) at hxy
  have hV : ∀ i, IsAffineOpen (V i) := fun i => (hU i).preimage p
  have hVcover : iSup V = ⊤ := p.iSup_preimage_eq_top hcover
  cases q with
  | zero =>
    change moduleCechCohomologyLinearEquivZero Y β N V hVcover yNat =
      moduleCohomologyMapAlong p
        ((Scheme.Modules.pullbackPushforwardAdjunction p).unit.app M) 0
        (moduleCechCohomologyLinearEquivZero X α M U hcover xNat)
    exact moduleCechCohomologyLinearEquivZero_geometric p U
      ((Scheme.Modules.pullbackPushforwardAdjunction p).unit.app M) α β hcover xNat yNat hxy
  | succ q =>
    have haff : ∀ (t : ℕ) (a : Fin (t + 1) → ι), IsAffineOpen (∏ᶜ fun k => U (a k)) := by
      intro t a
      have he : (∏ᶜ fun k => U (a k)) = ⨅ k, U (a k) := by
        apply le_antisymm
        · exact le_iInf fun k => leOfHom (Pi.π _ k)
        · exact leOfHom (Pi.lift fun k => homOfLE (iInf_le _ k))
      rw [he]
      exact IsAffineOpen.iInf (fun k => hU (a k))
    have haff' : ∀ (t : ℕ) (a : Fin (t + 1) → ι), IsAffineOpen (∏ᶜ fun k => V (a k)) := by
      intro t a
      have he : (∏ᶜ fun k => V (a k)) = ⨅ k, V (a k) := by
        apply le_antisymm
        · exact le_iInf fun k => leOfHom (Pi.π _ k)
        · exact leOfHom (Pi.lift fun k => homOfLE (iInf_le _ k))
      rw [he]
      exact IsAffineOpen.iInf (fun k => hV (a k))
    change moduleCechCohomologyAddEquiv V N (injectiveResolution (moduleAddSheaf Y N))
        hVcover haff' q ((moduleCechAdditiveHomologyIso Y β N V (q + 1)).hom yNat) =
      moduleCohomologyMapAlong p
        ((Scheme.Modules.pullbackPushforwardAdjunction p).unit.app M) (q + 1)
        (moduleCechCohomologyAddEquiv U M (injectiveResolution (moduleAddSheaf X M))
          hcover haff q ((moduleCechAdditiveHomologyIso X α M U (q + 1)).hom xNat))
    rw [hxy]
    exact moduleCechCohomologyAddEquiv_geometric p U M N
      (injectiveResolution (moduleAddSheaf X M)) (injectiveResolution (moduleAddSheaf Y N))
      hcover hVcover haff haff'
      (moduleCoefficientPullback p
        ((Scheme.Modules.pullbackPushforwardAdjunction p).unit.app M)) q _

end AlgebraicGeometry.Scheme.Cohomology
