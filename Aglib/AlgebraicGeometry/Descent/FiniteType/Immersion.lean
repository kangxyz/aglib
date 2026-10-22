/-
Copyright (c) 2026 algebraic-geometry contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.Descent.FinitePresentation.AffineAtlas
public import Aglib.AlgebraicGeometry.Morphisms.FiniteType.Generators
public import Aglib.AlgebraicGeometry.Morphisms.Immersion.ProductCharts
public import Aglib.AlgebraicGeometry.Products.IntegerBase

/-!
# A finite-type map and a supplied approximation give an immersion at a stage

The approximation is an actual diagram and limiting cone. The literal pair of
its stage projection and the original locally finite-type map is an immersion
at some stage. No existence of an absolute approximation or hull is assumed.
-/

@[expose] public noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true

universe u

open CategoryTheory CategoryTheory.Limits TopologicalSpace

namespace AlgebraicGeometry.Scheme

open Products

/-- The literal pair into the product over the actual universe-lifted integer base. -/
def integerBasePair {X Y S : Scheme.{u}} (p : X ⟶ Y) (q : X ⟶ S) :
    X ⟶ pullback (toIntegerBase Y) (toIntegerBase S) :=
  pullback.lift p q (by simp)

@[reassoc (attr := simp)]
lemma integerBasePair_fst {X Y S : Scheme.{u}} (p : X ⟶ Y) (q : X ⟶ S) :
    integerBasePair p q ≫ pullback.fst _ _ = p := by simp [integerBasePair]

@[reassoc (attr := simp)]
lemma integerBasePair_snd {X Y S : Scheme.{u}} (p : X ⟶ Y) (q : X ⟶ S) :
    integerBasePair p q ≫ pullback.snd _ _ = q := by simp [integerBasePair]

/-- The stage projection and a locally finite-type map jointly give an immersion
at some actual stage of a supplied qcqs affine-transition limit. -/
lemma exists_isImmersion_integerBasePair_of_isLimit
    {I : Type u} [Category.{u} I] [IsCofiltered I]
    (D : I ⥤ Scheme.{u}) (c : Cone D) (hc : IsLimit c)
    [∀ {i j} (f : i ⟶ j), IsAffineHom (D.map f)]
    [∀ i, CompactSpace (D.obj i)] [∀ i, QuasiSeparatedSpace (D.obj i)]
    {S : Scheme.{u}} (f : c.pt ⟶ S) [LocallyOfFiniteType f] :
    ∃ i : I, IsImmersion (integerBasePair (c.π.app i) f) := by
  classical
  let : CompactSpace c.pt := compactSpace_of_isLimit D c hc
  obtain ⟨J, V, U, hcover, hVU⟩ := f.exists_finite_affine_cover_subordinate
  let q (a : J) : (V a).toScheme ⟶ (U a).toScheme :=
    f.resLE (U a) (V a) (hVU a).2.2
  have (a : J) : IsAffine (V a).toScheme := (hVU a).1
  have (a : J) : IsAffine (U a).toScheme := (hVU a).2.1
  have (a : J) : LocallyOfFiniteType (q a) := by
    dsimp [q, Hom.resLE]
    infer_instance
  let (a : J) : Algebra Γ((U a).toScheme, ⊤) Γ((V a).toScheme, ⊤) :=
    (q a).appTop.hom.toAlgebra
  have hfin (a : J) : Algebra.FiniteType Γ((U a).toScheme, ⊤)
      Γ((V a).toScheme, ⊤) :=
    (HasRingHomProperty.iff_of_isAffine (P := @LocallyOfFiniteType)).mp inferInstance
  choose G hG using fun a => (hfin a).out
  obtain ⟨i, W, _, hW, e, t, ht⟩ := exists_affine_atlas_with_sections_of_isLimit
    D c hc V hcover (fun a => (hVU a).1)
    (fun a (z : G a) => (V a).topIso.hom z.val)
  refine ⟨i, ?_⟩
  apply isImmersion_pullback_lift_of_cover (toIntegerBase (D.obj i))
    (toIntegerBase S) (c.π.app i) f (by simp) V W U hcover e
    (fun a => (hVU a).2.2)
  intro a
  have : IsAffine (W a).toScheme := hW a
  let p : (V a).toScheme ⟶ (W a).toScheme :=
    (c.π.app i).resLE (W a) (V a) (e a).le
  have hgen : (G a : Set Γ((V a).toScheme, ⊤)) ⊆ Set.range p.appTop := by
    intro z hz
    let z' : G a := ⟨z, hz⟩
    refine ⟨(W a).topIso.inv (t a z'), ?_⟩
    have hw : (W a).topIso.inv ≫ p.appTop =
        (c.π.app i).appLE (W a) (V a) (e a).le ≫ (V a).topIso.inv :=
      (arrowResLEAppIso (c.π.app i) (W a) (V a) (e a).le).inv.w
    have hw' := congrArg (fun k : Γ(D.obj i, W a) ⟶ Γ((V a).toScheme, ⊤) =>
      k (t a z')) hw
    rw [CommRingCat.comp_apply, CommRingCat.comp_apply, ← ht a z'] at hw'
    exact hw'.trans ((V a).topIso.commRingCatIsoToRingEquiv.symm_apply_apply z)
  have : IsClosedImmersion
      (pullbackLiftResLE (toIntegerBase (D.obj i)) (toIntegerBase S)
        (c.π.app i) f (by simp) (V a) (W a) (U a) (e a).le (hVU a).2.2) := by
    apply Hom.isClosedImmersion_pullback_lift_of_generators
      ((W a).ι ≫ toIntegerBase (D.obj i)) ((U a).ι ≫ toIntegerBase S)
      p (q a) _ (G a : Set Γ((V a).toScheme, ⊤)) (hG a) hgen
  infer_instance

end AlgebraicGeometry.Scheme
