/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.Cohomology.ClosedImmersion.RightAdjoint.FiniteSource.Derived
public import Mathlib.RingTheory.IsTensorProduct
public import Mathlib.RingTheory.TensorProduct.Quotient

/-!
# The original mapped-ideal quotient chart

The existing quotient pushout and native Cartesian pasting construct the chart
on the original scheme pullback. Both Cartesian squares use the same native
pullback lift. No flatness, Noetherianity or derived coefficient is required.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits
open TensorProduct
open scoped TensorProduct

universe u

namespace AlgebraicGeometry.Scheme.Modules

/-- The original quotient map square is an algebra pushout, without flatness
or Noetherianity assumptions. -/
theorem quotientFlatChart_isPushout
    {R S : Type u} [CommRing R] [CommRing S] [Algebra R S] (I : Ideal R) :
    Algebra.IsPushout R S (R ⧸ I) (S ⧸ I.map (algebraMap R S)) := by
  constructor
  refine IsBaseChange.of_equiv
    (Algebra.TensorProduct.quotIdealMapEquivTensorQuot S I).symm.toLinearEquiv ?_
  intro x
  obtain ⟨r, rfl⟩ := Ideal.Quotient.mk_surjective x
  change (Algebra.TensorProduct.quotIdealMapEquivTensorQuot S I).symm
      ((1 : S) ⊗ₜ[R] (Ideal.Quotient.mk I r)) =
    algebraMap (R ⧸ I) (S ⧸ I.map (algebraMap R S)) (Ideal.Quotient.mk I r)
  simp only [Algebra.TensorProduct.quotIdealMapEquivTensorQuot_symm_tmul,
    Ideal.Quotient.algebraMap_quotient_map_quotient, Algebra.smul_def, mul_one]
  rfl

/-- The existing quotient pushout, viewed on the original spectra. -/
theorem quotientChart_isPullback
    (R S : CommRingCat.{u}) [Algebra R S] (I : Ideal R) :
    IsPullback
      (Spec.map (CommRingCat.ofHom
        (algebraMap (R ⧸ I) (S ⧸ I.map (algebraMap R S)))))
      (Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk (I.map (algebraMap R S)))))
      (Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk I)))
      (Spec.map (CommRingCat.ofHom (algebraMap R S))) := by
  let : Algebra.IsPushout R S (R ⧸ I) (S ⧸ I.map (algebraMap R S)) :=
    quotientFlatChart_isPushout I
  exact (isPullback_SpecMap_of_isPushout _ _ _ _
    (CommRingCat.isPushout_of_isPushout R S (R ⧸ I)
      (S ⧸ I.map (algebraMap R S)))).flip

namespace ClosedImmersionAffineQuotientChart

variable {X Y Y' : Scheme.{u}} {i : X ⟶ Y}
    {R S : CommRingCat.{u}} [Algebra R S] {a : Spec R ⟶ Y}
    (C : ClosedImmersionAffineQuotientChart i R a)
    (g : Y' ⟶ Y) (b : Spec S ⟶ Y')
    (H : IsPullback (Spec.map (CommRingCat.ofHom (algebraMap R S))) b a g)

include H in
/-- The original quotient-source map followed by the chosen source chart
and the original target quotient map define a cone over `i` and `g`. -/
theorem baseChangeSourceMap_condition :
    (Spec.map (CommRingCat.ofHom
      (algebraMap (R ⧸ C.ideal) (S ⧸ C.ideal.map (algebraMap R S)))) ≫
        C.sourceMap) ≫ i =
    (Spec.map (CommRingCat.ofHom
      (Ideal.Quotient.mk (C.ideal.map (algebraMap R S)))) ≫ b) ≫ g := by
  rw [Category.assoc, C.square.w, ← Category.assoc,
    (quotientChart_isPullback R S C.ideal).w, Category.assoc, H.w, Category.assoc]

/-- The target chart map is the native lift into the SAME scheme pullback. -/
def baseChangeSourceMap :
    Spec (.of (S ⧸ C.ideal.map (algebraMap R S))) ⟶ CategoryTheory.Limits.pullback i g :=
  pullback.lift
    (Spec.map (CommRingCat.ofHom
      (algebraMap (R ⧸ C.ideal) (S ⧸ C.ideal.map (algebraMap R S)))) ≫ C.sourceMap)
    (Spec.map (CommRingCat.ofHom
      (Ideal.Quotient.mk (C.ideal.map (algebraMap R S)))) ≫ b)
    (C.baseChangeSourceMap_condition g b H)

/-- The native lift retains the original quotient-source map. -/
@[reassoc (attr := simp)]
theorem baseChangeSourceMap_fst :
    C.baseChangeSourceMap g b H ≫ pullback.fst i g =
      Spec.map (CommRingCat.ofHom
        (algebraMap (R ⧸ C.ideal) (S ⧸ C.ideal.map (algebraMap R S)))) ≫
          C.sourceMap := by
  simp only [baseChangeSourceMap, pullback.lift_fst]

/-- The native lift retains the original target quotient map. -/
@[reassoc (attr := simp)]
theorem baseChangeSourceMap_snd :
    C.baseChangeSourceMap g b H ≫ pullback.snd i g =
      Spec.map (CommRingCat.ofHom
        (Ideal.Quotient.mk (C.ideal.map (algebraMap R S)))) ≫ b := by
  simp only [baseChangeSourceMap, pullback.lift_snd]

/-- The literal mapped-ideal quotient is the chart of the base-changed source. -/
theorem baseChangeSourceMap_isPullback :
    IsPullback (C.baseChangeSourceMap g b H)
      (Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk (C.ideal.map (algebraMap R S)))))
      (pullback.snd i g) b := by
  have h := (quotientChart_isPullback R S C.ideal).paste_horiz C.square
  rw [H.w] at h
  have houter : IsPullback
      (C.baseChangeSourceMap g b H ≫ pullback.fst i g)
      (Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk (C.ideal.map (algebraMap R S)))))
      i (b ≫ g) := by
    rw [C.baseChangeSourceMap_fst]
    exact h
  exact houter.of_right (C.baseChangeSourceMap_snd g b H)
    (IsPullback.of_hasPullback i g)

/-- Restricting the original projection uses the SAME target chart lift. -/
theorem baseChangeSourceMap_projection_isPullback :
    IsPullback
      (Spec.map (CommRingCat.ofHom
        (algebraMap (R ⧸ C.ideal) (S ⧸ C.ideal.map (algebraMap R S)))))
      (C.baseChangeSourceMap g b H) C.sourceMap (pullback.fst i g) := by
  have h := (quotientChart_isPullback R S C.ideal).paste_vert H
  rw [← C.square.w] at h
  have houter : IsPullback
      (Spec.map (CommRingCat.ofHom
        (algebraMap (R ⧸ C.ideal) (S ⧸ C.ideal.map (algebraMap R S)))))
      (C.baseChangeSourceMap g b H ≫ pullback.snd i g)
      (C.sourceMap ≫ i) g := by
    rw [C.baseChangeSourceMap_snd]
    exact h
  exact houter.of_bot (C.baseChangeSourceMap_fst g b H).symm
    (IsPullback.of_hasPullback i g)

/-- The target chart is open because it is the pullback of the given open. -/
instance [IsOpenImmersion b] : IsOpenImmersion (C.baseChangeSourceMap g b H) :=
  MorphismProperty.of_isPullback (C.baseChangeSourceMap_isPullback g b H).flip
    (show IsOpenImmersion b from inferInstance)

/-- Package the actual mapped ideal and the original lift, without choosing
an unrelated target quotient presentation. -/
def baseChange [IsOpenImmersion b] :
    ClosedImmersionAffineQuotientChart (pullback.snd i g) S b where
  ideal := C.ideal.map (algebraMap R S)
  sourceMap := C.baseChangeSourceMap g b H
  isOpenImmersion := inferInstance
  square := C.baseChangeSourceMap_isPullback g b H

/-- The packaged ideal is literally the original mapped ideal. -/
@[simp]
theorem baseChange_ideal [IsOpenImmersion b] :
    (C.baseChange g b H).ideal = C.ideal.map (algebraMap R S) := rfl

/-- The packaged source map is literally the original native lift. -/
@[simp]
theorem baseChange_sourceMap [IsOpenImmersion b] :
    (C.baseChange g b H).sourceMap = C.baseChangeSourceMap g b H := rfl

end ClosedImmersionAffineQuotientChart

end AlgebraicGeometry.Scheme.Modules
