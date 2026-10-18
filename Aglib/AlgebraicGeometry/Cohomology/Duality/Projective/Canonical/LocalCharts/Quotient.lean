/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.Cohomology.Duality.Projective.Canonical.LocalCharts
public import Aglib.AlgebraicGeometry.Modules.Differentials.Relative.Conormal.Determinant.Affine

/-!
# Quotient normalization of the regular affine charts

The source chart is reparametrized by the literal quotient by its ordered
regular list. Its closed arrow is consequently the original quotient map
used by the Koszul and derived closed-right-adjoint comparisons.
-/

@[expose] public section
noncomputable section

set_option autoImplicit false
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open CategoryTheory AlgebraicGeometry
universe u

namespace AlgebraicGeometry.Scheme.Modules.Differentials
namespace SmoothClosedImmersionLocalChart

variable {X P Y : Scheme.{u}} {i : X ⟶ P} {p : P ⟶ Y} {n d : ℕ} {x : X}
  (C : SmoothClosedImmersionLocalChart i p n d x)

/-- The original normal-first conormal frame computes the codimension at
the retained chart point, including the rank-zero cases. -/
theorem dimension_eq : n = C.regularList.length + d := by
  let := C.σ.hom.toAlgebra
  exact relativeConormalAffineDimension_eq C.α C.σ C.surjective
    C.regularList C.weaklyRegular C.kernel C.ambientFormallySmooth C.sourceFormallySmooth
    C.sourceBasis n (C.ambientBasis.baseChange C.B) C.point

/-- The original surjection identifies the regular-list quotient with the
source ring of the affine chart. -/
def quotientRingEquiv : (C.A ⧸ Ideal.ofList C.regularList) ≃+* C.B :=
  (Ideal.quotEquivOfEq C.kernel).trans
    (C.σ.hom.quotientKerEquivOfSurjective C.surjective)

@[simp]
theorem quotientRingEquiv_mk (a : C.A) :
    C.quotientRingEquiv (Ideal.Quotient.mk (Ideal.ofList C.regularList) a) = C.σ a := by
  simp [quotientRingEquiv]

/-- The affine source chart written on the literal regular-list quotient. -/
def quotientSource : Spec (CommRingCat.of (C.A ⧸ Ideal.ofList C.regularList)) ⟶ X :=
  Spec.map C.quotientRingEquiv.toCommRingCatIso.inv ≫ C.jX

instance quotientSource_isOpenImmersion : IsOpenImmersion C.quotientSource := by
  let := C.openX
  dsimp only [quotientSource]
  infer_instance

private theorem quotientMap_eq :
    CommRingCat.ofHom (Ideal.Quotient.mk (Ideal.ofList C.regularList)) =
      C.σ ≫ C.quotientRingEquiv.toCommRingCatIso.inv := by
  ext a
  apply C.quotientRingEquiv.injective
  simp

/-- Quotient normalization retains the same actual closed-immersion square. -/
@[reassoc]
theorem quotientSource_square :
    Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk (Ideal.ofList C.regularList))) ≫ C.jP =
      C.quotientSource ≫ i := by
  rw [C.quotientMap_eq, Spec.map_comp, Category.assoc, C.closedSquare]
  rfl

/-- The same source relative dimension holds for the literal quotient map. -/
theorem quotientSource_standardSmooth :
    RingHom.IsStandardSmoothOfRelativeDimension d
      (C.α ≫ CommRingCat.ofHom (Ideal.Quotient.mk (Ideal.ofList C.regularList))).hom := by
  rw [C.quotientMap_eq, ← Category.assoc, CommRingCat.hom_comp]
  exact RingHom.isStandardSmoothOfRelativeDimension_respectsIso.left
    (C.α ≫ C.σ).hom C.quotientRingEquiv.symm C.sourceSmooth

/-- The quotient-normalized closed square is the same actual pullback. -/
theorem quotientSource_isPullback :
    IsPullback C.quotientSource
      (Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk (Ideal.ofList C.regularList))))
      i C.jP := by
  let q : C.A ⟶ CommRingCat.of (C.A ⧸ Ideal.ofList C.regularList) :=
    CommRingCat.ofHom (Ideal.Quotient.mk (Ideal.ofList C.regularList))
  change IsPullback C.quotientSource (Spec.map q) i C.jP
  have h : IsPullback (Spec.map C.quotientRingEquiv.toCommRingCatIso.inv)
      (Spec.map q) (Spec.map C.σ) (𝟙 (Spec C.A)) :=
    IsPullback.of_horiz_isIso ⟨by
      rw [Category.comp_id]
      change Spec.map C.quotientRingEquiv.toCommRingCatIso.inv ≫ Spec.map C.σ =
        Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk (Ideal.ofList C.regularList)))
      rw [← Spec.map_comp, ← C.quotientMap_eq]⟩
  simpa only [quotientSource, Category.id_comp] using h.paste_horiz C.cartesian

/-- Quotient-normalized charts keep all point, frame and regularity data;
their ring map is definitionally the regular-list quotient map. -/
def quotientChart : SmoothClosedImmersionLocalChart i p n d x where
  R := C.R
  A := C.A
  B := CommRingCat.of (C.A ⧸ Ideal.ofList C.regularList)
  α := C.α
  σ := CommRingCat.ofHom (Ideal.Quotient.mk (Ideal.ofList C.regularList))
  surjective := Ideal.Quotient.mk_surjective
  jY := C.jY
  jP := C.jP
  jX := C.quotientSource
  openY := C.openY
  openP := C.openP
  openX := inferInstance
  ambientSquare := C.ambientSquare
  closedSquare := C.quotientSource_square
  cartesian := C.quotientSource_isPullback
  point := PrimeSpectrum.comap C.quotientRingEquiv.toRingHom C.point
  point_eq := by
    have h := congrArg (fun f : Spec C.B ⟶ Spec C.B => f C.point)
      (show Spec.map C.quotientRingEquiv.toCommRingCatIso.hom ≫
          Spec.map C.quotientRingEquiv.toCommRingCatIso.inv = 𝟙 (Spec C.B) from by
        rw [← Spec.map_comp, Iso.inv_hom_id, Spec.map_id]
        rfl)
    change C.jX ((Spec.map C.quotientRingEquiv.toCommRingCatIso.inv)
      ((Spec.map C.quotientRingEquiv.toCommRingCatIso.hom) C.point)) = x
    exact (congrArg C.jX h).trans C.point_eq
  regularList := C.regularList
  weaklyRegular := C.weaklyRegular
  kernel := Ideal.mk_ker.symm
  ambientSmooth := C.ambientSmooth
  sourceSmooth := C.quotientSource_standardSmooth

end SmoothClosedImmersionLocalChart
end AlgebraicGeometry.Scheme.Modules.Differentials
