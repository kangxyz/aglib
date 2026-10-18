/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.Cohomology.Duality.Projective.Canonical.LocalCharts.Quotient

/-!
# Isomorphic presentations of actual regular affine charts

An ambient ring isomorphism transports the original ordered kernel list.
A base ring isomorphism changes only the base presentation. The actual
point, source map, commuting squares and prescribed smooth dimensions
are retained, and the ambient closed square remains Cartesian.
-/

@[expose] public section
noncomputable section
set_option autoImplicit false
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

universe u
namespace AlgebraicGeometry.Scheme.Modules.Differentials
namespace SmoothClosedImmersionLocalChart

private theorem weaklyRegular_map_iso {A A' : CommRingCat.{u}} (e : A ≅ A')
    (s : List A) (hs : RingTheory.Sequence.IsWeaklyRegular A s) :
    RingTheory.Sequence.IsWeaklyRegular A' (s.map e.hom.hom) := by
  refine (AddEquiv.isWeaklyRegular_congr
    (e := e.commRingCatIsoToRingEquiv.toAddEquiv) ?_).mp hs
  apply List.forall₂_map_right_iff.mpr
  apply List.forall₂_same.mpr
  intro r _ z
  exact map_mul e.hom.hom r z

variable {X P Y : Scheme.{u}} {i : X ⟶ P} {p : P ⟶ Y} {n d : ℕ} {x : X}
  (C : SmoothClosedImmersionLocalChart i p n d x)

private theorem ambientReparametrization_isPullback {A' : CommRingCat.{u}} (e : C.A ≅ A') :
    IsPullback C.jX (Spec.map (e.inv ≫ C.σ)) i (Spec.map e.hom ≫ C.jP) := by
  have H : IsPullback (𝟙 (Spec C.B)) (Spec.map (e.inv ≫ C.σ))
      (Spec.map C.σ) (Spec.map e.hom) :=
    IsPullback.of_horiz_isIso ⟨by
      rw [Category.id_comp, ← Spec.map_comp, e.hom_inv_id_assoc]⟩
  simpa only [Category.id_comp] using H.paste_horiz C.cartesian

/-- Reparametrize the ambient ring by the given isomorphism and its literal mapped list. -/
def ambientIsoChart {A' : CommRingCat.{u}} (e : C.A ≅ A') :
    SmoothClosedImmersionLocalChart i p n d x where
  R := C.R
  A := A'
  B := C.B
  α := C.α ≫ e.hom
  σ := e.inv ≫ C.σ
  surjective := C.surjective.comp e.symm.commRingCatIsoToRingEquiv.surjective
  jY := C.jY
  jP := Spec.map e.hom ≫ C.jP
  jX := C.jX
  openY := C.openY
  openP := by
    let := C.openP
    infer_instance
  openX := C.openX
  ambientSquare := by
    simp only [Spec.map_comp, Category.assoc, C.ambientSquare]
  closedSquare := by
    calc
      Spec.map (e.inv ≫ C.σ) ≫ (Spec.map e.hom ≫ C.jP) =
          Spec.map (e.hom ≫ e.inv ≫ C.σ) ≫ C.jP := by
        simp only [Spec.map_comp, Category.assoc]
      _ = Spec.map C.σ ≫ C.jP := by rw [e.hom_inv_id_assoc]
      _ = C.jX ≫ i := C.closedSquare
  cartesian := by exact C.ambientReparametrization_isPullback e
  point := C.point
  point_eq := C.point_eq
  regularList := C.regularList.map e.hom.hom
  weaklyRegular := by exact weaklyRegular_map_iso e C.regularList C.weaklyRegular
  kernel := by
    rw [← Ideal.map_ofList, C.kernel]
    exact (Ideal.map_comap_of_equiv (I := RingHom.ker C.σ.hom)
      e.commRingCatIsoToRingEquiv).trans (RingHom.comap_ker C.σ.hom e.inv.hom)
  ambientSmooth := by
    exact RingHom.isStandardSmoothOfRelativeDimension_respectsIso.left
      C.α.hom e.commRingCatIsoToRingEquiv C.ambientSmooth
  sourceSmooth := by
    simpa only [Category.assoc, e.hom_inv_id_assoc] using C.sourceSmooth

/-- Reparametrize the base ring while retaining the actual ambient and source charts. -/
def baseIsoChart {R' : CommRingCat.{u}} (e : C.R ≅ R') :
    SmoothClosedImmersionLocalChart i p n d x where
  R := R'
  A := C.A
  B := C.B
  α := e.inv ≫ C.α
  σ := C.σ
  surjective := C.surjective
  jY := Spec.map e.hom ≫ C.jY
  jP := C.jP
  jX := C.jX
  openY := by
    let := C.openY
    infer_instance
  openP := C.openP
  openX := C.openX
  ambientSquare := by
    calc
      Spec.map (e.inv ≫ C.α) ≫ (Spec.map e.hom ≫ C.jY) =
          Spec.map (e.hom ≫ e.inv ≫ C.α) ≫ C.jY := by
        simp only [Spec.map_comp, Category.assoc]
      _ = Spec.map C.α ≫ C.jY := by rw [e.hom_inv_id_assoc]
      _ = C.jP ≫ p := C.ambientSquare
  closedSquare := C.closedSquare
  cartesian := C.cartesian
  point := C.point
  point_eq := C.point_eq
  regularList := C.regularList
  weaklyRegular := C.weaklyRegular
  kernel := C.kernel
  ambientSmooth := by
    exact RingHom.isStandardSmoothOfRelativeDimension_respectsIso.right
      C.α.hom e.symm.commRingCatIsoToRingEquiv C.ambientSmooth
  sourceSmooth := by
    change RingHom.IsStandardSmoothOfRelativeDimension d
      ((C.α ≫ C.σ).hom.comp e.inv.hom)
    exact RingHom.isStandardSmoothOfRelativeDimension_respectsIso.right
      (C.α ≫ C.σ).hom e.symm.commRingCatIsoToRingEquiv C.sourceSmooth

section AmbientFields
variable {A' : CommRingCat.{u}} (e : C.A ≅ A')

@[simp] theorem ambientIsoChart_R : (C.ambientIsoChart e).R = C.R := rfl
@[simp] theorem ambientIsoChart_A : (C.ambientIsoChart e).A = A' := rfl
@[simp] theorem ambientIsoChart_B : (C.ambientIsoChart e).B = C.B := rfl
@[simp] theorem ambientIsoChart_alpha : (C.ambientIsoChart e).α = C.α ≫ e.hom := rfl
@[simp] theorem ambientIsoChart_sigma : (C.ambientIsoChart e).σ = e.inv ≫ C.σ := rfl
@[simp] theorem ambientIsoChart_jY : (C.ambientIsoChart e).jY = C.jY := rfl
@[simp] theorem ambientIsoChart_jP :
    (C.ambientIsoChart e).jP = Spec.map e.hom ≫ C.jP := rfl
@[simp] theorem ambientIsoChart_jX : (C.ambientIsoChart e).jX = C.jX := rfl
@[simp] theorem ambientIsoChart_point : (C.ambientIsoChart e).point = C.point := rfl
@[simp] theorem ambientIsoChart_regularList :
    (C.ambientIsoChart e).regularList = C.regularList.map e.hom.hom := rfl

theorem ambientIsoChart_sourceMap :
    (C.ambientIsoChart e).α ≫ (C.ambientIsoChart e).σ = C.α ≫ C.σ := by
  change (C.α ≫ e.hom) ≫ (e.inv ≫ C.σ) = C.α ≫ C.σ
  simp only [Category.assoc, e.hom_inv_id_assoc]

theorem ambientIsoChart_regularList_length :
    (C.ambientIsoChart e).regularList.length = C.regularList.length := by
  simp only [ambientIsoChart_regularList, List.length_map]

end AmbientFields

section BaseFields
variable {R' : CommRingCat.{u}} (e : C.R ≅ R')

@[simp] theorem baseIsoChart_R : (C.baseIsoChart e).R = R' := rfl
@[simp] theorem baseIsoChart_A : (C.baseIsoChart e).A = C.A := rfl
@[simp] theorem baseIsoChart_B : (C.baseIsoChart e).B = C.B := rfl
@[simp] theorem baseIsoChart_alpha : (C.baseIsoChart e).α = e.inv ≫ C.α := rfl
@[simp] theorem baseIsoChart_sigma : (C.baseIsoChart e).σ = C.σ := rfl
@[simp] theorem baseIsoChart_jY :
    (C.baseIsoChart e).jY = Spec.map e.hom ≫ C.jY := rfl
@[simp] theorem baseIsoChart_jP : (C.baseIsoChart e).jP = C.jP := rfl
@[simp] theorem baseIsoChart_jX : (C.baseIsoChart e).jX = C.jX := rfl
@[simp] theorem baseIsoChart_point : (C.baseIsoChart e).point = C.point := rfl
@[simp] theorem baseIsoChart_regularList : (C.baseIsoChart e).regularList = C.regularList := rfl

theorem baseIsoChart_sourceMap :
    (C.baseIsoChart e).α ≫ (C.baseIsoChart e).σ = e.inv ≫ (C.α ≫ C.σ) := by
  change (e.inv ≫ C.α) ≫ C.σ = e.inv ≫ (C.α ≫ C.σ)
  exact Category.assoc _ _ _

end BaseFields
end SmoothClosedImmersionLocalChart
end AlgebraicGeometry.Scheme.Modules.Differentials
