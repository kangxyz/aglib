/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.Sites.EtaleSliceTopology
public import Aglib.AlgebraicGeometry.EtaleCohomology.Kummer.Coefficients
public import Aglib.AlgebraicGeometry.EtaleCohomology.Kummer.EtaleSliceCoefficients
public import Aglib.CategoryTheory.Sites.Continuous.Limits

/-! # Original root coefficients on an etale slice

The actual small-etale slice equivalence identifies the original root
sheaf with its restriction. The comparison is the native roots-of-unity section
coordinate, and its naturality is the original roots restriction formula.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite AlgebraicGeometry
open AlgebraicGeometry.Scheme.EtaleCohomology

namespace GroupCohomology.Kummer.Coefficients

universe u v w z

/-- Common additive section coordinates define a sheaf isomorphism when the original
restriction maps preserve equality of those coordinates. -/
def coordinateSheafIso {C : Type v} [Category.{w} C]
    {J : GrothendieckTopology C} (P Q : Sheaf J AddCommGrpCat.{z})
    (A : Cᵒᵖ → Type u) [∀ V, AddCommGroup (A V)]
    (eP : ∀ V, P.obj.obj V ≃+ A V) (eQ : ∀ V, Q.obj.obj V ≃+ A V)
    (h : ∀ {V W} (f : V ⟶ W) (a : P.obj.obj V) (b : Q.obj.obj V),
      eP V a = eQ V b → eP W (P.obj.map f a) = eQ W (Q.obj.map f b)) : P ≅ Q :=
  ObjectProperty.isoMk _ (NatIso.ofComponents
    (fun V => ((eP V).trans (eQ V).symm).toAddCommGrpIso)
    (by
      intro V W f
      ext a
      apply (eQ W).injective
      change eQ W ((eQ W).symm (eP W (P.obj.map f a))) =
        eQ W (Q.obj.map f ((eQ V).symm (eP V a)))
      rw [AddEquiv.apply_symm_apply]
      exact h f a ((eQ V).symm (eP V a)) ((eQ V).apply_symm_apply _).symm))

variable {X : Scheme.{u}} (U : X.Etale) (n : ℕ)

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
set_option backward.defeqAttrib.useBackward true in
/-- Transport the same actual root kernels along the whole original units comparison. -/
def rootsEtaleSliceKernelIso :
    (Scheme.Etale.sliceSheafEquivalence U AddCommGrpCat.{u + 1}).inverse.obj (mu U.left n) ≅
      (mu X n).over U := by
  let F := (Scheme.Etale.sliceSheafEquivalence U AddCommGrpCat.{u + 1}).inverse
  let G := (Scheme.smallEtaleTopology X).overPullback AddCommGrpCat.{u + 1} U
  letI : F.PreservesZeroMorphisms := ⟨fun _ _ => rfl⟩
  letI : G.PreservesZeroMorphisms := ⟨fun _ _ => rfl⟩
  exact KernelFork.mapIsoOfIsLimit
    (KernelFork.mapIsLimit _ (kernelIsLimit U.left n) F)
    (KernelFork.mapIsLimit _ (kernelIsLimit X n) G)
    (Arrow.isoMk' (F.map (power U.left n)) (G.map (power X n))
      (gmEtaleSliceIso U) (gmEtaleSliceIso U) (by
        ext V a
        change n • (gmEtaleSliceIso U).hom.hom.app V a =
          (gmEtaleSliceIso U).hom.hom.app V (n • a)
        simp only [map_nsmul]))

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
set_option backward.defeqAttrib.useBackward true in
private theorem rootsEtaleSliceKernelIso_hom_inclusion :
    (rootsEtaleSliceKernelIso U n).hom ≫
        ((Scheme.smallEtaleTopology X).overPullback AddCommGrpCat.{u + 1} U).map
          (inclusion X n) =
      (Scheme.Etale.sliceSheafEquivalence U AddCommGrpCat.{u + 1}).inverse.map
        (inclusion U.left n) ≫ (gmEtaleSliceIso U).hom := by
  let F := (Scheme.Etale.sliceSheafEquivalence U AddCommGrpCat.{u + 1}).inverse
  let G := (Scheme.smallEtaleTopology X).overPullback AddCommGrpCat.{u + 1} U
  let : F.PreservesZeroMorphisms := ⟨fun _ _ => rfl⟩
  let : G.PreservesZeroMorphisms := ⟨fun _ _ => rfl⟩
  have hF : F.map (inclusion U.left n) ≫ F.map (power U.left n) = 0 := by
    rw [← Functor.map_comp, inclusion_power, Functor.map_zero]
  let e : Arrow.mk (F.map (power U.left n)) ≅ Arrow.mk (G.map (power X n)) :=
    Arrow.isoMk' (F.map (power U.left n)) (G.map (power X n))
      (gmEtaleSliceIso U) (gmEtaleSliceIso U) (by
        ext V a
        change n • (gmEtaleSliceIso U).hom.hom.app V a =
          (gmEtaleSliceIso U).hom.hom.app V (n • a)
        simp only [map_nsmul])
  exact KernelFork.mapOfIsLimit_ι (KernelFork.ofι (F.map (inclusion U.left n)) hF)
    (KernelFork.mapIsLimit _ (kernelIsLimit X n) G) e.hom

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
set_option backward.defeqAttrib.useBackward true in
private theorem rootsEtaleSliceKernelIso_hom_apply (V : (Over U)ᵒᵖ)
    (a : (mu U.left n).obj.obj ((Scheme.Etale.sliceForward U).op.obj V)) :
    (rootsEtaleSliceKernelIso U n).hom.hom.app V a =
      (rootsSections X n (op V.unop.left)).symm
        (rootsSections U.left n ((Scheme.Etale.sliceForward U).op.obj V) a) := by
  have hf := ConcreteCategory.congr_hom
    (congrArg (fun q => q.hom.app V) (rootsEtaleSliceKernelIso_hom_inclusion U n)) a
  change (inclusion X n).hom.app (op V.unop.left)
      ((rootsEtaleSliceKernelIso U n).hom.hom.app V a) =
    (gmEtaleSliceIso U).hom.hom.app V
      ((inclusion U.left n).hom.app ((Scheme.Etale.sliceForward U).op.obj V) a) at hf
  have hg := gmEtaleSliceIso_hom_apply U V
    ((inclusion U.left n).hom.app ((Scheme.Etale.sliceForward U).op.obj V) a)
  have hgu := congrArg (unitsSections X (op V.unop.left)) hg
  have hg' := hgu.trans ((unitsSections X (op V.unop.left)).apply_symm_apply _)
  have hv := congrArg Additive.toMul
    ((congrArg (unitsSections X (op V.unop.left)) hf).trans hg')
  have hx := inclusion_apply X n (op V.unop.left)
    ((rootsEtaleSliceKernelIso U n).hom.hom.app V a)
  have hu := inclusion_apply U.left n ((Scheme.Etale.sliceForward U).op.obj V) a
  have hr := hx.symm.trans (hv.trans hu)
  have hc : rootsSections X n (op V.unop.left)
      ((rootsEtaleSliceKernelIso U n).hom.hom.app V a) =
      rootsSections U.left n ((Scheme.Etale.sliceForward U).op.obj V) a := by
    apply Additive.toMul.injective
    apply Subtype.ext
    exact hr
  apply (rootsSections X n (op V.unop.left)).injective
  exact hc.trans ((rootsSections X n (op V.unop.left)).apply_symm_apply _).symm

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
set_option backward.defeqAttrib.useBackward true in
/-- The original root-section restrictions preserve equality of the coordinates
on the chart and its etale slice. -/
theorem rootsSliceCoordinates_naturality {V W : (Over U)ᵒᵖ} (f : V ⟶ W)
    (a : (mu U.left n).obj.obj ((Scheme.Etale.sliceForward U).op.obj V))
    (b : (mu X n).obj.obj (op V.unop.left))
    (h : rootsSections U.left n ((Scheme.Etale.sliceForward U).op.obj V) a =
      rootsSections X n (op V.unop.left) b) :
    rootsSections U.left n ((Scheme.Etale.sliceForward U).op.obj W)
        ((mu U.left n).obj.map ((Scheme.Etale.sliceForward U).op.map f) a) =
      rootsSections X n (op W.unop.left) ((mu X n).obj.map f.unop.left.op b) := by
  have hb : (rootsEtaleSliceKernelIso U n).hom.hom.app V a = b := by
    apply (rootsSections X n (op V.unop.left)).injective
    rw [rootsEtaleSliceKernelIso_hom_apply, AddEquiv.apply_symm_apply]
    exact h
  have hn := ConcreteCategory.congr_hom
    ((rootsEtaleSliceKernelIso U n).hom.hom.naturality f) a
  calc
    _ = rootsSections X n (op W.unop.left)
        ((rootsEtaleSliceKernelIso U n).hom.hom.app W
          ((mu U.left n).obj.map ((Scheme.Etale.sliceForward U).op.map f) a)) := by
      rw [rootsEtaleSliceKernelIso_hom_apply, AddEquiv.apply_symm_apply]
    _ = rootsSections X n (op W.unop.left)
        ((mu X n).obj.map f.unop.left.op ((rootsEtaleSliceKernelIso U n).hom.hom.app V a)) :=
      congrArg (rootsSections X n (op W.unop.left)) hn
    _ = _ := congrArg (fun t => rootsSections X n (op W.unop.left)
      ((mu X n).obj.map f.unop.left.op t)) hb

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
set_option backward.defeqAttrib.useBackward true in
private theorem rootsEtaleSliceKernelIso_eq_coordinate :
    rootsEtaleSliceKernelIso U n =
      coordinateSheafIso
        ((Scheme.Etale.sliceSheafEquivalence U AddCommGrpCat.{u + 1}).inverse.obj (mu U.left n))
        ((mu X n).over U) (fun V => Additive (rootsOfUnity n Γ(V.unop.left.left, ⊤)))
        (fun V => rootsSections U.left n ((Scheme.Etale.sliceForward U).op.obj V))
        (fun V => rootsSections X n (op V.unop.left))
        (fun f a b h => rootsSliceCoordinates_naturality U n f a b h) := by
  apply Iso.ext
  ext V a
  exact rootsEtaleSliceKernelIso_hom_apply U n V a

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
set_option backward.defeqAttrib.useBackward true in
/-- The original root sheaf on a chart is the original root sheaf restricted
to the actual etale slice, not a separately chosen coefficient model. -/
def rootsEtaleSliceIso :
    (Scheme.Etale.sliceSheafEquivalence U AddCommGrpCat.{u + 1}).inverse.obj (mu U.left n) ≅
      (mu X n).over U :=
  rootsEtaleSliceKernelIso U n

/-- The canonical actual-kernel transport is the original root-coordinate comparison. -/
theorem rootsEtaleSliceIso_eq_coordinateSheafIso :
    rootsEtaleSliceIso U n = coordinateSheafIso
    ((Scheme.Etale.sliceSheafEquivalence U AddCommGrpCat.{u + 1}).inverse.obj (mu U.left n))
    ((mu X n).over U)
    (fun V => Additive (rootsOfUnity n Γ(V.unop.left.left, ⊤)))
    (fun V => rootsSections U.left n ((Scheme.Etale.sliceForward U).op.obj V))
    (fun V => rootsSections X n (op V.unop.left))
    (fun f a b h => rootsSliceCoordinates_naturality U n f a b h) :=
  rootsEtaleSliceKernelIso_eq_coordinate U n

/-- The forward slice comparison retains its original literal root-coordinate value. -/
theorem rootsEtaleSliceIso_hom_apply (V : (Over U)ᵒᵖ)
    (a : (mu U.left n).obj.obj ((Scheme.Etale.sliceForward U).op.obj V)) :
    (rootsEtaleSliceIso U n).hom.hom.app V a =
      (rootsSections X n (op V.unop.left)).symm
        (rootsSections U.left n ((Scheme.Etale.sliceForward U).op.obj V) a) :=
  rootsEtaleSliceKernelIso_hom_apply U n V a

end GroupCohomology.Kummer.Coefficients
