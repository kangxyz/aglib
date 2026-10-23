/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.Sites.EtaleSliceTopology
public import Aglib.AlgebraicGeometry.EtaleCohomology.Kummer.Coefficients

/-! # Original root coefficients on an etale slice

The actual small-etale slice equivalence identifies the original root
sheaf with its restriction. The comparison is the native roots-of-unity section
coordinate, and its naturality is the original roots restriction formula.
-/

@[expose] public noncomputable section

open CategoryTheory Opposite AlgebraicGeometry AlgebraicGeometry.Scheme.EtaleCohomology

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
  apply Additive.toMul.injective
  apply Subtype.ext
  change (rootsSections U.left n ((Scheme.Etale.sliceForward U).op.obj W)
      ((mu U.left n).obj.map ((Scheme.Etale.sliceForward U).op.map f) a)).toMul.val =
    (rootsSections X n (op W.unop.left) ((mu X n).obj.map f.unop.left.op b)).toMul.val
  have hv := congrArg
    (fun t : Additive (rootsOfUnity n Γ(V.unop.left.left, ⊤)) => t.toMul.val) h
  rw [rootsSections_naturality, rootsSections_naturality]
  exact congrArg (Units.map f.unop.left.left.appTop.hom.toMonoidHom) hv

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
set_option backward.defeqAttrib.useBackward true in
/-- The original root sheaf on a chart is the original root sheaf restricted
to the actual etale slice, not a separately chosen coefficient model. -/
def rootsEtaleSliceIso :
    (Scheme.Etale.sliceSheafEquivalence U AddCommGrpCat.{u + 1}).inverse.obj (mu U.left n) ≅
      (mu X n).over U :=
  coordinateSheafIso
    ((Scheme.Etale.sliceSheafEquivalence U AddCommGrpCat.{u + 1}).inverse.obj (mu U.left n))
    ((mu X n).over U)
    (fun V => Additive (rootsOfUnity n Γ(V.unop.left.left, ⊤)))
    (fun V => rootsSections U.left n ((Scheme.Etale.sliceForward U).op.obj V))
    (fun V => rootsSections X n (op V.unop.left))
    (fun f a b h => rootsSliceCoordinates_naturality U n f a b h)

end GroupCohomology.Kummer.Coefficients
