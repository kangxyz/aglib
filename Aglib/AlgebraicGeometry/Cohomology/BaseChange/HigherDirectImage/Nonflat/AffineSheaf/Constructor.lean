/-
Copyright (c) 2026 algebraic-geometry contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.Cohomology.BaseChange.HigherDirectImage.Nonflat.AffineSheaf
public import Aglib.AlgebraicGeometry.Modules.QuasiCoherent.Affine.TildePullbackRaw

/-! # Constructor -/

@[expose] public section
noncomputable section
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

universe u

open CategoryTheory AlgebraicGeometry

namespace AlgebraicGeometry.Scheme.Modules.Nonflat

variable {R S : CommRingCat.{u}}

/-- The native presented-sheaf map is the original generic transported-map constructor. -/
theorem affineMapOfTilde_eq (σ : R ⟶ S)
    {P : ModuleCat R} {Q : ModuleCat S} {E : (Spec R).Modules} {F : (Spec S).Modules}
    (e : (tilde.functor R).obj P ≅ E) (d : (tilde.functor S).obj Q ⟶ F)
    (t : (ModuleCat.extendScalars σ.hom).obj P ⟶ Q) :
    affineMapOfTilde σ e d t =
      affineFunctorMap (tilde.functor R) (tilde.functor S)
        (ModuleCat.extendScalars σ.hom) (pullback (Spec.map σ))
        (tildePullbackIso σ).hom e d t := by
  rfl

/-- The original raw scalar map gives the same native presented-sheaf constructor. -/
theorem affineMapOfTilde_ringHom_eq (f : R →+* S)
    {P : ModuleCat R} {Q : ModuleCat S} {E : (Spec R).Modules} {F : (Spec S).Modules}
    (e : (tilde.functor R).obj P ≅ E) (d : (tilde.functor S).obj Q ⟶ F)
    (t : (ModuleCat.extendScalars f).obj P ⟶ Q) :
    affineMapOfTilde (R := R) (S := S) (CommRingCat.ofHom f) e d t =
      affineFunctorMap (tilde.functor R) (tilde.functor S)
        (ModuleCat.extendScalars f) (pullback (Spec.map (CommRingCat.ofHom f : R ⟶ S)))
        (tildePullbackIso (CommRingCat.ofHom f : R ⟶ S)).hom e d t := by
  simpa only [CommRingCat.hom_ofHom] using
    (affineMapOfTilde_eq (R := R) (S := S) (CommRingCat.ofHom f) e d t)

/-- The original native constructor uses the same raw tilde hom data. -/
theorem affineMapOfTilde_ringHom_eq_raw (f : R →+* S)
    {P : ModuleCat R} {Q : ModuleCat S} {E : (Spec R).Modules} {F : (Spec S).Modules}
    (e : (tilde.functor R).obj P ≅ E) (d : (tilde.functor S).obj Q ⟶ F)
    (t : (ModuleCat.extendScalars f).obj P ⟶ Q) :
    affineMapOfTilde (R := R) (S := S) (CommRingCat.ofHom f) e d t =
      affineFunctorMap (tilde.functor R) (tilde.functor S)
        (ModuleCat.extendScalars f) (pullback (Spec.map (CommRingCat.ofHom f : R ⟶ S)))
        (tildePullbackHomRingHom (R := R) (S := S) f) e d t := by
  simpa only [tildePullbackHomRingHom_eq] using
    (affineMapOfTilde_ringHom_eq (R := R) (S := S) f e d t)

end AlgebraicGeometry.Scheme.Modules.Nonflat
