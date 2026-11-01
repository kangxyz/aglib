/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.Descent.FinitePresentation.ProperSubalgebraModel
public import Mathlib.AlgebraicGeometry.AffineTransitionLimit
public import Mathlib.AlgebraicGeometry.Morphisms.Proper

/-! # Actual finite models over finitely generated coefficient subalgebras

A finite, locally finitely presented morphism to an affine scheme descends to
an actual finite model over a finitely generated coefficient subalgebra.
The existing proper model is rebased only once more, using eventual affineness
of its original source diagram. The limit base need not be Noetherian.
The result retains the original model's cartesian comparison and structural map.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite

namespace AlgebraicGeometry.Scheme.FiniteTypeSubalgebraLimit

universe u v

open Algebra.FiniteTypeSubalgebraLimit Scheme.FinitePresentationDescent

variable (D : Type v) [CommRing D] [IsNoetherianRing D]
  (R : Type u) [CommRing R] [Algebra D R]
  {X : Scheme.{u}} (f : X ⟶ Spec (.of R)) [IsFinite f]

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
/-- Finite presentation descends a finite morphism to a finite model over one
finitely generated coefficient subalgebra. The base algebra is arbitrary. -/
theorem exists_finiteModel_over_finiteTypeSubalgebra [LocallyOfFinitePresentation f] :
    ∃ s : Finset R,
      ∃ M : Model (Spec.map (CommRingCat.ofHom (stage D R s).val.toRingHom)) f,
        IsFinite M.f := by
  obtain ⟨s, M, hM⟩ := exists_properModel_over_finiteTypeSubalgebra D R f
  let : IsProper M.f := hM
  let F := ringDiagram D R
  let E : (Finset R)ᵒᵖ ⥤ Scheme.{u} := F.op ⋙ Scheme.Spec
  let c : Cone E := Scheme.Spec.mapCone (ringCocone D R).op
  have hc : IsLimit c := isLimitOfPreserves Scheme.Spec (ringCoconeIsColimit D R).op
  have (t : (Finset R)ᵒᵖ) : IsAffine (E.obj t) :=
    inferInstanceAs (IsAffine (Spec (.of (stage D R t.unop))))
  have {t t' : (Finset R)ᵒᵖ} (a : t ⟶ t') : IsAffineHom (E.map a) :=
    inferInstance
  let N : Model (c.π.app (op s)) f := M
  have : IsAffine X := isAffine_of_isAffineHom f
  have : IsAffine (baseChangeCone E c (op s) N.f).pt :=
    isAffine_of_isAffineHom N.rawIso.inv
  obtain ⟨j, hj⟩ := Scheme.exists_isAffine_of_isLimit
    (baseChangeDiagram E (op s) N.f) (baseChangeCone E c (op s) N.f)
    (isLimitBaseChangeCone E c hc (op s) N.f)
  have : IsAffine (pullback (E.map j.hom) N.f) := hj
  let P := N.rebase E c (op s) j
  have : IsAffine P.X :=
    isAffine_of_isAffineHom (pullbackSymmetry N.f (E.map j.hom)).hom
  have : IsProper P.f := by
    change IsProper (pullback.snd N.f (E.map j.hom))
    infer_instance
  have hP : IsFinite P.f := IsFinite.iff_isProper_and_isAffineHom.mpr
    ⟨inferInstance, inferInstance⟩
  exact ⟨j.left.unop, P, hP⟩

/-- Over a Noetherian target, finite type supplies the local finite-presentation
condition, so the same actual finite-model endpoint needs no extra premise. -/
theorem exists_finiteModel_over_finiteTypeSubalgebra_of_noetherian [IsNoetherianRing R] :
    ∃ s : Finset R,
      ∃ M : Model (Spec.map (CommRingCat.ofHom (stage D R s).val.toRingHom)) f,
        IsFinite M.f :=
  exists_finiteModel_over_finiteTypeSubalgebra D R f

end AlgebraicGeometry.Scheme.FiniteTypeSubalgebraLimit
