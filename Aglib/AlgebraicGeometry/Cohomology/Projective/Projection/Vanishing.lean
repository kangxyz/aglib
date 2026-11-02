/-
Copyright (c) 2026 algebraic-geometry contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.ProjectiveSpace.BaseChange.Affine
public import Aglib.AlgebraicGeometry.Cohomology.Projective.Vanishing
public import Aglib.AlgebraicGeometry.Cohomology.DirectImage.QuasiCoherent
public import Aglib.AlgebraicGeometry.Cohomology.DirectImage.Affine.Cohomology
public import Aglib.AlgebraicGeometry.Modules.Support

/-!
# The sharp higher-image bound for projective-space projections

For quasicoherent coefficients, every actual higher direct image above the
projective dimension is zero over an arbitrary base scheme. On an affine
base chart, the original Cartesian comparison supplies the original finite
coordinate affine cover. Native finite-cover vanishing and the original
affine higher-image comparison then detect zero on each base chart.
No Noetherianity, finite-type coefficient or relative flatness is assumed.
-/

@[expose] public section

noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency.types false

open CategoryTheory CategoryTheory.Limits
open AlgebraicGeometry.ProjectiveSpace

universe u

namespace AlgebraicGeometry.Scheme.Cohomology

variable (R : Type u) [CommRing R] (ι : Type u)

/-- The original cohomology of an affine-base projective Cartesian square
vanishes above its coordinate dimension, for every quasicoherent coefficient. -/
theorem projectiveAffinePullbackCohomology_subsingleton_of_gt
    {A : Type u} [CommRing A] {X : Scheme.{u}}
    (a : X ⟶ ProjectiveSpace R ι) (b : X ⟶ Spec (.of A))
    (g : Spec (.of A) ⟶ Spec (.of R)) (h : IsPullback a b (toSpec R ι) g)
    (n : ℕ) (e : ι ≃ Fin (n + 1)) (M : X.Modules) [M.IsQuasicoherent]
    (q : ℕ) (hq : n < q) :
    Subsingleton (Sheaf.H.{u + 1} (moduleAddSheaf X M) q) := by
  let E := affinePullbackIso ι a b g h
  let : X.IsSeparated := by
    constructor
    rw [← terminal.comp_from E.hom]
    infer_instance
  let U : Fin (n + 1) → X.Opens :=
    fun k => E.hom ⁻¹ᵁ coordinateOpen A ι (e.symm k)
  have hcover : iSup U = ⊤ := by
    apply E.hom.iSup_preimage_eq_top
    rw [e.symm.iSup_comp]
    exact iSup_coordinateOpen_eq_top A ι
  exact subsingleton_sheafH_of_finite_affine_cover M n U
    (fun k => (isAffineOpen_coordinateOpen A ι (e.symm k)).preimage E.hom) hcover q hq

/-- Every original higher direct image above the projective dimension vanishes.
The base scheme is arbitrary and the coefficient is only quasicoherent. -/
theorem projectiveProjection_higherDirectImage_isZero
    {X Y : Scheme.{u}}
    (a : X ⟶ ProjectiveSpace R ι) (p : X ⟶ Y) (f : Y ⟶ Spec (.of R))
    (h : IsPullback a p (toSpec R ι) f)
    (n : ℕ) (e : ι ≃ Fin (n + 1)) (M : X.Modules) [M.IsQuasicoherent]
    (q : ℕ) (hq : n < q) :
    IsZero (((Scheme.Modules.pushforward p).rightDerived q).obj M) := by
  let := Fintype.ofEquiv (Fin (n + 1)) e.symm
  let : IsProper p := MorphismProperty.of_isPullback h inferInstance
  let F := ((Scheme.Modules.pushforward p).rightDerived q).obj M
  apply (Scheme.Modules.isZero_iff_stalks F).mpr
  intro x
  obtain ⟨A, j, hj, y, hy⟩ := Scheme.exists_Spec_apply_eq x
  let := hj
  let u := pullback.fst p j
  let v := pullback.snd p j
  let H := IsPullback.of_hasPullback p j
  let N := M.restrict u
  let G := ((Scheme.Modules.pushforward v).rightDerived q).obj N
  let : Subsingleton (Sheaf.H.{u + 1} (moduleAddSheaf (pullback p j) N) q) :=
    projectiveAffinePullbackCohomology_subsingleton_of_gt R ι
      (u ≫ a) v (j ≫ f) (H.paste_horiz h) n e N q hq
  let : Subsingleton (moduleSpecΓFunctor.obj G) :=
    (moduleHigherDirectImageAffineSectionsLinearEquiv v N
      (injectiveResolution N) q).injective.subsingleton
  let : G.IsQuasicoherent := moduleHigherDirectImage_isQuasicoherent v N q
  have hG : IsZero G :=
    ((tilde.functor A).map_isZero (ModuleCat.isZero_of_subsingleton
      (moduleSpecΓFunctor.obj G))).of_iso (asIso G.fromTildeΓ).symm
  have hrestrict : IsZero (F.restrict j) :=
    hG.of_iso ((Scheme.Modules.higherDirectImageOpenRestrictionIso u v p j H q).app M)
  have hs := (Scheme.Modules.stalkFunctor (Spec A) y).map_isZero hrestrict
  have hs' := hs.of_iso ((Scheme.Modules.restrictStalkNatIso j y).app F).symm
  have hs'' : IsZero ((Scheme.Modules.stalkFunctor Y (j y)).obj F) := by
    change IsZero ((TopCat.Presheaf.stalkFunctor AddCommGrpCat.{u}
      (X := (Y : TopCat.{u})) (j y)).obj F.presheaf)
    change IsZero ((TopCat.Presheaf.stalkFunctor AddCommGrpCat.{u}
      (X := (Y : TopCat.{u})) (j y)).obj F.presheaf) at hs'
    exact hs'
  simpa only [hy] using hs''

end AlgebraicGeometry.Scheme.Cohomology
