/-
Copyright (c) 2026 algebraic-geometry contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.ProjectiveSpace.BaseChange.Affine
public import Aglib.AlgebraicGeometry.Cohomology.Projective.ClosedImmersion
public import Aglib.AlgebraicGeometry.Cohomology.DirectImage.QuasiCoherent
public import Aglib.AlgebraicGeometry.Cohomology.DirectImage.Affine.Cohomology
public import Aglib.AlgebraicGeometry.Modules.QuasiCoherent.FiniteType.Restriction

/-!
# Coherent higher images of actual projective-space projections

Every base change of the original polynomial projective-space projection
over a locally Noetherian scheme has coherent higher direct images of
coherent coefficients. On each actual affine chart of the base, the native
Cartesian comparison gives an actual projective embedding. The proved
embedded-projective finiteness theorem and the original affine higher-image
comparison then give the finite section module. No relative-flatness or
proper-finiteness theorem family is assumed.
-/

@[expose] public section

noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency.types false

open CategoryTheory CategoryTheory.Limits
open AlgebraicGeometry.ProjectiveSpace
open AlgebraicGeometry.Scheme.Modules.QuasiCoherent

universe u

namespace AlgebraicGeometry.Scheme.Cohomology

variable (R : Type u) [CommRing R] (ι : Type u)

/-- All actual higher direct images under an original projective-space projection
are coherent over a locally Noetherian base, without relative flatness. The
supplied square is Cartesian for the original structural morphism. -/
theorem projectiveProjection_higherDirectImage_coherent
    {X Y : Scheme.{u}} [IsLocallyNoetherian Y]
    (a : X ⟶ ProjectiveSpace R ι) (p : X ⟶ Y) (f : Y ⟶ Spec (.of R))
    (h : IsPullback a p (toSpec R ι) f)
    (n : ℕ) (e : ι ≃ Fin (n + 1)) (M : X.Modules)
    (hM : affineLocallyFiniteType X M) (q : ℕ) :
    affineLocallyFiniteType Y (((Scheme.Modules.pushforward p).rightDerived q).obj M) := by
  let := Fintype.ofEquiv (Fin (n + 1)) e.symm
  let : IsProper p := MorphismProperty.of_isPullback h inferInstance
  let : M.IsQuasicoherent :=
    quasicoherent_of_affineCharts M (fun A j _ => (hM A j).1)
  intro A j _
  let : IsLocallyNoetherian (Spec A) := isLocallyNoetherian_of_isOpenImmersion j
  let : IsNoetherianRing A := isLocallyNoetherian_Spec.mp inferInstance
  let u := pullback.fst p j
  let v := pullback.snd p j
  let H := IsPullback.of_hasPullback p j
  let E := affinePullbackIso ι (u ≫ a) v (j ≫ f) (H.paste_horiz h)
  let N := M.restrict u
  have hN : affineLocallyFiniteType (pullback p j) N :=
    affineLocallyFiniteType_restrict u hM
  let α := v.appTop.hom.comp (Scheme.ΓSpecIso A).inv.hom
  let := moduleCohomologyModuleOfHom (pullback p j) α N q
  let : Module.Finite A (Sheaf.H.{u + 1} (moduleAddSheaf (pullback p j) N) q) :=
    moduleCohomology_finite_of_projectiveEmbedding A ι E.hom n e v
      (affinePullbackIso_hom_toSpec ι (u ≫ a) v (j ≫ f) (H.paste_horiz h)) N hN q
  have hΓ : Module.Finite A
      (moduleSpecΓFunctor.obj (((Scheme.Modules.pushforward v).rightDerived q).obj N)) :=
    Module.Finite.equiv
      (moduleHigherDirectImageAffineSectionsLinearEquiv v N (injectiveResolution N) q).symm
  have hQC : (((Scheme.Modules.pushforward v).rightDerived q).obj N).IsQuasicoherent :=
    moduleHigherDirectImage_isQuasicoherent v N q
  exact (affineFiniteSheaf A).prop_of_iso
    ((Scheme.Modules.higherDirectImageOpenRestrictionIso u v p j H q).app M).symm ⟨hQC, hΓ⟩

end AlgebraicGeometry.Scheme.Cohomology
