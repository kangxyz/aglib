/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/

module

public import Aglib.AlgebraicGeometry.Cohomology.Proper.StructureSheaf.Pushforward

/-! Focused consumer of universal O-connectedness (Picard plan target 2). The endpoints are
the original structure map `(pullback.snd f g).c` and its components `app V`, for arbitrary
test schemes; the local-base statements use the actual fibre product over `Spec.map σ` and
the instance-supplied geometrically integral closed fibre. -/

@[expose] public section

noncomputable section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

universe u

/- Ring-sheaf form on the original structure map, for every test scheme. -/
example {X S T : Scheme.{u}} (f : X ⟶ S) [IsLocallyNoetherian S] [IsProper f] [Flat f]
    [GeometricallyIntegral f] (g : T ⟶ S) : IsIso (pullback.snd f g).c :=
  isIso_c_pullback_snd_of_isProper_of_flat_of_geometricallyIntegral f g

/- Global functions of an arbitrary (possibly non-Noetherian, nonaffine) test scheme. -/
example {X S T : Scheme.{u}} (f : X ⟶ S) [IsLocallyNoetherian S] [IsProper f] [Flat f]
    [GeometricallyIntegral f] (g : T ⟶ S) :
    Function.Bijective (pullback.snd f g).appTop :=
  bijective_app_pullback_snd_of_isProper_of_flat_of_geometricallyIntegral f g ⊤

/- Every affine open of every test scheme. -/
example {X S T : Scheme.{u}} (f : X ⟶ S) [IsLocallyNoetherian S] [IsProper f] [Flat f]
    [GeometricallyIntegral f] (g : T ⟶ S) {V : T.Opens} (hV : IsAffineOpen V) :
    Function.Bijective ((pullback.snd f g).app V) :=
  bijective_app_pullback_snd_of_isAffineOpen_of_isProper_of_flat_of_geometricallyIntegral
    f g hV

/- The component of the sheaf isomorphism is an isomorphism of rings. -/
example {X S T : Scheme.{u}} (f : X ⟶ S) [IsLocallyNoetherian S] [IsProper f] [Flat f]
    [GeometricallyIntegral f] (g : T ⟶ S) (V : T.Opens) :
    IsIso ((pullback.snd f g).app V) := by
  have := isIso_c_pullback_snd_of_isProper_of_flat_of_geometricallyIntegral f g
  infer_instance

/- Local Noetherian base: the structure map `R → Γ(X, ⊤)` is bijective. -/
example {R : Type u} [CommRing R] [IsLocalRing R] [IsNoetherianRing R] {X : Scheme.{u}}
    (f : X ⟶ Spec (CommRingCat.of R)) [IsProper f] [Flat f] [GeometricallyIntegral f] :
    Function.Bijective (f.appTop.hom.comp (Scheme.ΓSpecIso (CommRingCat.of R)).inv.hom) :=
  Scheme.Cohomology.bijective_structureMap_of_proper_geometricallyIntegral_closedFibre

/- Local Noetherian base: after every ring map, on the actual fibre product. -/
example {R B : Type u} [CommRing R] [IsLocalRing R] [IsNoetherianRing R] [CommRing B]
    {X : Scheme.{u}} (f : X ⟶ Spec (CommRingCat.of R)) [IsProper f] [Flat f]
    [GeometricallyIntegral f] (σ : R →+* B) :
    Function.Bijective (pullback.snd f (Spec.map (CommRingCat.ofHom σ))).appTop :=
  Scheme.Cohomology.bijective_appTop_of_isPullback_of_proper_geometricallyIntegral_closedFibre σ
    (IsPullback.of_hasPullback f (Spec.map (CommRingCat.ofHom σ)))

/- The residue comparison of the structure module is the original degree-zero map. -/
example {R : Type u} [CommRing R] [IsLocalRing R] {X : Scheme.{u}}
    (f : X ⟶ Spec (CommRingCat.of R)) [IsProper f]
    [GeometricallyIntegral (Scheme.Cohomology.closedFibreMap f)] :
    Epi (Scheme.Cohomology.moduleCohomologyBaseChangeMap f
      (algebraMap R (IsLocalRing.ResidueField R)) (SheafOfModules.unit X.ringCatSheaf) 0) :=
  Scheme.Cohomology.epi_moduleCohomologyBaseChangeMap_residue_unit f

/- The structure module is a coherent relatively flat coefficient for a flat morphism. -/
example {X Y : Scheme.{u}} (f : X ⟶ Y) [Flat f] :
    Scheme.Modules.QuasiCoherent.affineLocallyFiniteType X
        (SheafOfModules.unit X.ringCatSheaf) ∧
      Scheme.Modules.relativeFlat f (SheafOfModules.unit X.ringCatSheaf) :=
  ⟨Scheme.Modules.affineLocallyFiniteType_unit X, Scheme.Modules.relativeFlat_unit_of_flat f⟩
