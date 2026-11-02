/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.Spec.PrincipalFractionProjection
public import Aglib.AlgebraicGeometry.Morphisms.FiniteEtale.Descent.LimitObjects
public import Aglib.AlgebraicGeometry.Morphisms.FiniteEtale.Descent.LimitAutomorphisms
public import Aglib.AlgebraicGeometry.Morphisms.FiniteEtale.GaloisBaseChange
public import Aglib.AlgebraicGeometry.Geometrically.Integral.Smooth
public import Aglib.CategoryTheory.Galois.FiberCompatibleReflection
public import Aglib.CategoryTheory.Galois.Iso

/-! # The original generic Galois cover descends to a principal stage

The supplied fraction field remains the limit vertex. Cover objects and their
original automorphisms descend through the same principal-neighborhood
system. Density, rather than surjectivity, gives integral stage sources.
-/

@[expose] public noncomputable section

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open CategoryTheory CategoryTheory.Limits CategoryTheory.PreGaloisCategory Opposite
open IsLocalization.PrincipalDiagram
open scoped nonZeroDivisors
open AlgebraicGeometry.Scheme.PrincipalNeighborhoodLimit

namespace AlgebraicGeometry.Scheme.FiniteEtale.LimitDescent

universe u

variable (R K : Type u) [CommRing R] [IsDomain R] [IsNoetherianRing R]
  [Field K] [Algebra R K] [IsFractionRing R K]
  {X : Scheme.{u}} [CompactSpace X] [QuasiSeparatedSpace X]
  (p : X ⟶ Spec (.of R)) [Smooth p] [GeometricallyConnected p]

local instance fractionGalois_limitConnected :
    ConnectedSpace (pullback p (Spec.algebraMap R K) : Scheme.{u}) :=
  GeometricallyConnected.connectedSpace_of_subsingleton (pullback.snd p (Spec.algebraMap R K))

local instance fractionGalois_stageConnected (s : Finset R⁰) :
    ConnectedSpace ((PrincipalNeighborhoodLimit.baseChangeDiagram R⁰ p).obj (op s)) := by
  change ConnectedSpace (pullback (Spec.algebraMap R (stage R⁰ s)) p : Scheme.{u})
  exact GeometricallyConnected.connectedSpace (pullback.fst (Spec.algebraMap R (stage R⁰ s)) p)
    (pullback.fst (Spec.algebraMap R (stage R⁰ s)) p).isOpenMap

/-- An original generic Galois cover has a native principal-stage model with
integral source, unchanged deck order, and its original reconstruction iso. -/
theorem exists_principal_galois_cover
    (Y : FiniteEtale (pullback p (Spec.algebraMap R K))) [IsGalois Y] :
    ∃ (s : Finset R⁰)
      (C : FiniteEtale ((PrincipalNeighborhoodLimit.baseChangeDiagram R⁰ p).obj (op s))),
      IsIntegral C.obj.left ∧ IsGalois C ∧ Nat.card (Aut C) = Nat.card (Aut Y) ∧
        Nonempty ((baseChange
          (PrincipalNeighborhoodLimit.baseChangeProjection R⁰ K p (op s))).obj C ≅ Y) := by
  classical
  let D := PrincipalNeighborhoodLimit.baseChangeDiagram R⁰ p
  let c := PrincipalNeighborhoodLimit.baseChangeCone R⁰ K p
  let hc := PrincipalNeighborhoodLimit.baseChangeConeIsLimit R⁰ K p
  let : ConnectedSpace c.pt :=
    inferInstanceAs (ConnectedSpace (pullback p (Spec.algebraMap R K) : Scheme.{u}))
  obtain ⟨i, Yi, ⟨e⟩⟩ := exists_cover_of_isLimit D c hc Y
  obtain ⟨j, k, hsurj⟩ := exists_iteratedCover_mapAut_surjective D c i Yi hc Y e
  let : ConnectedSpace (D.obj k.left) := fractionGalois_stageConnected R p k.left.unop
  let C := iteratedCover D i Yi j k
  let b : c.pt ⟶ D.obj k.left := c.π.app k.left
  let E : (baseChange b).obj C ≅ Y := iteratedCoverIso D c i Yi j k ≪≫ e
  let : GeometricallyIntegral p := geometricallyIntegral_of_smooth_of_geometricallyConnected p
  let : IsIntegral X := GeometricallyIntegral.isIntegral_of_isLocallyNoetherian p
  let : IsLocallyNoetherian X := LocallyOfFiniteType.isLocallyNoetherian p
  let : ConnectedSpace Y.obj.left := Connectedness.connectedSpace_of_categoricalConnected Y
  let : IsIntegral Y.obj.left :=
    isIntegral_of_connected_of_smooth (Y.obj.hom ≫ pullback.snd p (Spec.algebraMap R K))
  let eX : ((baseChange b).obj C).obj.left ≅ Y.obj.left := (forgetToScheme c.pt).mapIso E
  let : IsIntegral ((baseChange b).obj C).obj.left := IsIntegral.of_isIso eX.inv
  let : IsIntegral C.obj.left := fractionCover_isIntegral_of_generic R K p k.left.unop C
  let x := algebraicClosureResiduePoint c.pt
    (Classical.choice (inferInstance : Nonempty c.pt))
  let : IsGalois ((baseChange b).obj C) := isGalois_of_iso (fiberToFinite x) E.symm
  have hraw : Function.Surjective (Functor.mapAut C (baseChange b)) := by
    intro σ
    obtain ⟨ρ, hρ⟩ := hsurj (Aut.autMulEquivOfIso E σ)
    exact ⟨ρ, (Aut.autMulEquivOfIso E).injective hρ⟩
  let : IsConnected C := Connectedness.categoricalConnected_of_connectedSpace C
  let : IsGalois C := isGalois_of_fiberCompatible_of_mapAut_surjective
    (fiberToFinite (x ≫ b)) (fiberToFinite x) (baseChange b)
    (fiberToFiniteBaseChangeIso b x) C hraw
  refine ⟨k.left.unop, C, inferInstance, inferInstance, ?_, ⟨E⟩⟩
  exact (baseChange_card_aut_of_connected b C).symm.trans
    (Nat.card_congr (Aut.autMulEquivOfIso E).toEquiv)

end AlgebraicGeometry.Scheme.FiniteEtale.LimitDescent
