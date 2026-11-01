/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.CategoryTheory.Galois.FiberCompatible
public import Aglib.AlgebraicGeometry.Morphisms.FiniteEtale.GaloisInstances
public import Aglib.AlgebraicGeometry.Morphisms.FiniteEtale.BaseChange
public import Aglib.AlgebraicGeometry.Geometrically.Connected.FieldExtension

/-! # Original Galois covers under connected base change

The actual finite-etale base-change functor and its fibre comparison preserve
Galois objects whose pullback is connected, and preserve their deck group via
the original map on automorphisms. Field extensions of an algebraically closed
source field supply the connectedness for the literal base-change cover.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits CategoryTheory.PreGaloisCategory

namespace AlgebraicGeometry.Scheme.FiniteEtale

universe u

section Connected

variable {X S : Scheme.{u}} [ConnectedSpace X] [ConnectedSpace S]
  (g : S ⟶ X) (Y : FiniteEtale X) [IsGalois Y]
  [ConnectedSpace ((baseChange g).obj Y).obj.left]

/-- A connected actual pullback of a Galois cover is Galois, by its original fibre action. -/
theorem baseChange_isGalois_of_connected : IsGalois ((baseChange g).obj Y) := by
  let s := algebraicClosureResiduePoint S (Classical.choice (inferInstance : Nonempty S))
  let : IsConnected ((baseChange g).obj Y) :=
    Connectedness.categoricalConnected_of_connectedSpace _
  exact isGalois_obj_of_fiberCompatible (fiberToFinite (s ≫ g)) (fiberToFinite s)
    (baseChange g) (fiberToFiniteBaseChangeIso g s) Y

/-- The actual finite-etale pullback map is bijective on the original deck groups. -/
theorem baseChange_mapAut_bijective_of_connected :
    Function.Bijective (Functor.mapAut Y (baseChange g)) := by
  let s := algebraicClosureResiduePoint S (Classical.choice (inferInstance : Nonempty S))
  let : IsConnected ((baseChange g).obj Y) :=
    Connectedness.categoricalConnected_of_connectedSpace _
  exact mapAut_bijective_of_fiberCompatible (fiberToFinite (s ≫ g)) (fiberToFinite s)
    (baseChange g) (fiberToFiniteBaseChangeIso g s) Y

/-- The original base-change map, viewed as a deck-group isomorphism. -/
def baseChange_autEquiv_of_connected : Aut Y ≃* Aut ((baseChange g).obj Y) :=
  MulEquiv.ofBijective (Functor.mapAut Y (baseChange g))
    (baseChange_mapAut_bijective_of_connected g Y)

/-- The literal connected base-change cover has the unchanged deck-group order. -/
theorem baseChange_card_aut_of_connected :
    Nat.card (Aut ((baseChange g).obj Y)) = Nat.card (Aut Y) :=
  (Nat.card_congr (baseChange_autEquiv_of_connected g Y).toEquiv).symm

end Connected

section Field

attribute [local instance] Geometrically.fieldSpec_geometricallyConnected

variable (k K : Type u) [Field k] [IsAlgClosed k] [Field K] [Algebra k K]
  {X : Scheme.{u}} [ConnectedSpace X] (p : X ⟶ Spec (CommRingCat.of k))
  (Y : FiniteEtale X) [IsGalois Y]

/-- The literal iterated finite-cover pullback under a field extension is connected.
Only the source field is required to be algebraically closed. -/
theorem fieldExtension_baseChange_connected :
    ConnectedSpace ((baseChange (pullback.fst p (Spec.algebraMap k K))).obj Y).obj.left := by
  let : GeometricallyConnected (Spec.algebraMap k K) :=
    Geometrically.fieldSpec_geometricallyConnected k K
  let : ConnectedSpace Y.obj.left := Connectedness.connectedSpace_of_categoricalConnected Y
  exact inferInstanceAs (ConnectedSpace
    (pullback Y.obj.hom (pullback.fst p (Spec.algebraMap k K)) : Scheme.{u}))

/-- An original Galois cover remains Galois under any field extension of an
algebraically closed source, on the literal native base-change object. -/
theorem fieldExtension_baseChange_isGalois :
    IsGalois ((baseChange (pullback.fst p (Spec.algebraMap k K))).obj Y) := by
  let : ConnectedSpace (pullback p (Spec.algebraMap k K) : Scheme.{u}) :=
    Geometrically.connectedSpace_fieldBaseChange k K p
  let := fieldExtension_baseChange_connected k K p Y
  exact baseChange_isGalois_of_connected _ Y

/-- The unchanged original field base-change homomorphism is a deck-group equivalence. -/
def fieldExtension_baseChange_autEquiv :
    Aut Y ≃* Aut ((baseChange (pullback.fst p (Spec.algebraMap k K))).obj Y) := by
  letI : ConnectedSpace (pullback p (Spec.algebraMap k K) : Scheme.{u}) :=
    Geometrically.connectedSpace_fieldBaseChange k K p
  letI := fieldExtension_baseChange_connected k K p Y
  exact baseChange_autEquiv_of_connected _ Y

/-- Field base change preserves the actual deck-group order. -/
theorem fieldExtension_baseChange_card_aut :
    Nat.card (Aut ((baseChange (pullback.fst p (Spec.algebraMap k K))).obj Y)) =
      Nat.card (Aut Y) :=
  (Nat.card_congr (fieldExtension_baseChange_autEquiv k K p Y).toEquiv).symm

end Field

end AlgebraicGeometry.Scheme.FiniteEtale
