/-
Copyright (c) 2026 kangxyz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.SchemeOverField
public import Aglib.AlgebraicGeometry.Morphisms.Smooth.Properties
public import Aglib.AlgebraicGeometry.Properties.Normal.Basic
public import Mathlib.AlgebraicGeometry.Morphisms.Finite
public import Mathlib.AlgebraicGeometry.Morphisms.Etale
public import Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion

/-!
# The actual point component of a smooth field-scheme

Source: `R5Lab.Aglib.AlgebraicGeometry.IrreducibleComponents.PointComponent`.
R5 packet revision: `f8a3314ddecffcada2ec721d26d56a937bed9690`.
Source SHA-256: `bd3a430f4f51c8c234dc0e47d2f4f30aed822ee78d07495b905e6b9556255fba`.
Actual objects, maps, universes and hypotheses are retained.
Native declaration ownership replaces the source application namespaces.
-/

@[expose] public section

noncomputable section
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory Limits AlgebraicGeometry
universe u

open _root_.AlgebraicGeometry.Scheme.OverField (FScheme)
open _root_.AlgebraicGeometry.Scheme (SmoothFieldNormality NormalComponentsOpen)
namespace AlgebraicGeometry.Scheme.OverField

variable (hnormal : SmoothFieldNormality.{u}) (hcomp : NormalComponentsOpen.{u})
variable {F : Type u} [Field F] (X : FScheme F) [Smooth X.hom]

/-- The ACTUAL irreducible component containing a point, as an open subscheme.
Openness follows from the existing general normality/component foundations. -/
def pointComponentOpen (x : X.left) : X.left.Opens :=
  ⟨irreducibleComponent x, hcomp X.left (LocallyOfFiniteType.isLocallyNoetherian X.hom)
    (hnormal F X.left X.hom inferInstance) _ (irreducibleComponent_mem_irreducibleComponents x)⟩

abbrev pointComponent (x : X.left) : FScheme F :=
  Over.mk ((pointComponentOpen hnormal hcomp X x).ι ≫ X.hom)

def pointComponentMap (x : X.left) : pointComponent hnormal hcomp X x ⟶ X :=
  Over.homMk (pointComponentOpen hnormal hcomp X x).ι rfl

instance pointComponentMap_finite (x : X.left) :
    IsFinite (pointComponentMap hnormal hcomp X x).left := by
  let U := pointComponentOpen hnormal hcomp X x
  have : IsClosedImmersion U.ι := .of_isPreimmersion U.ι (by
    rw [Scheme.Opens.range_ι]
    exact isClosed_irreducibleComponent)
  exact inferInstanceAs (IsFinite U.ι)

instance pointComponentMap_etale (x : X.left) :
    Etale (pointComponentMap hnormal hcomp X x).left :=
  inferInstanceAs (Etale (pointComponentOpen hnormal hcomp X x).ι)

instance pointComponent_connected (x : X.left) :
    ConnectedSpace (pointComponent hnormal hcomp X x).left := by
  let : IrreducibleSpace (irreducibleComponent x) :=
    Subtype.irreducibleSpace (isIrreducible_irreducibleComponent (x := x))
  exact inferInstanceAs (ConnectedSpace (irreducibleComponent x))

/-- The original field-valued point factors through its ACTUAL component,
without a supplied component or point-lift certificate. -/
theorem pointComponent_point_lift (o : Spec (.of F) ⟶ X.left) :
    ∃ s : Spec (.of F) ⟶ (pointComponent hnormal hcomp X (o default)).left,
      s ≫ (pointComponentMap hnormal hcomp X (o default)).left = o := by
  let U := pointComponentOpen hnormal hcomp X (o default)
  have hr : Set.range o ⊆ Set.range U.ι := by
    rw [Scheme.Opens.range_ι]
    rintro _ ⟨p, rfl⟩
    have hp : p = default := Subsingleton.elim _ _
    change o p ∈ irreducibleComponent (o default)
    rw [hp]
    exact mem_irreducibleComponent
  exact ⟨IsOpenImmersion.lift U.ι o hr, IsOpenImmersion.lift_fac _ _ hr⟩

end AlgebraicGeometry.Scheme.OverField
