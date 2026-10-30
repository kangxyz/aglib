/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.Group.IdentityComponent.Basic
public import Aglib.AlgebraicGeometry.Morphisms.Smooth.RelativeDimension
public import Aglib.AlgebraicGeometry.RationalPoint.CotangentComparison
public import Mathlib.AlgebraicGeometry.AlgClosed.Basic

/-!
# Smooth group dimension and the identity cotangent space

For a connected smooth group over an arbitrary field, the dimension is the
dimension of its actual identity cotangent space. Over an algebraically closed
field, actual translations give the same result without connectedness. The
open inclusion of the identity component induces the original stalk and
cotangent isomorphisms.
-/

@[expose] public noncomputable section

open CategoryTheory AlgebraicGeometry MonoidalCategory MonObj CartesianMonoidalCategory
open scoped CategoryTheory.MonObj
open AlgebraicGeometry.Scheme.OverField

universe u

namespace AlgebraicGeometry.Scheme.Group

attribute [local instance] Over.cartesianMonoidalCategory

variable {k : Type u} [Field k]

/-- Pullback by the actual right translation identifies the cotangent space
at a rational point with the cotangent space at the group identity. -/
def translationCotangentEquiv (G : FScheme k) [GrpObj G]
    (a : 𝟙_ (FScheme k) ⟶ G) : Cotangent.Space a ≃ₗ[k] Cotangent.Space η[G] := by
  let e := GrpObj.mulRight a
  let : IsIso e.hom.left := (Over.forget (Base k)).map_isIso e.hom
  exact Cotangent.equivOfIsOpenImmersion η[G] a e.hom
    (by
      simp [e, GrpObj.mulRight, comp_lift_assoc]
      simpa only [Category.id_comp] using
        (MonObj.lift_comp_one_left (𝟙 (𝟙_ (FScheme k))) a))

/-- The actual cotangent pullback along the identity-component inclusion is a
linear equivalence at the native group identities. -/
def identityComponentCotangentEquiv (G : FScheme k) [GrpObj G]
    [LocallyOfFiniteType G.hom] :
    Cotangent.Space η[G] ≃ₗ[k] Cotangent.Space η[identityComponentOver G] :=
  Cotangent.equivOfIsOpenImmersion η[identityComponentOver G] η[G]
    (identityComponentι G) (by rw [one_identityComponentOver, identityComponentOne_ι])

-- The open-subscheme structural composition has definitionally equal source coercions.
set_option backward.isDefEq.respectTransparency.types false in
/-- The actual open identity component of a smooth group is smooth. -/
theorem smooth_identityComponentOver (G : FScheme k) [GrpObj G]
    [LocallyOfFiniteType G.hom] [Smooth G.hom] :
    Smooth (identityComponentOver G).hom := by
  rw [identityComponentOver_hom]
  have hi : Smooth (identityComponent G).ι := inferInstance
  exact @AlgebraicGeometry.smooth_comp _ _ (identityComponent G).ι _ G.hom hi ‹Smooth G.hom›

/-- A connected smooth group has relative dimension equal to the dimension
of its original identity cotangent space, over the original field. -/
theorem smoothOfRelativeDimension_finrank_identityCotangent_of_preconnected
    (G : FScheme k) [GrpObj G] [Smooth G.hom] [PreconnectedSpace G.left] :
    SmoothOfRelativeDimension (Module.finrank k (Cotangent.Space η[G])) G.hom := by
  obtain ⟨n, hn⟩ := exists_smoothOfRelativeDimension_of_preconnected G.hom (unitPoint G)
  let := hn
  rw [Cotangent.finrank η[G] n]
  exact hn

/-- The global topological dimension of a connected smooth group is the
dimension of its original identity cotangent space. -/
theorem topologicalKrullDim_eq_finrank_identityCotangent_of_preconnected
    (G : FScheme k) [GrpObj G] [Smooth G.hom] [PreconnectedSpace G.left] :
    topologicalKrullDim G.left = Module.finrank k (Cotangent.Space η[G]) :=
  smoothFieldDimension k G.left G.hom _
    (smoothOfRelativeDimension_finrank_identityCotangent_of_preconnected G) ⟨unitPoint G⟩

-- Locality for the morphism property uses the definitionally equal field-scheme presentation.
set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
/-- Over an algebraically closed field, translations identify the cotangent
dimensions at all closed points, so every smooth group has one relative
dimension even when it has several connected components. -/
theorem smoothOfRelativeDimension_finrank_identityCotangent_of_isAlgClosed
    [IsAlgClosed k] (G : FScheme k) [GrpObj G] [Smooth G.hom] :
    SmoothOfRelativeDimension (Module.finrank k (Cotangent.Space η[G])) G.hom := by
  choose U n hx hn using exists_smoothOfRelativeDimension_open G.hom
  apply IsZariskiLocalAtSource.of_iSup_eq_top
    (P := @SmoothOfRelativeDimension.{u} (Module.finrank k (Cotangent.Space η[G]))) U
    (by
      apply top_le_iff.mp
      intro z _
      exact TopologicalSpace.Opens.mem_iSup.mpr ⟨z, hx z⟩)
  intro z
  let T : FScheme k := Over.mk ((U z).ι ≫ G.hom)
  let : SmoothOfRelativeDimension (n z) T.hom := hn z
  let : Smooth T.hom := SmoothOfRelativeDimension.smooth (n z) T.hom
  let : JacobsonSpace T.left := LocallyOfFiniteType.jacobsonSpace T.hom
  obtain ⟨p, -, hp⟩ := nonempty_inter_closedPoints
    (show (Set.univ : Set T.left).Nonempty from ⟨⟨z, hx z⟩, trivial⟩)
    isOpen_univ.isLocallyClosed
  let a : 𝟙_ (FScheme k) ⟶ T :=
    Over.homMk (pointOfClosedPoint T.hom p hp) (pointOfClosedPoint_comp T.hom p hp)
  let i : T ⟶ G := Over.homMk (U z).ι rfl
  let : IsOpenImmersion i.left := inferInstanceAs (IsOpenImmersion (U z).ι)
  have hd : Module.finrank k (Cotangent.Space η[G]) = n z :=
    (translationCotangentEquiv G (a ≫ i)).finrank_eq.symm.trans
      ((Cotangent.equivOfIsOpenImmersion a (a ≫ i) i rfl).finrank_eq.trans
        (Cotangent.finrank a (n z)))
  simpa only [hd] using hn z

/-- The global dimension of a smooth group over an algebraically closed field
is its actual identity cotangent dimension, with no connectedness assumption. -/
theorem topologicalKrullDim_eq_finrank_identityCotangent_of_isAlgClosed
    [IsAlgClosed k] (G : FScheme k) [GrpObj G] [Smooth G.hom] :
    topologicalKrullDim G.left = Module.finrank k (Cotangent.Space η[G]) :=
  smoothFieldDimension k G.left G.hom _
    (smoothOfRelativeDimension_finrank_identityCotangent_of_isAlgClosed G) ⟨unitPoint G⟩

end AlgebraicGeometry.Scheme.Group
