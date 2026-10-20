/-
Copyright (c) 2026 kangxyz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.Curves.Basic
public import Aglib.AlgebraicGeometry.Properties.Normal.Basic
public import Aglib.AlgebraicGeometry.Morphisms.Smooth.Properties
public import Mathlib.AlgebraicGeometry.Geometrically.Integral
public import Mathlib.AlgebraicGeometry.Noetherian
public import Mathlib.RingTheory.IntegralClosure.IntegrallyClosed
public import Mathlib.Topology.Connected.Clopen
public import Mathlib.RingTheory.RegularLocalRing.Defs
public import Mathlib.Topology.KrullDimension

/-!
# Actual smooth proper field curves

Engineering basis: 7f86e4a1763cc4ec35e9b0a8acd659750355a0de;
mathlib d13f23b723b8a846827a245b89c10fc7d3f11612.
Application owner: K2-018#prop:k2018-arithmetic-characters, mathematical
snapshot e73d98b1b5c1e5abcdebf7d058e436d792b87982, lines 341–445.

The explicitly quantified general normality premises below concern actual local rings
and irreducible components of arbitrary schemes. They are not curve integrality
or pointed-morphism hypotheses. The geometric-integrality application proves the
passage through every field-valued base change. No genus is introduced here.
-/

open _root_.AlgebraicGeometry.Scheme
  (NormalComponentsOpen SmoothClosedPointDimension SmoothFieldDimension SmoothFieldNormality
    SmoothFieldRegularity isIntegral_of_connected_normalStalks)
open _root_.AlgebraicGeometry.Scheme.OverField (Base FScheme)

/- Interface migration basis: 46f53465aaf3b0167049e9c8e9e2294111bb4281.
Original mathematical and construction source identities are retained. -/



@[expose] public section

noncomputable section
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option linter.style.haveILetI false
open CategoryTheory Limits AlgebraicGeometry
open AlgebraicGeometry.Scheme.OverField.Curve

namespace AlgebraicGeometry.Scheme.OverField.Curve
universe u

/- Normality defined on the actual local rings, including the domain condition. -/

/- General smooth-field normality premise, Stacks 056T (33.25.4), using
its ordinary normality consequence. Inspected 2026-10-09; the page has no
correction comments. The proof passes through 056S and 0569. This statement
is retained, not claimed to be proved in the pinned library. -/

/- General normal-scheme component theorem, Stacks 0357 (28.7.5), specialized
to locally Noetherian schemes as in 033N (28.7.7). Inspected 2026-10-09.
The 2018 correction removes an unjustified global finiteness claim; no such
claim occurs here. Its full algebraic proof is a retained general premise. -/

/- Local domains imply reducedness of the actual structure sheaf. -/

/- Connectedness turns an open-and-closed irreducible component into the
whole scheme; reducedness is independently obtained from the actual stalks. -/

variable {F : Type u} [Field F] {X : FScheme F}

/-- The nonempty connectedness conclusion uses `ConnectedSpace`, not merely
preconnectedness. In particular the empty scheme is excluded. -/
theorem curveProperties_connectedSpace (h : Properties X) : ConnectedSpace X.left := by
  letI : GeometricallyConnected X.hom := h.connected
  exact GeometricallyConnected.connectedSpace_of_subsingleton X.hom

theorem curveProperties_nonempty (h : Properties X) : Nonempty X.left := by
  letI := curveProperties_connectedSpace h
  infer_instance

theorem curveProperties_smooth (h : Properties X) : Smooth X.hom := by
  letI := h.smooth
  exact SmoothOfRelativeDimension.smooth 1 X.hom

theorem curveProperties_locallyOfFiniteType (h : Properties X) :
    LocallyOfFiniteType X.hom := by
  letI := curveProperties_smooth h
  infer_instance

theorem curveProperties_isNoetherian (h : Properties X) : IsNoetherian X.left := by
  letI : IsProper X.hom := h.proper
  letI : LocallyOfFiniteType X.hom := curveProperties_locallyOfFiniteType h
  letI : IsLocallyNoetherian X.left := LocallyOfFiniteType.isLocallyNoetherian X.hom
  letI : CompactSpace X.left := QuasiCompact.compactSpace_of_compactSpace X.hom
  exact ⟨⟩

/-- The actual curve conditions are preserved along every structural field map,
not only along a selected algebraic closure. -/
theorem curveProperties_baseChange (h : Properties X) (K : Type u) [Field K]
    (s : Spec (.of K) ⟶ Base F) :
    Properties (Over.mk (pullback.snd X.hom s)) := by
  letI := h.smooth
  letI := h.proper
  letI := h.connected
  refine ⟨?_, ?_, ?_⟩
  · exact MorphismProperty.pullback_snd X.hom s h.smooth
  · change IsProper (pullback.snd X.hom s)
    infer_instance
  · change GeometricallyConnected (pullback.snd X.hom s)
    infer_instance

/-- Exact existing `Properties` bridge, conditional only on the two
independently stated arbitrary-scheme normality theorem families above. -/
theorem curveProperties_geometricallyIntegral
    (hnormal : SmoothFieldNormality.{u}) (hcomp : NormalComponentsOpen.{u})
    (h : Properties X) : GeometricallyIntegral X.hom := by
  constructor
  intro K _ s Z fst snd hp
  letI : Smooth snd := MorphismProperty.of_isPullback hp (curveProperties_smooth h)
  letI : GeometricallyConnected snd := MorphismProperty.of_isPullback hp h.connected
  letI : IsLocallyNoetherian Z := LocallyOfFiniteType.isLocallyNoetherian snd
  letI : ConnectedSpace Z := GeometricallyConnected.connectedSpace_of_subsingleton snd
  exact isIntegral_of_connected_normalStalks hcomp Z (hnormal K Z snd inferInstance)

theorem curveProperties_isIntegral
    (hnormal : SmoothFieldNormality.{u}) (hcomp : NormalComponentsOpen.{u})
    (h : Properties X) : IsIntegral X.left := by
  letI := curveProperties_geometricallyIntegral hnormal hcomp h
  exact GeometricallyIntegral.isIntegral_of_subsingleton X.hom

/- General smooth-field regularity of actual local rings, Stacks 056S.
Statement, proof route and comment inspected 2026-10-09. -/

/- General relative-to-absolute dimension theorem for nonempty smooth field
schemes. The standard-smooth convention is related to fibre dimension by
Stacks 02G1/02G2 (29.35.12–13), via 10.137.6. Retained general premise,
not a theorem of the pinned library. -/

/- General closed-point dimension theorem for smooth field schemes.
Stacks 02G1/02G2 and 0A21 (33.20.3(2)); statement and proof inspected
2026-10-09. The 2026 correction to 0A21 concerns specialization notation in
part (9), not part (2). This does not assert dimension n at generic points. -/

variable {F : Type u} [Field F] {X : FScheme F}

theorem curveProperties_dimension (hdim : SmoothFieldDimension.{u})
    (h : Properties X) : topologicalKrullDim X.left = 1 :=
  hdim F X.left X.hom 1 h.smooth (curveProperties_nonempty h)

theorem curveProperties_stalk_regular (hreg : SmoothFieldRegularity.{u})
    (h : Properties X) (x : X.left) : IsRegularLocalRing (X.left.presheaf.stalk x) :=
  hreg F X.left X.hom (curveProperties_smooth h) x

theorem curveProperties_closedPoint_stalk_dimension
    (hdim : SmoothClosedPointDimension.{u}) (h : Properties X)
    (x : X.left) (hx : IsClosed ({x} : Set X.left)) :
    ringKrullDim (X.left.presheaf.stalk x) = 1 :=
  hdim F X.left X.hom 1 h.smooth x hx

/-- Actual codimension-one input for the divisor module, deduced from the
local-ring dimension comparison in the pinned library. -/
theorem curveProperties_closedPoint_coheight
    (hdim : SmoothClosedPointDimension.{u}) (h : Properties X)
    (x : X.left) (hx : IsClosed ({x} : Set X.left)) : Order.coheight x = 1 := by
  have hd := curveProperties_closedPoint_stalk_dimension hdim h x hx
  rw [ringKrullDim_stalk_eq_coheight] at hd
  exact_mod_cast hd

/-- Absolute dimension remains one along every structural field map. -/
theorem curveProperties_baseChange_dimension
    (hdim : SmoothFieldDimension.{u}) (h : Properties X)
    (K : Type u) [Field K] (s : Spec (.of K) ⟶ Base F) :
    topologicalKrullDim (pullback X.hom s : Scheme.{u}) = 1 :=
  curveProperties_dimension hdim (curveProperties_baseChange h K s)

/-- A regular one-dimensional local domain is a DVR, by the proved cotangent
space characterization. The domain hypothesis comes from actual normal stalks. -/
theorem curveProperties_closedPoint_stalk_dvr
    (hnormal : SmoothFieldNormality.{u}) (hreg : SmoothFieldRegularity.{u})
    (hdim : SmoothClosedPointDimension.{u}) (h : Properties X)
    (x : X.left) (hx : IsClosed ({x} : Set X.left)) :
    letI := (hnormal F X.left X.hom (curveProperties_smooth h) x).1
    IsDiscreteValuationRing (X.left.presheaf.stalk x) := by
  letI : IsDomain (X.left.presheaf.stalk x) :=
    (hnormal F X.left X.hom (curveProperties_smooth h) x).1
  letI := curveProperties_stalk_regular hreg h x
  apply IsLocalRing.finrank_CotangentSpace_eq_one_iff.mp
  have hr := (IsRegularLocalRing.iff_finrank_cotangentSpace (X.left.presheaf.stalk x)).mp
    (curveProperties_stalk_regular hreg h x)
  rw [curveProperties_closedPoint_stalk_dimension hdim h x hx] at hr
  exact_mod_cast hr

end AlgebraicGeometry.Scheme.OverField.Curve
