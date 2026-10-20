/-
Copyright (c) 2026 kangxyz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.Morphisms.Smooth.Reduced
public import Aglib.AlgebraicGeometry.Properties.IrreducibleComponents
public import Aglib.RingTheory.LocalRing.PrincipalMaximalIdeal
public import Aglib.AlgebraicGeometry.RationalPoint.SmoothCurve
public import Mathlib.AlgebraicGeometry.Geometrically.Integral
public import Mathlib.AlgebraicGeometry.Geometrically.Connected

/-!
# Geometric integrality of smooth connected curves

For a scheme smooth of relative dimension one over an arbitrary field, every
stalk is a domain. At a rational point, smoothness supplies reducedness and
cotangent dimension one, so the maximal ideal is principal and the local ring
is a domain. At an arbitrary point, base change to its actual residue field
makes that point rational. The faithfully flat stalk map descends the domain
property to the original stalk.

Domain stalks prevent distinct irreducible components from meeting. Local
Noetherianity makes the components open, so connectedness implies
irreducibility and hence integrality. Applying the same proof after arbitrary
field base change gives geometric integrality from geometric connectedness.
No properness, perfectness, characteristic, or integrality premise is used.

## Source correspondence

Auxiliary geometry for `K2-018#sec:k2018-splitting`, lines 240–249,
`K2-018#lem:k2018-residue-bockstein`, lines 308–339, and
`K2-018#prop:k2018-arithmetic-characters`, lines 341–445, in
`research/exposes/K2/018/expose.tex` at revision
`e73d98b1b5c1e5abcdebf7d058e436d792b87982`, source SHA-256
`e716cfb3c6eaba82370c5b46b806df5705ad4583df0ed41b1a576e419f3bd299`.

The last theorem discharges the geometric-integrality input of
`PointedGroupMorphisms.isMonHom_of_geometricallyIntegral` for the actual
`PointedIsogenies.CurveProperties` source. It does not instantiate the remaining
genus, Riemann–Hurwitz, or group-law fields of `GeometryBackground`, nor does it
prove Quillen specialization or the complete arithmetic-character theorem.

Implementation basis: `6987216b7dfb16036f94cc41b3c33a2da4e5e535`;
Lean `4.34.1`, mathlib `d13f23b723b8a846827a245b89c10fc7d3f11612`.
The actual rational-point cotangent calculation is imported from
`R5Lab.AlgebraicGeometry.LocalRing.SmoothCurve`.
-/

@[expose] public section

open _root_.AlgebraicGeometry.Scheme
  (irreducibleSpace_of_connected_of_isLocallyNoetherian_of_isDomain_stalk
    isReduced_of_smooth_over_field)



noncomputable section
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory Limits AlgebraicGeometry
universe u
namespace AlgebraicGeometry.Scheme
variable {F : Type u} [Field F] {X : Scheme.{u}}

/- Auxiliary geometry for the three `K2-018` locators and pinned source above:
a scheme smooth over a field is reduced. -/

/-- Auxiliary origin geometry for `K2-018#sec:k2018-splitting` and
`K2-018#lem:k2018-residue-bockstein`, pinned above: the actual rational-origin stalk of
a smooth relative-dimension-one scheme is a domain. No integral-scheme premise is supplied. -/
lemma RationalPoint.localRing_isDomain_of_smoothOfRelativeDimension_one
    (q : RationalPoint F X) [SmoothOfRelativeDimension 1 q.structureMap] :
    IsDomain q.localRing := by
  have : Smooth q.structureMap := SmoothOfRelativeDimension.smooth 1 q.structureMap
  have : IsReduced X := isReduced_of_smooth_over_field q.structureMap
  have : IsNoetherianRing q.localRing := q.localRing_isNoetherianRing
  exact IsLocalRing.isDomain_of_isReduced_of_finrank_cotangentSpace_le_one _
    (by rw [q.localRing_finrank_cotangentSpace 1])

/-- Auxiliary geometry for the three `K2-018` locators and pinned source above:
every actual stalk of a smooth relative-dimension-one scheme over a field is a domain.
The rational point after residue-field base change and the injective stalk map are constructed. -/
lemma isDomain_stalk_of_smoothOfRelativeDimension_one
    (f : X ⟶ Spec (.of F)) [SmoothOfRelativeDimension 1 f] (x : X) :
    IsDomain (X.presheaf.stalk x) := by
  let s := X.fromSpecResidueField x ≫ f
  let q : RationalPoint (X.residueField x) (pullback f s) :=
    { structureMap := pullback.snd f s
      sectionMap := pullback.lift (X.fromSpecResidueField x) (𝟙 _) (by simp [s])
      section_comp := by simp }
  have hq : SmoothOfRelativeDimension 1 q.structureMap := by
    exact MorphismProperty.pullback_snd f s (inferInstance : SmoothOfRelativeDimension 1 f)
  have : IsDomain q.localRing := q.localRing_isDomain_of_smoothOfRelativeDimension_one
  have he : pullback.fst f s q.point = x := by
    change (q.sectionMap ≫ pullback.fst f s) (IsLocalRing.closedPoint _) = x
    simp only [q, pullback.lift_fst]
    apply Scheme.fromSpecResidueField_apply
  let g := pullback.fst f s
  have hi : Function.Injective (g.stalkMap q.point).hom := by
    algebraize [(g.stalkMap q.point).hom]
    have : Module.FaithfullyFlat (X.presheaf.stalk (g q.point))
        ((pullback f s).presheaf.stalk q.point) :=
      @Module.FaithfullyFlat.of_flat_of_isLocalHom _ _ _ _ _ _ _
        (Flat.stalkMap g q.point) (g.toLRSHom.prop q.point)
    exact ‹RingHom.FaithfullyFlat _›.injective
  have : IsDomain (X.presheaf.stalk (g q.point)) :=
    Function.Injective.isDomain (g.stalkMap q.point).hom hi
  rw [← he]
  exact this

/- Auxiliary geometry for `K2-018#prop:k2018-arithmetic-characters`, pinned above:
two irreducible components through a point with a domain stalk coincide. -/

/- Auxiliary geometry for `K2-018#prop:k2018-arithmetic-characters`, pinned above:
with finitely many irreducible components and domain stalks, each component is open. -/

/- Auxiliary geometry for `K2-018#prop:k2018-arithmetic-characters`, pinned above:
local Noetherianity and domain stalks make each irreducible component open. -/

/- Auxiliary geometry for `K2-018#prop:k2018-arithmetic-characters`, pinned above:
a connected locally Noetherian scheme with domain stalks is irreducible. -/

/-- Auxiliary geometry for `K2-018#prop:k2018-arithmetic-characters`, pinned above:
a connected scheme smooth of relative dimension one over any field is integral. -/
lemma isIntegral_of_connected_of_smoothOfRelativeDimension_one
    (f : X ⟶ Spec (.of F)) [SmoothOfRelativeDimension 1 f] [ConnectedSpace X] :
    IsIntegral X := by
  have : Smooth f := SmoothOfRelativeDimension.smooth 1 f
  have : IsLocallyNoetherian X := LocallyOfFiniteType.isLocallyNoetherian f
  have (x : X) : IsDomain (X.presheaf.stalk x) :=
    isDomain_stalk_of_smoothOfRelativeDimension_one f x
  have : IsReduced X := isReduced_of_smooth_over_field f
  have : IrreducibleSpace X :=
    irreducibleSpace_of_connected_of_isLocallyNoetherian_of_isDomain_stalk
  exact isIntegral_of_irreducibleSpace_of_isReduced X

/-- Auxiliary curve geometry for `K2-018#prop:k2018-arithmetic-characters`, pinned above:
smooth relative dimension one and geometric connectedness imply geometric integrality.
These are exactly the smoothness and connectedness fields of the actual `CurveProperties`
consumer; properness is unnecessary for this bridge. -/
lemma geometricallyIntegral_of_smoothOfRelativeDimension_one_of_geometricallyConnected
    (f : X ⟶ Spec (.of F)) [SmoothOfRelativeDimension 1 f] [GeometricallyConnected f] :
    GeometricallyIntegral f := by
  constructor
  intro K _ s Y fst snd h
  have : SmoothOfRelativeDimension 1 snd :=
    MorphismProperty.of_isPullback h (inferInstance : SmoothOfRelativeDimension 1 f)
  have : ConnectedSpace Y := GeometricallyConnected.geometrically_connectedSpace s fst snd h
  exact isIntegral_of_connected_of_smoothOfRelativeDimension_one snd

end AlgebraicGeometry.Scheme

/- Migration source: R5Lab/Aglib/AlgebraicGeometry/Geometrically/Integral/SmoothCurve.lean
Frozen packet R5 f8a3314ddecffcada2ec721d26d56a937bed9690.
SHA-256 4c2eda97d1152603a1395a2a41cd1b35501ddb25eea495232f705cc063316d94.
Native names and imports replace source wrappers; stated conditions and maps are retained. -/
