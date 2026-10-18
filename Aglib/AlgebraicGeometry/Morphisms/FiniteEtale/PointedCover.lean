/-
Copyright (c) 2026 kangxyz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/

module

public import Aglib.AlgebraicGeometry.SchemeOverField
public import Aglib.CategoryTheory.TorsorAction.Basic
public import Mathlib.AlgebraicGeometry.Morphisms.Finite
public import Mathlib.AlgebraicGeometry.Morphisms.Etale
public import Mathlib.AlgebraicGeometry.Morphisms.Proper
public import Mathlib.AlgebraicGeometry.Geometrically.Connected
public import Mathlib.CategoryTheory.Monoidal.Cartesian.Over
public import Mathlib.Data.ZMod.Basic

/-!
# Pointed finite torsor covers and cyclic coefficients

Source: `K2-018#eq:k2018-pointed-character` and
`K2-018#prop:k2018-arithmetic-characters`, `research/exposes/K2/018/expose.tex`
lines 341–445 at HEAD `e73d98b1b5c1e5abcdebf7d058e436d792b87982`, SHA256
`e716cfb3c6eaba82370c5b46b806df5705ad4583df0ed41b1a576e419f3bd299`.

This generic split contains Base, FScheme, CyclicCoefficient, PointedTorsorCover, geometric_card,
CoverIso and coverSetoid.

Every geometric object in the original source is an actual scheme over `Spec F`; every group
object is a `Grp (Over (Spec F))`, and every morphism is defined over `F`.
A coefficient group scheme may have nontrivial Galois action. Geometric
cyclicity does not identify that action with the Tate-square twist: realization
of the specific Galois module `Z/n(2)` remains an explicit comparison input.

The companion Curves/PointedIsogeny supplies the curve-specific declarations.
`GeometryBackground` separates general results not presently instantiated from
the manuscript deductions proved here. Its genus function is external: its
identification with coherent-cohomological genus has not been formalized.
Degree means cardinality of every algebraically closed geometric fibre; the
comparison with finite locally free rank has not been formalized. The fields
are general Riemann–Hurwitz, pointed genus-one group-law existence, the pointed
proper-group morphism theorem, finite-cover lift rigidity, and existence of
points in finite surjective fibres over algebraically closed fields. No field
asserts character/isogeny equivalence or that a torsor is an isogeny.

The passage from primitive continuous characters/H¹ to the pointed connected
torsor input, its converse classification, and a Weierstrass/group-scheme bridge
remain uninstantiated. The retained conditional theorem proves the geometric
deductions from that input; compilation does not discharge the background.
-/

@[expose] public section

open _root_.AlgebraicGeometry.Scheme.OverField (Base FScheme)

noncomputable section

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open CategoryTheory MonoidalCategory CartesianMonoidalCategory MonObj
open scoped CategoryTheory.MonObj
open AlgebraicGeometry
open CategoryTheory

namespace AlgebraicGeometry.Scheme.FiniteEtale.PointedCovers

universe u

variable (F : Type u) [Field F]

/- `K2-018#prop:k2018-arithmetic-characters`, pinned snapshot above: the
actual base scheme, with no rational-point replacement. -/

/- `K2-018#prop:k2018-arithmetic-characters`, pinned snapshot above: schemes
and morphisms over the field of definition. -/

attribute [local instance] Over.cartesianMonoidalCategory

variable {F}

/-- `K2-018#prop:k2018-arithmetic-characters`, pinned snapshot above: an actual
finite étale coefficient group scheme of geometric cyclic order `n`. This does
not assert that its descent action is the Tate-square action. -/
structure CyclicCoefficient (A : Grp (FScheme F)) (n : ℕ) : Prop where
  positive : 0 < n
  finite : IsFinite A.X.hom
  etale : Etale A.X.hom
  geometric_cyclic : ∀ (K : Type u) [Field K] [IsAlgClosed K]
    (s : Spec (CommRingCat.of K) ⟶ Base F),
    Nonempty ((Over.mk s ⟶ A.X) ≃* Multiplicative (ZMod n))

/-- `K2-018#prop:k2018-arithmetic-characters`, pinned snapshot above: the
primitive character's required geometric output, specified independently of
isogenies. The action is natural on all scheme-valued points. -/
structure PointedTorsorCover (A E : Grp (FScheme F)) where
  /-- The source scheme of the torsor cover, viewed over `Spec F`. -/
  X : FScheme F
  /-- The finite étale surjective morphism from the cover to the base group scheme `E.X`. -/
  map : X ⟶ E.X
  finite : IsFinite map.left
  etale : Etale map.left
  surjective : Surjective map.left
  connected : GeometricallyConnected X.hom
  /-- The chosen origin section of the cover above the unit of `E`. -/
  origin : 𝟙_ (FScheme F) ⟶ X
  pointed : origin ≫ map = η[E.X]
  /-- The torsor action of the coefficient group scheme `A` on the cover morphism `map`. -/
  action : TorsorAction A map

variable {A : Grp (FScheme F)} {n : ℕ}

/-- `K2-018#prop:k2018-arithmetic-characters`, pinned snapshot above: the
coefficient's geometric cyclicity gives order `n`, without making its Galois
descent action constant. -/
theorem CyclicCoefficient.geometric_card (a : CyclicCoefficient A n)
    (K : Type u) [Field K] [IsAlgClosed K]
    (s : Spec (CommRingCat.of K) ⟶ Base F) :
    Nat.card (Over.mk s ⟶ A.X) = n := by
  let : NeZero n := ⟨Nat.ne_of_gt a.positive⟩
  obtain ⟨e⟩ := a.geometric_cyclic K s
  calc
    Nat.card (Over.mk s ⟶ A.X) = Nat.card (Multiplicative (ZMod n)) := Nat.card_congr e.toEquiv
    _ = n := by simp

/-- `K2-018#prop:k2018-arithmetic-characters`, pinned snapshot above: an
independently specified isomorphism of pointed coefficient torsors. The source
isomorphism is over `F`, commutes with the target, preserves the chosen origin,
and intertwines the action on every test scheme. -/
structure CoverIso {A H : Grp (FScheme F)}
    (c d : PointedTorsorCover A H) where
  /-- The isomorphism of the source schemes over `Spec F`, required to respect the
  cover maps, origins and actions by the remaining fields. -/
  iso : c.X ≅ d.X
  over : iso.hom ≫ d.map = c.map
  pointed : c.origin ≫ iso.hom = d.origin
  equivariant : ∀ {T : FScheme F} (a : T ⟶ A.X) (x : T ⟶ c.X),
    c.action.act a x ≫ iso.hom = d.action.act a (x ≫ iso.hom)

/-- `K2-018#prop:k2018-arithmetic-characters`, pinned snapshot above: identity
pointed equivariant cover isomorphism. -/
def CoverIso.refl {A H : Grp (FScheme F)} (c : PointedTorsorCover A H) :
    CoverIso c c where
  iso := Iso.refl c.X
  over := by simp
  pointed := by simp
  equivariant a x := by simp

/-- `K2-018#prop:k2018-arithmetic-characters`, pinned snapshot above: inverse
pointed equivariant cover isomorphism. -/
def CoverIso.symm {A H : Grp (FScheme F)} {c d : PointedTorsorCover A H}
    (h : CoverIso c d) : CoverIso d c where
  iso := h.iso.symm
  over := by rw [← h.over]; simp
  pointed := by rw [← h.pointed]; simp
  equivariant a x := by
    apply (cancel_mono h.iso.hom).1
    simp [Category.assoc, h.equivariant]

/-- `K2-018#prop:k2018-arithmetic-characters`, pinned snapshot above:
composition of pointed equivariant cover isomorphisms. -/
def CoverIso.trans {A H : Grp (FScheme F)} {c d e : PointedTorsorCover A H}
    (h : CoverIso c d) (k : CoverIso d e) : CoverIso c e where
  iso := h.iso.trans k.iso
  over := by simp [Category.assoc, k.over, h.over]
  pointed := by simp [← Category.assoc, h.pointed, k.pointed]
  equivariant a x := by simp [← Category.assoc, h.equivariant, k.equivariant]

/-- `K2-018#prop:k2018-arithmetic-characters`, pinned snapshot above: the
independent relation of pointed equivariant `F`-isomorphism of torsor covers. -/
def coverSetoid (A H : Grp (FScheme F)) : Setoid (PointedTorsorCover A H) where
  r c d := Nonempty (CoverIso c d)
  iseqv := ⟨fun c => ⟨CoverIso.refl c⟩,
    fun ⟨h⟩ => ⟨h.symm⟩, fun ⟨h⟩ ⟨k⟩ => ⟨h.trans k⟩⟩

end AlgebraicGeometry.Scheme.FiniteEtale.PointedCovers

/- Migration source: the R5Lab/Aglib mirror; exact module in the migration record.
R5 revision c82abf3a72ce1e1cedf4a4f1fe08bea994ad4df5.
SHA256 2e20b9b6e8dff9f59d51869a1b39625553dcdb01c78b904d91f2676871292aff.
Definitions, hypotheses and universes are retained modulo native names. -/
