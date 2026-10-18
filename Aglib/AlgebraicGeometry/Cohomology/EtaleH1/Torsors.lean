/-
Copyright (c) 2026 kangxyz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/

module

/- Current interface basis: 46f53465aaf3b0167049e9c8e9e2294111bb4281.
Original construction and mathematical provenance are retained below. -/
public import Aglib.AlgebraicGeometry.Cohomology.EtaleH1.FiniteLocallyConstant
public import Aglib.AlgebraicGeometry.Cohomology.EtaleH1.PullbackComposition

/-!
# Genuine sheaf torsors on the small étale site

Definition layer for `K2-018#eq:k2018-pointed-character`, frozen source
`7f86e4a1763cc4ec35e9b0a8acd659750355a0de`. Actions are defined on an actual
sheaf, commute with restrictions, and are simply transitive wherever sections
exist. Local nonemptiness is a covering-sieve condition. We deliberately do
not require nonempty sections on every test scheme.

The quotient here is the set of isomorphism classes of these sheaf torsors;
it is not substituted for `H1Etale`. The canonical Ext class and contracted
sum are separate constructions.
-/

@[expose] public section

noncomputable section
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory AlgebraicGeometry Opposite
namespace AlgebraicGeometry.Scheme.EtaleH1
universe u

/-- Sheaves of sets in `Type (u + 1)` on the small étale site of `X`. -/
abbrev SetSheaf (X : Scheme.{u}) := Sheaf (Scheme.smallEtaleTopology X) (Type (u + 1))

/-- The sieve on which a sheaf has a section. -/
def nonemptySieve {X : Scheme.{u}} (T : SetSheaf X) (U : X.Etale) : Sieve U where
  arrows {V} _ := Nonempty (T.obj.obj (op V))
  downward_closed h g := h.map (T.obj.map g.op)

/-- A left torsor for an actual abelian sheaf, including local nonemptiness. -/
structure Torsor {X : Scheme.{u}} (L : AbelianSheaf.{u, u + 1} X) where
  /-- The sheaf of sets underlying the torsor. -/
  carrier : SetSheaf X
  /-- The sectionwise left action of the coefficient sheaf on the torsor's carrier. -/
  action : ∀ U, L.obj.obj U → carrier.obj.obj U → carrier.obj.obj U
  zero_action : ∀ U t, action U 0 t = t
  add_action : ∀ U a b t, action U (a + b) t = action U a (action U b t)
  naturality : ∀ {U V} (f : U ⟶ V) a t,
    carrier.obj.map f (action U a t) = action V (L.obj.map f a) (carrier.obj.map f t)
  unique_transport : ∀ U s t, ∃! a, action U a s = t
  locally_nonempty : ∀ U, nonemptySieve carrier U ∈ Scheme.smallEtaleTopology X U

/-- The underlying sheaf of sets of an abelian sheaf. -/
abbrev underlyingSetSheaf {X : Scheme.{u}} (L : AbelianSheaf.{u, u + 1} X) : SetSheaf X :=
  ⟨L.obj ⋙ CategoryTheory.forget AddCommGrpCat, Presheaf.isSheaf_comp_of_isSheaf _ _ _ L.property⟩

/-- The trivial left torsor, with the regular translation action. -/
abbrev trivialTorsor {X : Scheme.{u}} (L : AbelianSheaf.{u, u + 1} X) : Torsor L where
  carrier := underlyingSetSheaf L
  action U a t := a + (show L.obj.obj U from t)
  zero_action _ _ := zero_add _
  add_action _ _ _ _ := add_assoc _ _ _
  naturality f a t := (L.obj.map f).hom.map_add a t
  unique_transport U s t := ⟨t - s, sub_add_cancel _ _,
    fun a ha => (eq_sub_iff_add_eq).mpr ha⟩
  locally_nonempty U := by
    have h : nonemptySieve (underlyingSetSheaf L) U = ⊤ := by
      ext V f
      exact iff_of_true ⟨0⟩ trivial
    rw [h]
    exact (Scheme.smallEtaleTopology X).top_mem U

namespace Torsor
variable {X : Scheme.{u}} {L : AbelianSheaf.{u, u + 1} X}

/-- The section-level additive action, without assuming a global section. -/
@[instance_reducible]
def sectionAction (P : Torsor L) (U : X.Etaleᵒᵖ) :
    AddAction (L.obj.obj U) (P.carrier.obj.obj U) where
  vadd := P.action U
  add_vadd := P.add_action U
  zero_vadd := P.zero_action U

/-- Pairwise unique transport remains meaningful even for empty section sets. -/
theorem sectionAction_unique_transport (P : Torsor L) (U : X.Etaleᵒᵖ) :
    letI := P.sectionAction U
    ∀ s t : P.carrier.obj.obj U, ∃! a : L.obj.obj U, a +ᵥ s = t :=
  P.unique_transport U

/-- A chosen section identifies the coefficient group with its torsor fibre.
This choice is only available on test objects where a section exists. -/
def sectionEquiv (P : Torsor L) (U : X.Etaleᵒᵖ) (s : P.carrier.obj.obj U) :
    L.obj.obj U ≃ P.carrier.obj.obj U :=
  Equiv.ofBijective (P.action U · s) ⟨
    fun a _b h => (P.unique_transport U s (P.action U a s)).unique rfl h.symm,
    fun t => (P.unique_transport U s t).exists⟩

/-- Equivariant isomorphisms are actual isomorphisms of the underlying sheaves. -/
structure Iso (P Q : Torsor L) where
  /-- The underlying isomorphism between the carrier sheaves of the two torsors. -/
  carrierIso : P.carrier ≅ Q.carrier
  equivariant : ∀ U a t,
    carrierIso.hom.hom.app U (P.action U a t) = Q.action U a (carrierIso.hom.hom.app U t)

/-- The torsor isomorphism whose carrier map is the identity. -/
def Iso.refl (P : Torsor L) : Iso P P where
  carrierIso := CategoryTheory.Iso.refl P.carrier
  equivariant _ _ _ := rfl

/-- The inverse torsor isomorphism, with the inverse carrier isomorphism. -/
def Iso.symm {P Q : Torsor L} (e : Iso P Q) : Iso Q P where
  carrierIso := e.carrierIso.symm
  equivariant U a t := by
    apply (ConcreteCategory.bijective_of_isIso (e.carrierIso.hom.hom.app U)).injective
    rw [e.equivariant]
    have hi (s : Q.carrier.obj.obj U) :
        e.carrierIso.hom.hom.app U (e.carrierIso.inv.hom.app U s) = s :=
      congrArg (fun q : Q.carrier ⟶ Q.carrier => q.hom.app U s) e.carrierIso.inv_hom_id
    exact (hi (Q.action U a t)).trans (congrArg (Q.action U a) (hi t)).symm

/-- The composite torsor isomorphism, applying `e` and then `d` on carrier sections. -/
def Iso.trans {P Q R : Torsor L} (e : Iso P Q) (d : Iso Q R) : Iso P R where
  carrierIso := e.carrierIso ≪≫ d.carrierIso
  equivariant U a t := by
    change d.carrierIso.hom.hom.app U (e.carrierIso.hom.hom.app U (P.action U a t)) = _
    rw [e.equivariant, d.equivariant]
    rfl

/-- Isomorphism relation on actual sheaf torsors. -/
def isomorphicSetoid (L : AbelianSheaf.{u, u + 1} X) : Setoid (Torsor L) where
  r P Q := Nonempty (Iso P Q)
  iseqv := ⟨fun P => ⟨Iso.refl P⟩,
    fun ⟨e⟩ => ⟨e.symm⟩, fun ⟨e⟩ ⟨d⟩ => ⟨e.trans d⟩⟩

/-- Restrict an actual global torsor section to an arbitrary étale test object. -/
def restrictGlobalSection (P : Torsor L)
    (s : P.carrier.obj.obj (op (etaleTerminal X))) (U : X.Etaleᵒᵖ) :
    P.carrier.obj.obj U :=
  P.carrier.obj.map ((etaleTerminalIsTerminal X).from U.unop).op s

theorem restrictGlobalSection_naturality (P : Torsor L)
    (s : P.carrier.obj.obj (op (etaleTerminal X))) {U V : X.Etaleᵒᵖ} (f : U ⟶ V) :
    P.carrier.obj.map f (P.restrictGlobalSection s U) = P.restrictGlobalSection s V := by
  have h : ((etaleTerminalIsTerminal X).from U.unop).op ≫ f =
      ((etaleTerminalIsTerminal X).from V.unop).op :=
    congrArg Quiver.Hom.op ((etaleTerminalIsTerminal X).hom_ext _ _)
  change P.carrier.obj.map f (P.carrier.obj.map
    ((etaleTerminalIsTerminal X).from U.unop).op s) = _
  rw [← Functor.map_comp_apply, h]
  rfl

/-- A global section constructs an actual equivariant sheaf trivialization. -/
def trivializationOfSection (P : Torsor L)
    (s : P.carrier.obj.obj (op (etaleTerminal X))) : Iso (trivialTorsor L) P where
  carrierIso := ObjectProperty.isoMk _ (NatIso.ofComponents
    (fun U => (P.sectionEquiv U (P.restrictGlobalSection s U)).toIso)
    (fun f => by
      ext a
      change P.action _ (L.obj.map f a) (P.restrictGlobalSection s _) =
        P.carrier.obj.map f (P.action _ a (P.restrictGlobalSection s _))
      rw [P.naturality, P.restrictGlobalSection_naturality]))
  equivariant U a t := P.add_action U a t _

/-- A torsor has a global section precisely when it is equivariantly trivial. -/
theorem nonempty_globalSections_iff_trivial (P : Torsor L) :
    Nonempty (P.carrier.obj.obj (op (etaleTerminal X))) ↔
      Nonempty (Iso (trivialTorsor L) P) := by
  constructor
  · rintro ⟨s⟩
    exact ⟨P.trivializationOfSection s⟩
  · rintro ⟨e⟩
    exact ⟨e.carrierIso.hom.hom.app (op (etaleTerminal X)) 0⟩

end Torsor

/-- Isomorphism classes of genuine sheaf torsors, without yet asserting an
abelian-group structure or a comparison with Ext. -/
def TorsorClass {X : Scheme.{u}} (L : AbelianSheaf.{u, u + 1} X) :=
  Quotient (Torsor.isomorphicSetoid L)

end AlgebraicGeometry.Scheme.EtaleH1

/- Migration source: the R5Lab/Aglib mirror; exact module in the migration record.
R5 revision c82abf3a72ce1e1cedf4a4f1fe08bea994ad4df5.
SHA256 f4093c2299adf5e9d2c0a650518d3534d20d88be36ba291f0c63aab9e403e95b.
Definitions, hypotheses and universes are retained modulo native names. -/
