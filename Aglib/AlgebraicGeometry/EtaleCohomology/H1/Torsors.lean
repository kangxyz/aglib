/-
Copyright (c) 2026 kangxyz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

/- Current interface basis: 46f53465aaf3b0167049e9c8e9e2294111bb4281.
Original construction and mathematical provenance are retained below. -/
public import Aglib.CategoryTheory.Sites.Torsor.Basic
public import Aglib.AlgebraicGeometry.EtaleCohomology.H1.FiniteLocallyConstant
public import Aglib.AlgebraicGeometry.EtaleCohomology.H1.PullbackComposition

/-!
# Genuine sheaf torsors on the small etale site

The original Scheme interface specializes the selected generic-site torsor.
Its carrier, action, local nonemptiness, equivariant isomorphisms and quotient
are the same implementation. The augmentation, canonical Ext class and
contracted sum remain the existing original constructions.
-/

@[expose] public noncomputable section

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open CategoryTheory AlgebraicGeometry Opposite

namespace AlgebraicGeometry.Scheme.EtaleCohomology

universe u

/-- Sheaves of sets in the original small-etale value universe. -/
abbrev SetSheaf (X : Scheme.{u}) := Sheaf (Scheme.smallEtaleTopology X) (Type (u + 1))

/-- The original locally nonempty-section sieve. -/
abbrev nonemptySieve {X : Scheme.{u}} (T : SetSheaf X) (U : X.Etale) : Sieve U :=
  CategoryTheory.Sheaf.nonemptySieve T U

/-- The selected generic-site torsor with the original etale coefficient and carrier worlds. -/
abbrev Torsor {X : Scheme.{u}} (L : AbelianSheaf.{u, u + 1} X) :=
  CategoryTheory.Sheaf.Torsor L

/-- The original underlying-set sheaf, using native sheaf composition. -/
abbrev underlyingSetSheaf {X : Scheme.{u}} (L : AbelianSheaf.{u, u + 1} X) : SetSheaf X :=
  CategoryTheory.Sheaf.underlyingSetSheaf L

/-- The original regular translation torsor. -/
abbrev trivialTorsor {X : Scheme.{u}} (L : AbelianSheaf.{u, u + 1} X) : Torsor L :=
  CategoryTheory.Sheaf.trivialTorsor L

namespace Torsor

variable {X : Scheme.{u}} {L : AbelianSheaf.{u, u + 1} X}

/-- The original constructor, with the same sectionwise data. -/
abbrev mk := CategoryTheory.Sheaf.Torsor.mk (L := L)

/-- The original carrier projection. -/
abbrev carrier (P : Torsor L) := CategoryTheory.Sheaf.Torsor.carrier P

/-- The original action projection. -/
abbrev action (P : Torsor L) := CategoryTheory.Sheaf.Torsor.action P

/-- The original zero-action law. -/
theorem zero_action (P : Torsor L) : ∀ U t, P.action U 0 t = t :=
  CategoryTheory.Sheaf.Torsor.zero_action P

/-- The original additive action law. -/
theorem add_action (P : Torsor L) :
    ∀ U a b t, P.action U (a + b) t = P.action U a (P.action U b t) :=
  CategoryTheory.Sheaf.Torsor.add_action P

/-- The original restriction law for the action. -/
abbrev naturality (P : Torsor L) {U V : X.Etaleᵒᵖ} :=
  CategoryTheory.Sheaf.Torsor.naturality P (U := U) (V := V)

/-- The original unique-transport law. -/
theorem unique_transport (P : Torsor L) : ∀ U s t, ∃! a, P.action U a s = t :=
  CategoryTheory.Sheaf.Torsor.unique_transport P

/-- The original local-nonemptiness law. -/
theorem locally_nonempty (P : Torsor L) :
    ∀ U, nonemptySieve P.carrier U ∈ Scheme.smallEtaleTopology X U :=
  CategoryTheory.Sheaf.Torsor.locally_nonempty P

/-- The original additive action on possibly empty section sets. -/
abbrev sectionAction (P : Torsor L) (U : X.Etaleᵒᵖ) :
    AddAction (L.obj.obj U) (P.carrier.obj.obj U) :=
  CategoryTheory.Sheaf.Torsor.sectionAction P U

/-- The original sectionwise unique-transport statement. -/
theorem sectionAction_unique_transport (P : Torsor L) (U : X.Etaleᵒᵖ) :
    letI := P.sectionAction U
    ∀ s t : P.carrier.obj.obj U, ∃! a : L.obj.obj U, a +ᵥ s = t :=
  CategoryTheory.Sheaf.Torsor.sectionAction_unique_transport P U

/-- The original equivalence determined by an existing section. -/
abbrev sectionEquiv (P : Torsor L) (U : X.Etaleᵒᵖ) (s : P.carrier.obj.obj U) :
    L.obj.obj U ≃ P.carrier.obj.obj U :=
  CategoryTheory.Sheaf.Torsor.sectionEquiv P U s

/-- Original positive transport is the existing augmentation difference in its correct order. -/
theorem sectionEquiv_symm_eq_difference (P : Torsor L) (U : X.Etaleᵒᵖ)
    (s t : P.carrier.obj.obj U) :
    letI := P.sectionAction U
    (P.sectionEquiv U s).symm t =
      AddAction.TorsorAugmentation.difference (P.unique_transport U) t s :=
  CategoryTheory.Sheaf.Torsor.sectionEquiv_symm_eq_difference P U s t

/-- The original equivariant carrier isomorphism. -/
abbrev Iso (P Q : Torsor L) := CategoryTheory.Sheaf.Torsor.Iso P Q

/-- The original equivariant-isomorphism constructor. -/
abbrev Iso.mk {P Q : Torsor L} := CategoryTheory.Sheaf.Torsor.Iso.mk (P := P) (Q := Q)

/-- The original carrier-isomorphism projection. -/
abbrev Iso.carrierIso {P Q : Torsor L} (e : Iso P Q) :=
  CategoryTheory.Sheaf.Torsor.Iso.carrierIso e

/-- The original equivariance projection. -/
abbrev Iso.equivariant {P Q : Torsor L} (e : Iso P Q) :=
  CategoryTheory.Sheaf.Torsor.Iso.equivariant e

/-- The original identity torsor isomorphism. -/
abbrev Iso.refl (P : Torsor L) : Iso P P := CategoryTheory.Sheaf.Torsor.Iso.refl P

/-- The original inverse torsor isomorphism. -/
abbrev Iso.symm {P Q : Torsor L} (e : Iso P Q) : Iso Q P :=
  CategoryTheory.Sheaf.Torsor.Iso.symm e

/-- The original composite torsor isomorphism. -/
abbrev Iso.trans {P Q R : Torsor L} (e : Iso P Q) (d : Iso Q R) : Iso P R :=
  CategoryTheory.Sheaf.Torsor.Iso.trans e d

/-- The original relation of equivariant torsor isomorphism. -/
abbrev isomorphicSetoid (L : AbelianSheaf.{u, u + 1} X) : Setoid (Torsor L) :=
  CategoryTheory.Sheaf.Torsor.isomorphicSetoid L

/-- Restriction from the original terminal etale object. -/
abbrev restrictGlobalSection (P : Torsor L)
    (s : P.carrier.obj.obj (op (etaleTerminal X))) (U : X.Etaleᵒᵖ) :
    P.carrier.obj.obj U :=
  CategoryTheory.Sheaf.Torsor.restrictGlobalSection P (etaleTerminalIsTerminal X) s U

/-- The original terminal-section restriction law. -/
theorem restrictGlobalSection_naturality (P : Torsor L)
    (s : P.carrier.obj.obj (op (etaleTerminal X))) {U V : X.Etaleᵒᵖ} (f : U ⟶ V) :
    P.carrier.obj.map f (P.restrictGlobalSection s U) = P.restrictGlobalSection s V :=
  CategoryTheory.Sheaf.Torsor.restrictGlobalSection_naturality P (etaleTerminalIsTerminal X) s f

/-- The original equivariant trivialization from a genuine global section. -/
abbrev trivializationOfSection (P : Torsor L)
    (s : P.carrier.obj.obj (op (etaleTerminal X))) : Iso (trivialTorsor L) P :=
  CategoryTheory.Sheaf.Torsor.trivializationOfSection P (etaleTerminalIsTerminal X) s

/-- The original equivalence between a global section and equivariant triviality. -/
theorem nonempty_globalSections_iff_trivial (P : Torsor L) :
    Nonempty (P.carrier.obj.obj (op (etaleTerminal X))) ↔
      Nonempty (Iso (trivialTorsor L) P) :=
  CategoryTheory.Sheaf.Torsor.nonempty_globalSections_iff_trivial P (etaleTerminalIsTerminal X)

end Torsor

/-- Original isomorphism classes of the same actual torsors. -/
abbrev TorsorClass {X : Scheme.{u}} (L : AbelianSheaf.{u, u + 1} X) :=
  CategoryTheory.Sheaf.TorsorClass L

end AlgebraicGeometry.Scheme.EtaleCohomology

/- Migration source: the R5Lab/Aglib mirror; exact module in the migration record.
R5 revision c82abf3a72ce1e1cedf4a4f1fe08bea994ad4df5.
SHA256 f4093c2299adf5e9d2c0a650518d3534d20d88be36ba291f0c63aab9e403e95b.
Definitions, hypotheses and universes are retained modulo native names. -/
