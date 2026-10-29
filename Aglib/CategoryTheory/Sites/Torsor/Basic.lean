/-
Copyright (c) 2026 kangxyz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.Algebra.Group.Action.TorsorAugmentation
public import Aglib.CategoryTheory.Monoidal.Cartesian.Shear
public import Aglib.CategoryTheory.Topos.SheafMorphism
public import Mathlib.Algebra.Category.Grp.Limits
public import Mathlib.CategoryTheory.ConcreteCategory.EpiMono
public import Mathlib.CategoryTheory.Limits.Shapes.Terminal
public import Mathlib.CategoryTheory.Sites.CartesianMonoidal
public import Mathlib.CategoryTheory.Sites.LocallySurjective
public import Mathlib.CategoryTheory.Sites.Whiskering

/-!
# Torsors for abelian sheaves on a site

The carrier and its sectionwise action are the original sheaf-torsor data.
Unique transport is required only between existing sections; local
nonemptiness is a covering-sieve condition. No global nonemptiness, points,
sheafification or cohomology realization is required for the torsor itself.

The terminal-object sector is conditional on a specified terminal object.
The underlying-set and trivial-torsor constructions use native sheaf
composition with the forgetful functor.
-/

@[expose] public noncomputable section

open CategoryTheory.Limits Opposite

namespace CategoryTheory.Sheaf

universe u v w

variable {C : Type u} [Category.{v} C] {J : GrothendieckTopology C}

/-- The sieve on which the actual carrier sheaf has a section. -/
def nonemptySieve (P : Sheaf J (Type w)) (U : C) : Sieve U where
  arrows {V} _ := Nonempty (P.obj.obj (op V))
  downward_closed h g := h.map (P.obj.map g.op)

/-- A left torsor for an actual abelian sheaf, including local nonemptiness. -/
structure Torsor (L : Sheaf J AddCommGrpCat.{w}) where
  /-- The sheaf of sets underlying the torsor. -/
  carrier : Sheaf J (Type w)
  /-- The sectionwise action of the coefficient sheaf on the carrier. -/
  action : ∀ U, L.obj.obj U → carrier.obj.obj U → carrier.obj.obj U
  /-- Zero acts as the identity on every existing section. -/
  zero_action : ∀ U t, action U 0 t = t
  /-- The action respects addition of coefficients. -/
  add_action : ∀ U a b t, action U (a + b) t = action U a (action U b t)
  /-- Restriction commutes with the original coefficient action. -/
  naturality : ∀ {U V} (f : U ⟶ V) a t,
    carrier.obj.map f (action U a t) = action V (L.obj.map f a) (carrier.obj.map f t)
  /-- Transport between two existing sections is unique. -/
  unique_transport : ∀ U s t, ∃! a, action U a s = t
  /-- The carrier has sections locally for the given topology. -/
  locally_nonempty : ∀ U, nonemptySieve carrier U ∈ J U

section Underlying

/-- The native underlying sheaf of sets of an abelian sheaf. -/
abbrev underlyingSetSheaf (L : Sheaf J AddCommGrpCat.{w}) : Sheaf J (Type w) :=
  (sheafCompose J (forget AddCommGrpCat.{w})).obj L

/-- The trivial torsor, with the original regular translation action. -/
abbrev trivialTorsor (L : Sheaf J AddCommGrpCat.{w}) : Torsor L where
  carrier := underlyingSetSheaf L
  action U a t := a + (show L.obj.obj U from t)
  zero_action U t := by
    change (0 : L.obj.obj U) + (show L.obj.obj U from t) = (show L.obj.obj U from t)
    exact zero_add (show L.obj.obj U from t)
  add_action U a b t := by
    change (a + b) + (show L.obj.obj U from t) =
      a + (b + (show L.obj.obj U from t))
    exact add_assoc _ _ _
  naturality f a t := (L.obj.map f).hom.map_add a t
  unique_transport U s t := by
    change (L.obj.obj U : Type w) at s t
    change ∃! a : L.obj.obj U, a + s = t
    exact ⟨t - s, sub_add_cancel _ _, fun a ha => (eq_sub_iff_add_eq).mpr ha⟩
  locally_nonempty U := by
    have h : nonemptySieve (underlyingSetSheaf L) U = ⊤ := by
      ext V f
      exact iff_of_true ⟨(0 : L.obj.obj (op V))⟩ trivial
    rw [h]
    exact J.top_mem U

end Underlying

namespace Torsor

variable {L : Sheaf J AddCommGrpCat.{w}}

/-- The section-level additive action, without assuming a section exists. -/
@[instance_reducible]
def sectionAction (P : Torsor L) (U : Cᵒᵖ) :
    AddAction (L.obj.obj U) (P.carrier.obj.obj U) where
  vadd := P.action U
  add_vadd := P.add_action U
  zero_vadd := P.zero_action U

/-- Pairwise unique transport remains meaningful for empty section sets. -/
theorem sectionAction_unique_transport (P : Torsor L) (U : Cᵒᵖ) :
    letI := P.sectionAction U
    ∀ s t : P.carrier.obj.obj U, ∃! a : L.obj.obj U, a +ᵥ s = t :=
  P.unique_transport U

/-- An existing section gives the original coefficient-to-torsor equivalence. -/
def sectionEquiv (P : Torsor L) (U : Cᵒᵖ) (s : P.carrier.obj.obj U) :
    L.obj.obj U ≃ P.carrier.obj.obj U :=
  Equiv.ofBijective (P.action U · s) ⟨
    fun a _b h => (P.unique_transport U s (P.action U a s)).unique rfl h.symm,
    fun t => (P.unique_transport U s t).exists⟩

/-- Positive displacement from s to t is the existing augmentation difference t minus s. -/
theorem sectionEquiv_symm_eq_difference (P : Torsor L) (U : Cᵒᵖ)
    (s t : P.carrier.obj.obj U) :
    letI := P.sectionAction U
    (P.sectionEquiv U s).symm t =
      AddAction.TorsorAugmentation.difference (P.unique_transport U) t s := by
  let := P.sectionAction U
  exact (AddAction.TorsorAugmentation.difference_eq (P.unique_transport U) t s
    ((P.sectionEquiv U s).symm t) ((P.sectionEquiv U s).apply_symm_apply t)).symm

/-- An equivariant isomorphism uses the actual carrier-sheaf isomorphism. -/
structure Iso (P Q : Torsor L) where
  /-- The isomorphism of the two carrier sheaves. -/
  carrierIso : P.carrier ≅ Q.carrier
  /-- The carrier map preserves the original coefficient action. -/
  equivariant : ∀ U a t,
    carrierIso.hom.hom.app U (P.action U a t) = Q.action U a (carrierIso.hom.hom.app U t)

/-- The identity equivariant carrier isomorphism. -/
def Iso.refl (P : Torsor L) : Iso P P where
  carrierIso := CategoryTheory.Iso.refl P.carrier
  equivariant _ _ _ := rfl

/-- The inverse equivariant carrier isomorphism. -/
def Iso.symm {P Q : Torsor L} (e : Iso P Q) : Iso Q P where
  carrierIso := e.carrierIso.symm
  equivariant U a t := by
    apply (ConcreteCategory.bijective_of_isIso (e.carrierIso.hom.hom.app U)).injective
    rw [e.equivariant]
    have hi (s : Q.carrier.obj.obj U) :
        e.carrierIso.hom.hom.app U (e.carrierIso.inv.hom.app U s) = s :=
      congrArg (fun q : Q.carrier ⟶ Q.carrier => q.hom.app U s) e.carrierIso.inv_hom_id
    exact (hi (Q.action U a t)).trans (congrArg (Q.action U a) (hi t)).symm

/-- Composition of equivariant carrier isomorphisms. -/
def Iso.trans {P Q R : Torsor L} (e : Iso P Q) (d : Iso Q R) : Iso P R where
  carrierIso := e.carrierIso ≪≫ d.carrierIso
  equivariant U a t := by
    change d.carrierIso.hom.hom.app U (e.carrierIso.hom.hom.app U (P.action U a t)) = _
    rw [e.equivariant, d.equivariant]
    rfl

/-- Isomorphism relation on the same actual sheaf torsors. -/
def isomorphicSetoid (L : Sheaf J AddCommGrpCat.{w}) : Setoid (Torsor L) where
  r P Q := Nonempty (Iso P Q)
  iseqv := ⟨fun P => ⟨Iso.refl P⟩,
    fun ⟨e⟩ => ⟨e.symm⟩, fun ⟨e⟩ ⟨d⟩ => ⟨e.trans d⟩⟩

/-- A component of the original terminal sheaf is the native singleton. -/
private theorem terminalSheaf_component_ext (U : Cᵒᵖ)
    (x y : (Topos.terminalSheaf J : Sheaf J (Type w)).obj.obj U) : x = y := by
  change (PUnit : Type w) at x y
  exact Subsingleton.elim x y

/-- The canonical map to the actual terminal sheaf. -/
def toTerminalSheaf (P : Torsor L) : P.carrier ⟶ Topos.terminalSheaf J :=
  (Topos.terminalSheafIsTerminal J).from P.carrier

/-- Original local nonemptiness is local surjectivity of the terminal-sheaf map. -/
theorem toTerminalSheaf_isLocallySurjective (P : Torsor L) :
    Sheaf.IsLocallySurjective P.toTerminalSheaf := by
  constructor
  intro U s
  have h : Presheaf.imageSieve P.toTerminalSheaf.hom s = nonemptySieve P.carrier U := by
    ext V f
    constructor
    · rintro ⟨t, ht⟩
      exact ⟨t⟩
    · rintro ⟨t⟩
      exact ⟨t, terminalSheaf_component_ext (J := J) (op V) _ _⟩
  rw [h]
  exact P.locally_nonempty U

/-- The actual carrier is epimorphic over the terminal sheaf, without enough points. -/
instance toTerminalSheaf_epi (P : Torsor L) : Epi P.toTerminalSheaf := by
  let : Sheaf.IsLocallySurjective P.toTerminalSheaf := P.toTerminalSheaf_isLocallySurjective
  infer_instance

open MonoidalCategory in
/-- The original action and second projection form the native cartesian shear map. -/
def actionPair (P : Torsor L) :
    underlyingSetSheaf L ⊗ P.carrier ⟶ P.carrier ⊗ P.carrier where
  hom.app U := ↾fun x => (P.action U (show L.obj.obj U from x.1) x.2, x.2)
  hom.naturality {U V} f := by
    ext x
    apply Prod.ext
    · change P.action V (L.obj.map f (show L.obj.obj U from x.1))
        (P.carrier.obj.map f x.2) =
          P.carrier.obj.map f (P.action U (show L.obj.obj U from x.1) x.2)
      exact (P.naturality f _ _).symm
    · rfl

/-- Original unique transport makes the actual shear map an isomorphism. -/
instance actionPair_isIso (P : Torsor L) : IsIso P.actionPair := by
  have h (U : Cᵒᵖ) : Function.Bijective (P.actionPair.hom.app U) := by
    constructor
    · rintro ⟨a, s⟩ ⟨b, t⟩ hab
      change (L.obj.obj U : Type w) at a b
      change (P.action U a s, s) = (P.action U b t, t) at hab
      have hst : s = t :=
        congrArg (fun x : P.carrier.obj.obj U × P.carrier.obj.obj U => x.2) hab
      subst t
      apply Prod.ext
      · exact (P.sectionEquiv U s).injective
          (congrArg (fun x : P.carrier.obj.obj U × P.carrier.obj.obj U => x.1) hab)
      · rfl
    · rintro ⟨t, s⟩
      refine ⟨((P.sectionEquiv U s).symm t, s), ?_⟩
      exact Prod.ext ((P.sectionEquiv U s).apply_symm_apply t) rfl
  let (U : Cᵒᵖ) : IsIso (P.actionPair.hom.app U) :=
    (CategoryTheory.isIso_iff_bijective _).mpr (h U)
  let : IsIso ((sheafToPresheaf J (Type w)).map P.actionPair) := by
    change IsIso P.actionPair.hom
    exact NatIso.isIso_of_isIso_app _
  exact isIso_of_reflects_iso P.actionPair (sheafToPresheaf J (Type w))

open MonoidalCategory CartesianMonoidalCategory in
/-- The actual shear retains the original second coordinate. -/
@[reassoc (attr := simp)]
theorem actionPair_snd (P : Torsor L) :
    P.actionPair ≫ snd P.carrier P.carrier = snd (underlyingSetSheaf L) P.carrier := by
  ext U x
  rfl

open MonoidalCategory CartesianMonoidalCategory in
/-- The native isomorphism view of the actual shear keeps its original second projection.
The public global-point producer supplies this proof to the cartesian shear specialization. -/
theorem actionPair_asIso_snd (P : Torsor L) :
    (asIso P.actionPair).hom ≫ snd P.carrier P.carrier =
      snd (underlyingSetSheaf L) P.carrier := by
  rw [asIso_hom]
  exact P.actionPair_snd

open MonoidalCategory CartesianMonoidalCategory in
private theorem actionPair_point_hom_app (P : Torsor L)
    (s : Topos.GlobalPoint P.carrier) (U : Cᵒᵖ) (a : L.obj.obj U) :
    (isoOfShear (Topos.terminalSheafIsTerminal J) (asIso P.actionPair)
      (actionPair_asIso_snd P) s).hom.hom.app U a = P.action U a (s.hom.app U PUnit.unit) := by
  let i : underlyingSetSheaf L ⟶ underlyingSetSheaf L ⊗ P.carrier :=
    lift (𝟙 _) ((Topos.terminalSheafIsTerminal J).from _ ≫ s)
  have hfst : (show L.obj.obj U from (i.hom.app U a).1) = a := by
    exact congrArg (fun q : underlyingSetSheaf L ⟶ underlyingSetSheaf L => q.hom.app U a)
      (lift_fst (𝟙 _) ((Topos.terminalSheafIsTerminal J).from _ ≫ s))
  have hsnd : (i.hom.app U a).2 = s.hom.app U PUnit.unit := by
    have h := congrArg (fun q : underlyingSetSheaf L ⟶ P.carrier => q.hom.app U a)
      (lift_snd (𝟙 _) ((Topos.terminalSheafIsTerminal J).from _ ≫ s))
    change (i.hom.app U a).2 =
      s.hom.app U (((Topos.terminalSheafIsTerminal J).from (underlyingSetSheaf L)).hom.app U a)
        at h
    exact h.trans (congrArg (s.hom.app U)
      (terminalSheaf_component_ext (J := J) U _ PUnit.unit))
  rw [isoOfShear_hom, asIso_hom]
  change P.action U (show L.obj.obj U from (i.hom.app U a).1) (i.hom.app U a).2 = _
  rw [hfst, hsnd]

/-- An actual global point specializes the existing categorical shear isomorphism. -/
def trivializationOfGlobalPoint (P : Torsor L) (s : Topos.GlobalPoint P.carrier) :
    Iso (trivialTorsor L) P where
  carrierIso := by
    change underlyingSetSheaf L ≅ P.carrier
    exact CartesianMonoidalCategory.isoOfShear (Topos.terminalSheafIsTerminal J)
      (asIso P.actionPair) (actionPair_asIso_snd P) s
  equivariant U a t := by
    change (L.obj.obj U : Type w) at t
    have hsum := actionPair_point_hom_app P s U (a + t)
    have ht := actionPair_point_hom_app P s U t
    exact hsum.trans ((P.add_action U a t (s.hom.app U PUnit.unit)).trans
      (congrArg (P.action U a) ht.symm))

/-- The categorical specialization has exactly the original action component. -/
@[simp]
theorem trivializationOfGlobalPoint_hom_app (P : Torsor L)
    (s : Topos.GlobalPoint P.carrier) (U : Cᵒᵖ) (a : L.obj.obj U) :
    (P.trivializationOfGlobalPoint s).carrierIso.hom.hom.app U a =
      P.action U a ((Topos.globalPointSectionsEquiv P.carrier s).val U) :=
  actionPair_point_hom_app P s U a

/-- The categorical inverse is the original unique transport from the given point. -/
@[simp]
theorem trivializationOfGlobalPoint_inv_app (P : Torsor L)
    (s : Topos.GlobalPoint P.carrier) (U : Cᵒᵖ) (t : P.carrier.obj.obj U) :
    (show L.obj.obj U from (P.trivializationOfGlobalPoint s).carrierIso.inv.hom.app U t) =
      (P.sectionEquiv U ((Topos.globalPointSectionsEquiv P.carrier s).val U)).symm t := by
  apply (P.sectionEquiv U ((Topos.globalPointSectionsEquiv P.carrier s).val U)).injective
  have h := congrArg (fun q : P.carrier ⟶ P.carrier => q.hom.app U t)
    (P.trivializationOfGlobalPoint s).carrierIso.inv_hom_id
  change (P.trivializationOfGlobalPoint s).carrierIso.hom.hom.app U
    ((P.trivializationOfGlobalPoint s).carrierIso.inv.hom.app U t) = t at h
  have he := trivializationOfGlobalPoint_hom_app P s U
    (show L.obj.obj U from (P.trivializationOfGlobalPoint s).carrierIso.inv.hom.app U t)
  exact he.symm.trans (h.trans ((P.sectionEquiv U
    ((Topos.globalPointSectionsEquiv P.carrier s).val U)).apply_symm_apply t).symm)

/-- The inverse retains the original positive displacement, with no new inverse choice. -/
theorem trivializationOfGlobalPoint_inv_app_eq_difference (P : Torsor L)
    (s : Topos.GlobalPoint P.carrier) (U : Cᵒᵖ) (t : P.carrier.obj.obj U) :
    letI := P.sectionAction U
    (show L.obj.obj U from (P.trivializationOfGlobalPoint s).carrierIso.inv.hom.app U t) =
      AddAction.TorsorAugmentation.difference (P.unique_transport U) t
        ((Topos.globalPointSectionsEquiv P.carrier s).val U) := by
  let := P.sectionAction U
  rw [trivializationOfGlobalPoint_inv_app]
  exact P.sectionEquiv_symm_eq_difference U _ _

/-- Torsor triviality is an intrinsic global-point statement in the actual sheaf topos. -/
theorem nonempty_globalPoints_iff_trivial (P : Torsor L) :
    Nonempty (Topos.GlobalPoint P.carrier) ↔ Nonempty (Iso (trivialTorsor L) P) := by
  constructor
  · rintro ⟨s⟩
    exact ⟨P.trivializationOfGlobalPoint s⟩
  · rintro ⟨e⟩
    refine ⟨{ hom := ?_ }⟩
    refine {
      app U := ↾fun _ => e.carrierIso.hom.hom.app U (0 : L.obj.obj U)
      naturality := ?_ }
    intro U V f
    ext x
    change e.carrierIso.hom.hom.app V (0 : L.obj.obj V) =
      P.carrier.obj.map f (e.carrierIso.hom.hom.app U (0 : L.obj.obj U))
    have h := congrArg (fun k => k (0 : L.obj.obj U))
      (e.carrierIso.hom.hom.naturality f)
    change e.carrierIso.hom.hom.app V (L.obj.map f (0 : L.obj.obj U)) =
      P.carrier.obj.map f (e.carrierIso.hom.hom.app U (0 : L.obj.obj U)) at h
    simpa only [map_zero] using h

section Terminal

variable {T : C}

/-- Restrict a section at the specified terminal object to a test object. -/
def restrictGlobalSection (P : Torsor L) (hT : IsTerminal T)
    (s : P.carrier.obj.obj (op T)) (U : Cᵒᵖ) : P.carrier.obj.obj U :=
  P.carrier.obj.map (hT.from U.unop).op s

/-- The original restriction of a terminal-object section is natural. -/
theorem restrictGlobalSection_naturality (P : Torsor L) (hT : IsTerminal T)
    (s : P.carrier.obj.obj (op T)) {U V : Cᵒᵖ} (f : U ⟶ V) :
    P.carrier.obj.map f (P.restrictGlobalSection hT s U) =
      P.restrictGlobalSection hT s V := by
  have h : (hT.from U.unop).op ≫ f = (hT.from V.unop).op :=
    congrArg Quiver.Hom.op (hT.hom_ext _ _)
  change P.carrier.obj.map f (P.carrier.obj.map (hT.from U.unop).op s) = _
  rw [← Functor.map_comp_apply, h]
  rfl

/-- A genuine terminal-object section gives the original equivariant trivialization. -/
abbrev trivializationOfSection (P : Torsor L) (hT : IsTerminal T)
    (s : P.carrier.obj.obj (op T)) : Iso (trivialTorsor L) P :=
  P.trivializationOfGlobalPoint ((Topos.globalPointTerminalEquiv hT P.carrier).symm s)

/-- The specialized global point has exactly the original terminal-section restrictions. -/
@[simp]
theorem trivializationOfSection_point_restrict (P : Torsor L) (hT : IsTerminal T)
    (s : P.carrier.obj.obj (op T)) (U : Cᵒᵖ) :
    (Topos.globalPointSectionsEquiv P.carrier
      ((Topos.globalPointTerminalEquiv hT P.carrier).symm s)).val U =
        P.restrictGlobalSection hT s U := rfl

/-- The historical constructor keeps the literal original action component. -/
@[simp]
theorem trivializationOfSection_hom_app (P : Torsor L) (hT : IsTerminal T)
    (s : P.carrier.obj.obj (op T)) (U : Cᵒᵖ) (a : L.obj.obj U) :
    (P.trivializationOfSection hT s).carrierIso.hom.hom.app U a =
      P.action U a (P.restrictGlobalSection hT s U) :=
  P.trivializationOfGlobalPoint_hom_app ((Topos.globalPointTerminalEquiv hT P.carrier).symm s) U a

/-- The historical inverse keeps the original positive displacement component. -/
@[simp]
theorem trivializationOfSection_inv_app (P : Torsor L) (hT : IsTerminal T)
    (s : P.carrier.obj.obj (op T)) (U : Cᵒᵖ) (t : P.carrier.obj.obj U) :
    (show L.obj.obj U from (P.trivializationOfSection hT s).carrierIso.inv.hom.app U t) =
      (P.sectionEquiv U (P.restrictGlobalSection hT s U)).symm t :=
  P.trivializationOfGlobalPoint_inv_app ((Topos.globalPointTerminalEquiv hT P.carrier).symm s) U t

/-- A terminal-object section exists exactly when the torsor is equivariantly trivial. -/
theorem nonempty_globalSections_iff_trivial (P : Torsor L) (hT : IsTerminal T) :
    Nonempty (P.carrier.obj.obj (op T)) ↔ Nonempty (Iso (trivialTorsor L) P) := by
  constructor
  · rintro ⟨s⟩
    exact P.nonempty_globalPoints_iff_trivial.mp
      ⟨(Topos.globalPointTerminalEquiv hT P.carrier).symm s⟩
  · intro h
    obtain ⟨s⟩ := P.nonempty_globalPoints_iff_trivial.mpr h
    exact ⟨Topos.globalPointTerminalEquiv hT P.carrier s⟩

end Terminal
end Torsor

/-- Isomorphism classes of the same actual torsors, without an imposed group law or Ext model. -/
def TorsorClass (L : Sheaf J AddCommGrpCat.{w}) :=
  _root_.Quotient (Torsor.isomorphicSetoid L)

end CategoryTheory.Sheaf
