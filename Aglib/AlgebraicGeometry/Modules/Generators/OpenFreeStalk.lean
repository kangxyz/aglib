/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.Modules.Generators.OpenFreeFunctor
/-!
# Naturality of the actual open-free stalk isomorphisms

The existing `openFreeStalkIso` is natural in the open, with target the free
stalk module on point membership. `openFreeStalk_map_isIso` detects when an
open inclusion induces an isomorphism of these original module stalks.
-/
@[expose] public section


noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
universe w v v' v'' u u' u''
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry TopologicalSpace Opposite
namespace AlgebraicGeometry.Scheme.Modules

lemma corepresentable_uniqueUpToIso_homEquiv {C : Type*} [Category C]
    {F : C ⥤ Type*} {A B N : C} (e : F.CorepresentableBy A)
    (e' : F.CorepresentableBy B) (p : B ⟶ N) :
    e.homEquiv ((e.uniqueUpToIso e').hom ≫ p) = e'.homEquiv p := by
  change e.homEquiv (e.homEquiv.symm (e'.homEquiv (𝟙 B)) ≫ p) = _
  rw [Functor.CorepresentableBy.homEquiv_comp, Equiv.apply_symm_apply,
    ← Functor.CorepresentableBy.homEquiv_comp, Category.id_comp]

lemma openFreeStalkCorepresentable_naturality (X : Scheme.{u}) (x : X)
    {U V : X.Opens} (h : U ⟶ V) (N : ModuleCat.{u} (X.presheaf.stalk x))
    (p : (moduleStalk X x).obj (openFree X V) ⟶ N) (hx : PLift (x ∈ U)) :
    (openFreeStalkCorepresentable X x U).homEquiv
      ((moduleStalk X x).map ((openFreeFunctor X).map h) ≫ p) hx =
    (openFreeStalkCorepresentable X x V).homEquiv p ⟨h.le hx.down⟩ := by
  dsimp [openFreeStalkCorepresentable]
  erw [Adjunction.homEquiv_naturality_left, openFreeHomEquiv_naturality_open]
  rfl

/-- The covariant functor of opens whose value is the lifted type of witnesses that `x` belongs to
the open, with maps induced by inclusions. -/
def pointMembershipFunctor (X : Scheme.{u}) (x : X) : X.Opens ⥤ Type u where
  obj U := ULift.{u} (PLift (x ∈ U))
  map h := ↾fun hx => ⟨⟨h.le hx.down.down⟩⟩

/-- The covariant functor assigning to each open the free module over the stalk ring at `x` on its
lifted point-membership type. -/
def pointOpenFreeFunctor (X : Scheme.{u}) (x : X) :
    X.Opens ⥤ ModuleCat.{u} (X.presheaf.stalk x) :=
  pointMembershipFunctor X x ⋙ ModuleCat.free (X.presheaf.stalk x)

lemma openFreeStalkIso_naturality (X : Scheme.{u}) (x : X)
    {U V : X.Opens} (h : U ⟶ V) :
    (moduleStalk X x).map ((openFreeFunctor X).map h) ≫ (openFreeStalkIso X x V).hom =
      (openFreeStalkIso X x U).hom ≫ (pointOpenFreeFunctor X x).map h := by
  apply (openFreeStalkCorepresentable X x U).homEquiv.injective
  funext hx
  rw [openFreeStalkCorepresentable_naturality]
  change ((openFreeStalkCorepresentable X x V).homEquiv
    ((openFreeStalkIso X x V).hom ≫ 𝟙 _)) _ = _
  rw [show (openFreeStalkIso X x V).hom =
    ((openFreeStalkCorepresentable X x V).uniqueUpToIso
      (freePointOpenCorepresentable X x V)).hom from rfl,
    corepresentable_uniqueUpToIso_homEquiv]
  rw [show (openFreeStalkIso X x U).hom =
    ((openFreeStalkCorepresentable X x U).uniqueUpToIso
      (freePointOpenCorepresentable X x U)).hom from rfl,
    corepresentable_uniqueUpToIso_homEquiv]
  change ModuleCat.freeMk ⟨⟨h.le hx.down⟩⟩ =
    (ModuleCat.free (X.presheaf.stalk x)).map ((pointMembershipFunctor X x).map h)
      (ModuleCat.freeMk ⟨hx⟩)
  rw [ModuleCat.free_map_apply]
  rfl

/-- The natural isomorphism identifying stalks of open-free module sheaves with free stalk modules
on point membership. -/
def openFreeStalkNatIso (X : Scheme.{u}) (x : X) :
    openFreeFunctor X ⋙ moduleStalk X x ≅ pointOpenFreeFunctor X x :=
  NatIso.ofComponents (openFreeStalkIso X x) (fun h => openFreeStalkIso_naturality X x h)

lemma openFreeStalk_map_isIso (X : Scheme.{u}) (x : X) {U V : X.Opens}
    (h : U ⟶ V) (hx : x ∈ V → x ∈ U) :
    IsIso ((moduleStalk X x).map ((openFreeFunctor X).map h)) := by
  have : IsIso ((pointMembershipFunctor X x).map h) := by
    apply (CategoryTheory.isIso_iff_bijective _).mpr
    change Function.Bijective (fun hu : ULift.{u} (PLift (x ∈ U)) =>
      (⟨⟨h.le hu.down.down⟩⟩ : ULift.{u} (PLift (x ∈ V))))
    refine ⟨fun _ _ _ => Subsingleton.elim _ _, ?_⟩
    intro hv
    exact ⟨⟨⟨hx hv.down.down⟩⟩, Subsingleton.elim _ _⟩
  have : IsIso ((pointOpenFreeFunctor X x).map h) := by
    change IsIso ((ModuleCat.free (X.presheaf.stalk x)).map _)
    infer_instance
  rw [← isIso_comp_right_iff _ (openFreeStalkIso X x V).hom,
    openFreeStalkIso_naturality]
  infer_instance

end AlgebraicGeometry.Scheme.Modules
