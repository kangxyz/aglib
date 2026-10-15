/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.Modules.Stalk.Basic
public import Mathlib.Algebra.Category.ModuleCat.Presheaf.Generator
public import Mathlib.Algebra.Category.ModuleCat.Products
public import Mathlib.RingTheory.Flat.Basic
/-!
# Actual flat generators for scheme module sheaves

Sheafifying the free module presheaf on an open representable gives the
extension-by-zero free generator on that open. Its actual module stalk is free
on the proposition that the point belongs to the open. These objects will
supply flat epimorphic covers without quasicoherence or a resolution hypothesis.
-/
@[expose] public section


noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
universe u
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry TopologicalSpace Opposite
namespace AlgebraicGeometry.Scheme.Modules

/-- The actual sheafification of the free module presheaf on an open representable. -/
def openFree (X : Scheme.{u}) (U : X.Opens) : X.Modules :=
  (_root_.PresheafOfModules.sheafification (𝟙 X.ringCatSheaf.obj)).obj
    ((_root_.PresheafOfModules.free X.ringCatSheaf.obj).obj (yoneda.obj U))

/-- An open free generator represents sections on that open. -/
def openFreeHomEquiv (X : Scheme.{u}) (U : X.Opens) (M : X.Modules) :
    (openFree X U ⟶ M) ≃ Γ(M, U) :=
  ((_root_.PresheafOfModules.sheafificationAdjunction (𝟙 X.ringCatSheaf.obj)).homEquiv _ _).trans
    _root_.PresheafOfModules.freeYonedaEquiv

/-- Naturality of the represented sections. -/
theorem openFreeHomEquiv_comp (X : Scheme.{u}) (U : X.Opens) {M N : X.Modules}
    (p : openFree X U ⟶ M) (q : M ⟶ N) :
    openFreeHomEquiv X U N (p ≫ q) = q.app U (openFreeHomEquiv X U M p) := by
  dsimp [openFreeHomEquiv]
  erw [Adjunction.homEquiv_naturality_right]
  rfl

/-- The functor of stalk-module-valued sections on open membership. -/
def pointOpenSections (X : Scheme.{u}) (x : X) (U : X.Opens) :
    ModuleCat.{u} (X.presheaf.stalk x) ⥤ Type u where
  obj N := PLift (x ∈ U) → N
  map p := ↾fun s hx => p (s hx)

/-- Stalks of the actual open free sheaf represent the expected membership functor. -/
def openFreeStalkCorepresentable (X : Scheme.{u}) (x : X) (U : X.Opens) :
    (pointOpenSections X x U).CorepresentableBy ((moduleStalk X x).obj (openFree X U)) where
  homEquiv := ((moduleStalkSkyscraperAdjunction X x).homEquiv _ _).trans
    (openFreeHomEquiv X U _)
  homEquiv_comp p q := by
    dsimp
    erw [Adjunction.homEquiv_naturality_right, openFreeHomEquiv_comp]

/-- The genuinely free stalk module has the same representing property. -/
def freePointOpenCorepresentable (X : Scheme.{u}) (x : X) (U : X.Opens) :
    (pointOpenSections X x U).CorepresentableBy
      ((ModuleCat.free (X.presheaf.stalk x)).obj (ULift.{u} (PLift (x ∈ U)))) where
  homEquiv :=
    { toFun := fun p hx => p (ModuleCat.freeMk ⟨hx⟩)
      invFun := fun s => ModuleCat.freeDesc (↾fun hx => s hx.down)
      left_inv := by intro p; ext hx; simp
      right_inv := by intro s; funext hx; simp }
  homEquiv_comp _ _ := rfl

/-- An actual open generator has a free module stalk, with rank one on the open
and rank zero off it. -/
def openFreeStalkIso (X : Scheme.{u}) (x : X) (U : X.Opens) :
    (moduleStalk X x).obj (openFree X U) ≅
      (ModuleCat.free (X.presheaf.stalk x)).obj (ULift.{u} (PLift (x ∈ U))) :=
  (openFreeStalkCorepresentable X x U).uniqueUpToIso (freePointOpenCorepresentable X x U)

/-- Flatness is proved on the actual stalk, not assumed as generator data. -/
instance openFree_stalk_flat (X : Scheme.{u}) (x : X) (U : X.Opens) :
    Module.Flat (X.presheaf.stalk x) ((moduleStalk X x).obj (openFree X U)) := by
  let : Module.Flat (X.presheaf.stalk x)
      ((ModuleCat.free (X.presheaf.stalk x)).obj (ULift.{u} (PLift (x ∈ U)))) :=
    inferInstanceAs (Module.Flat (X.presheaf.stalk x)
      (ULift.{u} (PLift (x ∈ U)) →₀ X.presheaf.stalk x))
  exact Module.Flat.of_linearEquiv ((openFreeStalkIso X x U).toLinearEquiv)

/-- Stalkwise flatness for the actual sheaf module stalks. -/
def stalkwiseFlat (X : Scheme.{u}) : ObjectProperty X.Modules :=
  fun M => ∀ x, Module.Flat (X.presheaf.stalk x) ((moduleStalk X x).obj M)

/-- Coproducts of genuinely stalkwise-flat sheaves are stalkwise flat. -/
theorem stalkwiseFlat_coproduct (X : Scheme.{u}) {I : Type u} (M : I → X.Modules)
    (hM : ∀ i, stalkwiseFlat X (M i)) : stalkwiseFlat X (∐ M) := by
  classical
  intro x
  let (i : I) : Module.Flat (X.presheaf.stalk x) ((moduleStalk X x).obj (M i)) := hM i x
  exact Module.Flat.of_linearEquiv
    ((PreservesCoproduct.iso (moduleStalk X x) M) ≪≫
      ModuleCat.coprodIsoDirectSum (fun i => (moduleStalk X x).obj (M i))).toLinearEquiv

/-- The index set of all actual local sections of a module sheaf. -/
def localSectionIndex {X : Scheme.{u}} (M : X.Modules) := Σ U : X.Opens, Γ(M, U)

/-- An explicit coproduct of open free generators covering a module sheaf. -/
def flatCover {X : Scheme.{u}} (M : X.Modules) : X.Modules :=
  ∐ (fun s : localSectionIndex M => openFree X s.1)

/-- Each local section determines the corresponding component of the cover map. -/
def flatCoverπ {X : Scheme.{u}} (M : X.Modules) : flatCover M ⟶ M :=
  Sigma.desc (fun s : localSectionIndex M => (openFreeHomEquiv X s.1 M).symm s.2)

/-- The explicit cover has flat actual module stalks. -/
theorem flatCover_stalkwiseFlat {X : Scheme.{u}} (M : X.Modules) :
    stalkwiseFlat X (flatCover M) :=
  stalkwiseFlat_coproduct X _ (fun s x => openFree_stalk_flat X x s.1)

/-- The cover map is epic because every actual local section occurs as a generator. -/
instance flatCoverπ_epi {X : Scheme.{u}} (M : X.Modules) : Epi (flatCoverπ M) where
  left_cancellation p q h := by
    ext U s
    have e := congrArg (fun f => Sigma.ι (fun t : localSectionIndex M => openFree X t.1)
      (⟨U, s⟩ : localSectionIndex M) ≫ f) h
    dsimp [flatCoverπ] at e
    simp only [Sigma.ι_comp_desc_assoc] at e
    have he := congrArg (openFreeHomEquiv X U _) e
    simpa only [openFreeHomEquiv_comp, Equiv.apply_symm_apply] using he

/-- Every module sheaf has a proved epimorphic cover with flat actual stalks. -/
theorem exists_stalkwiseFlat_epi (X : Scheme.{u}) (M : X.Modules) :
    ∃ (F : X.Modules) (p : F ⟶ M), stalkwiseFlat X F ∧ Epi p :=
  ⟨flatCover M, flatCoverπ M, flatCover_stalkwiseFlat M, inferInstance⟩

end AlgebraicGeometry.Scheme.Modules
