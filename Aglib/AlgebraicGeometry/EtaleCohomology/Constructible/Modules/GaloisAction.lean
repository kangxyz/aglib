/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.EtaleCohomology.Constructible.Modules.ConnectedTorsionSections
public import Aglib.AlgebraicGeometry.EtaleCohomology.Constructible.Modules.EtaleRestriction
public import Aglib.AlgebraicGeometry.Morphisms.FiniteEtale.GaloisInstances
public import Mathlib.RepresentationTheory.Rep.Basic

/-! # Actual deck action on an original torsion module value

Restriction of a native module sheaf along inverse deck automorphisms gives an
R-linear left action on its original sections over the cover. A supplied actual
constant trivialization on a connected qcqs cover transports that action onto
the literal original torsion module value, without any finite underlying-set
assumption. For a Galois finite-etale cover the native deck group is finite.
This construction does not assert effective descent or descend submodules.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite

namespace AlgebraicGeometry.Scheme.EtaleCohomology.Constructible.Modules

universe u r

attribute [local instance] hasSheafifyLarge ModuleCat.Sheaf.hasSheafify

variable {R : Type r} [CommRing R] {X : Scheme.{u}}

/-- The original module of sections on the actual finite-etale object. -/
abbrev finiteEtaleSections (F : ModuleSheaf R X) (Y : Scheme.FiniteEtale X) :
    ModuleCat.{u + 1} R :=
  F.obj.obj (op ((Scheme.FiniteEtale.toEtale X).obj Y))

/-- Contravariant restriction along inverse deck maps is an actual R-linear left action. -/
def finiteEtaleSectionsRepresentation (F : ModuleSheaf R X) (Y : Scheme.FiniteEtale X) :
    Representation R (Aut Y) (finiteEtaleSections F Y) where
  toFun σ := (F.obj.map ((Scheme.FiniteEtale.toEtale X).map σ.inv).op).hom
  map_one' := by
    change (F.obj.map ((Scheme.FiniteEtale.toEtale X).map (𝟙 Y)).op).hom = _
    rw [CategoryTheory.Functor.map_id, op_id, CategoryTheory.Functor.map_id]
    rfl
  map_mul' σ τ := by
    change (F.obj.map ((Scheme.FiniteEtale.toEtale X).map (σ.inv ≫ τ.inv)).op).hom = _
    rw [Functor.map_comp, op_comp, Functor.map_comp]
    rfl

/-- The action is literally the original sheaf restriction, with inverse orientation. -/
@[simp]
theorem finiteEtaleSectionsRepresentation_apply (F : ModuleSheaf R X)
    (Y : Scheme.FiniteEtale X) (σ : Aut Y) (s : finiteEtaleSections F Y) :
    finiteEtaleSectionsRepresentation F Y σ s =
      F.obj.map ((Scheme.FiniteEtale.toEtale X).map σ.inv).op s := rfl

/-- Postcomposing the original terminal test scheme returns the original cover object. -/
def finiteEtalePostcomposeTerminalIso (Y : Scheme.FiniteEtale X) :
    (siteEtalePostcompose Y.obj.hom).obj (etaleTerminal Y.obj.left) ≅
      (Scheme.FiniteEtale.toEtale X).obj Y :=
  MorphismProperty.Over.isoMk (Iso.refl Y.obj.left) (by rfl)

/-- Actual constant trivialization identifies the literal torsion value with the
original module of sections on the cover. -/
def trivializedFiniteEtaleSectionsIso (F : ModuleSheaf R X) (Y : Scheme.FiniteEtale X)
    [ConnectedSpace Y.obj.left] [CompactSpace Y.obj.left] [QuasiSeparatedSpace Y.obj.left]
    (M : ModuleCat.{u + 1} R) (hM : IsAddTorsion M)
    (e : (moduleInverseImage R Y.obj.hom).obj F ≅
      (constantSheaf Y.obj.left.smallEtaleTopology (ModuleCat.{u + 1} R)).obj M) :
    M ≅ finiteEtaleSections F Y :=
  moduleConstantSectionsIso R Y.obj.left M hM ≪≫
    (moduleGlobalSections R Y.obj.left).mapIso
      (e.symm ≪≫ (moduleInverseImageEtaleIso R Y.obj.hom).app F) ≪≫
    (F.obj.mapIso (finiteEtalePostcomposeTerminalIso Y).op).symm

/-- The native deck action transported onto the literal supplied module M. -/
def trivializedDeckRepresentation (F : ModuleSheaf R X) (Y : Scheme.FiniteEtale X)
    [ConnectedSpace Y.obj.left] [CompactSpace Y.obj.left] [QuasiSeparatedSpace Y.obj.left]
    (M : ModuleCat.{u + 1} R) (hM : IsAddTorsion M)
    (e : (moduleInverseImage R Y.obj.hom).obj F ≅
      (constantSheaf Y.obj.left.smallEtaleTopology (ModuleCat.{u + 1} R)).obj M) :
    Representation R (Aut Y) M :=
  ((trivializedFiniteEtaleSectionsIso F Y M hM e).toLinearEquiv.symm.conjRingEquiv.toMonoidHom).comp
    (finiteEtaleSectionsRepresentation F Y)

/-- Transport intertwines the literal M-action with the actual original restriction map. -/
theorem trivializedDeckRepresentation_restriction (F : ModuleSheaf R X)
    (Y : Scheme.FiniteEtale X)
    [ConnectedSpace Y.obj.left] [CompactSpace Y.obj.left] [QuasiSeparatedSpace Y.obj.left]
    (M : ModuleCat.{u + 1} R) (hM : IsAddTorsion M)
    (e : (moduleInverseImage R Y.obj.hom).obj F ≅
      (constantSheaf Y.obj.left.smallEtaleTopology (ModuleCat.{u + 1} R)).obj M)
    (σ : Aut Y) (m : M) :
    (trivializedFiniteEtaleSectionsIso F Y M hM e).hom
        (trivializedDeckRepresentation F Y M hM e σ m) =
      F.obj.map ((Scheme.FiniteEtale.toEtale X).map σ.inv).op
        ((trivializedFiniteEtaleSectionsIso F Y M hM e).hom m) := by
  let i := (trivializedFiniteEtaleSectionsIso F Y M hM e).toLinearEquiv
  change i (i.symm ((finiteEtaleSectionsRepresentation F Y σ) (i m))) = _
  exact i.apply_symm_apply _

/-- A nonzero annihilating natural number gives torsion, not a finite underlying group. -/
theorem moduleIsAddTorsion_of_nsmul_eq_zero (M : ModuleCat.{u + 1} R)
    (n : ℕ) (hn : 0 < n) (hM : ∀ m : M, n • m = 0) : IsAddTorsion M :=
  fun m => isOfFinAddOrder_iff_nsmul_eq_zero.mpr ⟨n, hn, hM m⟩

/-- An actual n-killed coefficient gives a bundled representation on literal M. -/
abbrev killedTrivializedDeckRep (F : ModuleSheaf R X) (Y : Scheme.FiniteEtale X)
    [ConnectedSpace Y.obj.left] [CompactSpace Y.obj.left] [QuasiSeparatedSpace Y.obj.left]
    (M : ModuleCat.{u + 1} R) (n : ℕ) (hn : 0 < n) (hM : ∀ m : M, n • m = 0)
    (e : (moduleInverseImage R Y.obj.hom).obj F ≅
      (constantSheaf Y.obj.left.smallEtaleTopology (ModuleCat.{u + 1} R)).obj M) :
    Rep.{u + 1} R (Aut Y) :=
  Rep.of (trivializedDeckRepresentation F Y M
    (moduleIsAddTorsion_of_nsmul_eq_zero M n hn hM) e)

/-- The deck group of the actual native Galois cover is finite. -/
theorem finite_galoisDeckGroup [ConnectedSpace X] (Y : Scheme.FiniteEtale X)
    [PreGaloisCategory.IsGalois Y] : Finite (Aut Y) := inferInstance

end AlgebraicGeometry.Scheme.EtaleCohomology.Constructible.Modules
