/-
Copyright (c) 2026 kangxyz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.Algebra.Category.ModuleCat.ChangeOfRings.Coinduction
public import Mathlib.Algebra.Category.ModuleCat.Projective
public import Mathlib.Algebra.Homology.DerivedCategory.Ext.MapAdjunction
public import Mathlib.Algebra.Homology.DerivedCategory.Ext.Linear

/-!
# Exact coinduction for a projective algebra

Projectivity of the target ring as the original restricted source module
makes native scalar coinduction preserve epimorphisms and hence finite
colimits. The original restriction--coinduction adjunction then compares
Ext for arbitrary source and coefficient modules. Its unit, counit and
source-multiplication formulas remain the native ones.

No finiteness, locality, dimension or duality hypothesis is imposed. The
ring universes and Ext sizes remain independent; the common module universe
for the adjunction is the one already required by native coinduction.
-/

@[expose] public section

noncomputable section

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open CategoryTheory CategoryTheory.Limits CategoryTheory.Abelian

universe u v w eR eA

namespace ModuleCat

section Exactness

variable {R : Type u} {A : Type v} [Ring R] [Ring A] (σ : R →+* A)

/-- Projective lifting of the actual R-linear functionals makes original
scalar coinduction preserve epimorphisms. -/
instance coextendScalars_preservesEpimorphisms_of_projective
    [Module.Projective R ((restrictScalars σ).obj (ModuleCat.of A A))] :
    (coextendScalars.{u, v, w} σ).PreservesEpimorphisms where
  preserves {M N} f := by
    intro hf
    apply (ModuleCat.epi_iff_surjective _).mpr
    intro x
    obtain ⟨y, hy⟩ := Module.projective_lifting_property f.hom
      (CoextendScalars.equiv σ N x) ((ModuleCat.epi_iff_surjective f).mp inferInstance)
    refine ⟨(CoextendScalars.equiv σ M).symm y, ?_⟩
    apply (CoextendScalars.equiv σ N).injective
    exact hy

/-- Native coinduction is exact when the original restricted regular module
is projective. Kernel preservation is inherited from its original right adjoint. -/
instance coextendScalars_preservesHomology_of_projective
    [Module.Projective R ((restrictScalars σ).obj (ModuleCat.of A A))] :
    (coextendScalars.{u, v, max v w} σ).PreservesHomology := by
  exact Functor.preservesHomology_of_preservesEpis_and_kernels _

/-- The actual coinduction functor preserves finite colimits under projectivity
of the original restricted regular module. -/
instance coextendScalars_preservesFiniteColimits_of_projective
    [Module.Projective R ((restrictScalars σ).obj (ModuleCat.of A A))] :
    PreservesFiniteColimits (coextendScalars.{u, v, max v w} σ) := by
  exact Functor.preservesFiniteColimits_of_preservesHomology _

/-- Original short exact rows remain short exact under native projective coinduction. -/
theorem coextendScalars_map_shortExact_of_projective
    [Module.Projective R ((restrictScalars σ).obj (ModuleCat.of A A))]
    (T : ShortComplex (ModuleCat.{max v w} R)) (hT : T.ShortExact) :
    (T.map (coextendScalars σ)).ShortExact :=
  hT.map_of_exact (coextendScalars σ)

end Exactness

section Ext

variable {R : Type u} {A : Type v} [CommRing R] [CommRing A] (σ : R →+* A)
  [Module.Projective R ((restrictScalars σ).obj (ModuleCat.of A A))]
  [HasExt.{eR} (ModuleCat.{max v w} R)] [HasExt.{eA} (ModuleCat.{max v w} A)]

/-- The original exact restriction--coinduction adjunction on native Ext.
The source module and coefficient are arbitrary. -/
def coextendScalarsExtEquiv (M : ModuleCat.{max v w} A)
    (N : ModuleCat.{max v w} R) (q : ℕ) :
    Ext.{eR} ((restrictScalars σ).obj M) N q ≃+
      Ext.{eA} M ((coextendScalars σ).obj N) q :=
  (restrictCoextendScalarsAdj.{w, u, v} σ).extEquiv

/-- The forward Ext map is the original exact coinduction followed by the
original adjunction unit on its source. -/
theorem coextendScalarsExtEquiv_apply (M : ModuleCat.{max v w} A)
    (N : ModuleCat.{max v w} R) (q : ℕ)
    (x : Ext.{eR} ((restrictScalars σ).obj M) N q) :
    coextendScalarsExtEquiv σ M N q x =
      (Ext.mk₀ ((restrictCoextendScalarsAdj.{w, u, v} σ).unit.app M)).comp
        (x.mapExactFunctor (coextendScalars σ)) (zero_add q) := rfl

/-- The inverse Ext map is original restriction followed by the actual counit. -/
theorem coextendScalarsExtEquiv_symm_apply (M : ModuleCat.{max v w} A)
    (N : ModuleCat.{max v w} R) (q : ℕ)
    (x : Ext.{eA} M ((coextendScalars σ).obj N) q) :
    (coextendScalarsExtEquiv σ M N q).symm x =
      (x.mapExactFunctor (restrictScalars σ)).comp
        (Ext.mk₀ ((restrictCoextendScalarsAdj.{w, u, v} σ).counit.app N)) (add_zero q) := rfl

/-- Multiplication by an actual target-ring scalar on the source corresponds
to the intrinsic target-ring scalar action on the coinduced Ext group. -/
theorem coextendScalarsExtEquiv_source_smul (M : ModuleCat.{max v w} A)
    (N : ModuleCat.{max v w} R) (q : ℕ) (a : A)
    (x : Ext.{eR} ((restrictScalars σ).obj M) N q) :
    coextendScalarsExtEquiv σ M N q
        ((Ext.mk₀ ((restrictScalars σ).map (a • 𝟙 M))).comp x (zero_add q)) =
      a • coextendScalarsExtEquiv σ M N q x := by
  simpa only [coextendScalarsExtEquiv, Ext.mk₀_smul, Ext.smul_comp, Ext.mk₀_id_comp] using
    (restrictCoextendScalarsAdj.{w, u, v} σ).extEquiv_naturality_left₀ (a • 𝟙 M) x

/-- The inverse comparison retains the same original source-multiplication action. -/
theorem coextendScalarsExtEquiv_symm_smul (M : ModuleCat.{max v w} A)
    (N : ModuleCat.{max v w} R) (q : ℕ) (a : A)
    (x : Ext.{eA} M ((coextendScalars σ).obj N) q) :
    (coextendScalarsExtEquiv σ M N q).symm (a • x) =
      (Ext.mk₀ ((restrictScalars σ).map (a • 𝟙 M))).comp
        ((coextendScalarsExtEquiv σ M N q).symm x) (zero_add q) := by
  simpa only [coextendScalarsExtEquiv, Ext.mk₀_smul, Ext.smul_comp, Ext.mk₀_id_comp] using
    (restrictCoextendScalarsAdj.{w, u, v} σ).extEquiv_symm_naturality_left₀ (a • 𝟙 M) x

/-- In degree zero, the Ext comparison is literally the original Hom adjunction. -/
@[simp]
theorem coextendScalarsExtEquiv_mk₀ (M : ModuleCat.{max v w} A)
    (N : ModuleCat.{max v w} R) (h : (restrictScalars σ).obj M ⟶ N) :
    coextendScalarsExtEquiv σ M N 0 (Ext.mk₀ h) =
      Ext.mk₀ (RestrictionCoextensionAdj.HomEquiv.fromRestriction σ h) := by
  have hHom : (restrictCoextendScalarsAdj.{w, u, v} σ).homEquiv M N h =
      RestrictionCoextensionAdj.HomEquiv.fromRestriction σ h := by
    rw [Adjunction.homEquiv_unit]
    ext m a
    rfl
  exact ((restrictCoextendScalarsAdj.{w, u, v} σ).extEquiv_mk₀ h).trans
    (congrArg (fun k : M ⟶ (coextendScalars σ).obj N => Ext.mk₀ k) hHom)

/-- Inverse degree-zero comparison is the original evaluation-at-one Hom map. -/
@[simp]
theorem coextendScalarsExtEquiv_symm_mk₀ (M : ModuleCat.{max v w} A)
    (N : ModuleCat.{max v w} R) (h : M ⟶ (coextendScalars σ).obj N) :
    (coextendScalarsExtEquiv σ M N 0).symm (Ext.mk₀ h) =
      Ext.mk₀ (RestrictionCoextensionAdj.HomEquiv.toRestriction σ h) := by
  have hHom : ((restrictCoextendScalarsAdj.{w, u, v} σ).homEquiv M N).symm h =
      RestrictionCoextensionAdj.HomEquiv.toRestriction σ h := by
    rw [Adjunction.homEquiv_counit]
    ext m
    rfl
  exact ((restrictCoextendScalarsAdj.{w, u, v} σ).extEquiv_symm_mk₀ h).trans
    (congrArg (fun k : (restrictScalars σ).obj M ⟶ N => Ext.mk₀ k) hHom)

/-- The actual degree-zero forward map sends h to the functional m ↦ (a ↦ h(a • m)). -/
theorem coextendScalarsExtEquiv_mk₀_hom_apply (M : ModuleCat.{max v w} A)
    (N : ModuleCat.{max v w} R) (h : (restrictScalars σ).obj M ⟶ N) (m : M) (a : A) :
    (Ext.homEquiv₀ (coextendScalarsExtEquiv σ M N 0 (Ext.mk₀ h))).hom m a = h (a • m) := by
  rw [coextendScalarsExtEquiv_mk₀]
  change (Ext.homEquiv₀ (Ext.homEquiv₀.symm
    (RestrictionCoextensionAdj.HomEquiv.fromRestriction σ h))).hom m a = _
  rw [Equiv.apply_symm_apply]
  rfl

/-- The actual inverse degree-zero map evaluates each original functional at one. -/
theorem coextendScalarsExtEquiv_symm_mk₀_hom_apply (M : ModuleCat.{max v w} A)
    (N : ModuleCat.{max v w} R) (h : M ⟶ (coextendScalars σ).obj N) (m : M) :
    (Ext.homEquiv₀ ((coextendScalarsExtEquiv σ M N 0).symm (Ext.mk₀ h))).hom m =
      h.hom m (1 : A) := by
  rw [coextendScalarsExtEquiv_symm_mk₀]
  change (Ext.homEquiv₀ (Ext.homEquiv₀.symm
    (RestrictionCoextensionAdj.HomEquiv.toRestriction σ h))).hom m = _
  rw [Equiv.apply_symm_apply]
  rfl

end Ext

section Counit

variable {R : Type u} {A : Type v} [Ring R] [Ring A] (σ : R →+* A)

/-- The counit used in the inverse Ext comparison is the actual evaluation at one.
This ordinary formula needs neither projectivity nor Ext instances. -/
theorem coextendScalarsExt_counit_apply (N : ModuleCat.{max v w} R)
    (x : (coextendScalars σ).obj N) :
    ((restrictCoextendScalarsAdj.{w, u, v} σ).counit.app N).hom x = x (1 : A) := rfl

end Counit

end ModuleCat
