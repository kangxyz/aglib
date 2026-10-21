/-
Copyright (c) 2026 algebraic-geometry contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.Modules.QuasiCoherent.Affine.PullbackSections
public import Aglib.AlgebraicGeometry.Cohomology.BaseChange.HigherDirectImage.Nonflat.ChartAdjoint
public import Aglib.Algebra.Category.ModuleCat.ScalarExtensionCoordinatesUnit

/-!
# Scalar-extension coordinates on the original affine charts

For a commuting pair of affine open charts of a scheme morphism, the actual
pullback sections are scalar extension of the original source-chart sections.
The comparison and its coordinate change preserve the original restricted
geometric unit. No reconstructed base-change square, flatness, or finiteness
hypothesis is used.
-/

@[expose] public noncomputable section
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

universe u
open CategoryTheory
open scoped TensorProduct

namespace AlgebraicGeometry.Scheme.Modules

variable {R S : Type u} [CommRing R] [CommRing S] [Algebra R S]
  {X Z : Scheme.{u}} (p : Z ⟶ X)
  (j : Spec (CommRingCat.of R) ⟶ X) [IsOpenImmersion j]
  (c : Spec (CommRingCat.of S) ⟶ Z) [IsOpenImmersion c]
  (H : c ≫ p = Spec.map (CommRingCat.ofHom (algebraMap R S)) ≫ j)
  (M : X.Modules) [M.IsQuasicoherent]

local notation "φ" => CommRingCat.ofHom (algebraMap R S)

/-- Sections of the actual pullback on the supplied target chart are scalar
extension of the sections on the supplied source chart. -/
def chartPullbackSectionsIso :
    (ModuleCat.extendScalars (algebraMap R S)).obj
      (moduleSpecΓFunctor.obj (M.restrict j)) ≅
      moduleSpecΓFunctor.obj (((pullback p).obj M).restrict c) :=
  affinePullbackGlobalSectionsIso φ (M.restrict j) ≪≫
    moduleSpecΓFunctor.mapIso ((pullbackOpenSquare c (Spec.map φ) p j H).app M).symm

/-- The native chart comparison preserves the original restricted pullback unit. -/
theorem chartPullbackSectionsIso_unit :
    (ModuleCat.extendRestrictScalarsAdj (φ).hom).unit.app
        (moduleSpecΓFunctor.obj (M.restrict j)) ≫
      (ModuleCat.restrictScalars (φ).hom).map
        (chartPullbackSectionsIso p j c H M).hom =
    moduleSpecΓFunctor.map
      (Nonflat.chartCoefficient p j c (Spec.map φ) H.symm
        ((pullbackPushforwardAdjunction p).unit.app M)) ≫
      (pushforwardGlobalSectionsIso φ).hom.app (((pullback p).obj M).restrict c) := by
  have hc : (pullbackPushforwardAdjunction (Spec.map φ)).unit.app (M.restrict j) ≫
      (pushforward (Spec.map φ)).map
        ((pullbackOpenSquare c (Spec.map φ) p j H).inv.app M) =
    Nonflat.chartCoefficient p j c (Spec.map φ) H.symm
      ((pullbackPushforwardAdjunction p).unit.app M) := by
    change (pullbackPushforwardAdjunction (Spec.map φ)).homEquiv _ _
      ((pullbackOpenSquare c (Spec.map φ) p j H).inv.app M) = _
    rw [← Nonflat.chartCoefficient_pullbackUnit_adjoint p j c (Spec.map φ) H.symm M]
    exact Equiv.apply_symm_apply _ _
  have hn := (pushforwardGlobalSectionsIso φ).hom.naturality
    ((pullbackOpenSquare c (Spec.map φ) p j H).inv.app M)
  dsimp only [Functor.comp_map, Functor.comp_obj] at hn
  dsimp only [chartPullbackSectionsIso, Iso.trans_hom, Functor.mapIso_hom,
    Iso.symm_hom, Iso.app_inv]
  rw [Functor.map_comp, ← Category.assoc, affinePullbackGlobalSectionsIso_unit,
    Category.assoc, ← hn, ← Functor.map_comp_assoc, hc]

/-- Scalar-extension coordinates for the actual target-chart sections, using
any specified coordinates for the original source-chart sections. -/
def chartPullbackCoordinatesIso {N : ModuleCat.{u} R}
    (e : moduleSpecΓFunctor.obj (M.restrict j) ≅ N) :
    moduleSpecΓFunctor.obj (((pullback p).obj M).restrict c) ≅
      ModuleCat.of S (S ⊗[R] N) :=
  ModuleCat.scalarExtensionCoordinatesIso (chartPullbackSectionsIso p j c H M) e

/-- The original chart-unit arrow in the specified scalar-extension coordinates. -/
theorem chartPullbackCoordinatesIso_unit {N : ModuleCat.{u} R}
    (e : moduleSpecΓFunctor.obj (M.restrict j) ≅ N) :
    (ModuleCat.extendRestrictScalarsAdj (φ).hom).unit.app N ≫
      (ModuleCat.restrictScalars (φ).hom).map
        ((ModuleCat.extendScalarsAlgebraIso R S N).hom ≫
          (chartPullbackCoordinatesIso p j c H M e).inv) =
    e.inv ≫ moduleSpecΓFunctor.map
      (Nonflat.chartCoefficient p j c (Spec.map φ) H.symm
        ((pullbackPushforwardAdjunction p).unit.app M)) ≫
      (pushforwardGlobalSectionsIso φ).hom.app (((pullback p).obj M).restrict c) := by
  have h := congrArg (fun k => e.inv ≫ k) (chartPullbackSectionsIso_unit p j c H M)
  exact (ModuleCat.scalarExtensionCoordinatesIso_unit
    (R := R) (S := S) (chartPullbackSectionsIso p j c H M) e).trans
      (by simpa only [CommRingCat.hom_ofHom, Functor.id_obj, Category.assoc] using h)

end AlgebraicGeometry.Scheme.Modules
