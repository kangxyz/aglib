/-
Copyright (c) 2026 algebraic-geometry contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.Cohomology.Restriction.Open
public import Aglib.AlgebraicGeometry.Cohomology.Functoriality.Modules
public import Aglib.AlgebraicGeometry.Cohomology.MayerVietoris.Geometric
public import Aglib.Topology.Sheaves.Cohomology.Restriction.Geometric

/-!
# The original geometric map and open restriction

The open-cohomology comparison with actual restricted-module cohomology is
the original geometric inverse-image map with the original restriction unit.
The comparison retains the native inverse-image-open equality and actual
module-to-additive coefficient map. No quasicoherence or flatness is needed.
-/

@[expose] public section

noncomputable section

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry TopologicalSpace Opposite

namespace AlgebraicGeometry.Scheme.Cohomology

universe u

/-- Forgetting the original module restriction unit gives the normalized native
inverse-image/restriction comparison. -/
theorem moduleCoefficientPullback_restrictUnit (X : Scheme.{u}) (U : X.Opens)
    (M : X.Modules) :
    moduleCoefficientPullback U.ι ((Scheme.Modules.restrictAdjunction U.ι).unit.app M) =
      (TopCat.Sheaf.openRestrictionInverseImageIso (X := X.toTopCat) U).hom.app
        (moduleAddSheaf X M) := by
  apply ((TopCat.Sheaf.pullbackPushforwardAdjunction AddCommGrpCat.{u}
    U.ι.base).homEquiv _ _).injective
  rw [moduleCoefficientPullback, Equiv.apply_symm_apply]
  erw [TopCat.Sheaf.openRestrictionPullbackIso_homEquiv (X := X.toTopCat) U
    (moduleAddSheaf X M)]
  rfl

/-- The actual additive open comparison is the original geometric map for the open
immersion, followed by its native whole-space comparison. -/
theorem sheafHPrimeOpenRestrictionAddEquiv_geometric (X : Scheme.{u}) (U : X.Opens)
    (A : Sheaf (Opens.grothendieckTopology X) AddCommGrpCat.{u})
    (n : ℕ) (x : Sheaf.H'.{u + 1} A n U) :
    sheafHPrimeOpenRestrictionAddEquiv X U A n x =
      sheafHPrimeTopAddEquiv U.toScheme ((openAdditiveRestriction X U).obj A) n
        ((((openAdditiveRestriction X U).obj A).cohomologyPresheaf n).map
          (eqToHom U.ι_preimage_self.symm).op
            ((zariskiCohomologyOpenMap U.ι A ((openAdditiveRestriction X U).obj A)
              ((TopCat.Sheaf.openRestrictionInverseImageIso (X := X.toTopCat) U).hom.app A)
              n).app (op U) x)) := by
  let B := (openAdditiveRestriction X U).obj A
  let W := U.isOpenEmbedding.functor.obj (⊤ : TopologicalSpace.Opens U)
  let i : op U ⟶ op W := (eqToHom (openRestriction_image_top X U)).op
  let q : (⊤ : U.toScheme.Opens) ⟶ U.ι ⁻¹ᵁ W :=
    eqToHom (Opens.map_functor_eq (U := U) (⊤ : TopologicalSpace.Opens U)).symm
  let k : (⊤ : U.toScheme.Opens) ⟶ U.ι ⁻¹ᵁ U := eqToHom U.ι_preimage_self.symm
  let g := zariskiCohomologyOpenMap U.ι A B
    ((TopCat.Sheaf.openRestrictionInverseImageIso (X := X.toTopCat) U).hom.app A) n
  have hg (y : Sheaf.H'.{u + 1} A n W) :
      TopCat.Sheaf.cohomologyOpenRestrictionAddEquiv (X := X.toTopCat) U A n ⊤ y =
        (B.cohomologyPresheaf n).map q.op (g.app (op W) y) := by
    exact TopCat.Sheaf.cohomologyOpenRestrictionAddEquiv_geometric
      (X := X.toTopCat) U A n ⊤ y
  change sheafHPrimeTopAddEquiv U.toScheme B n
      (TopCat.Sheaf.cohomologyOpenRestrictionAddEquiv U A n ⊤
        ((A.cohomologyPresheaf n).map i x)) =
    sheafHPrimeTopAddEquiv U.toScheme B n
      ((B.cohomologyPresheaf n).map k.op (g.app (op U) x))
  apply congrArg (sheafHPrimeTopAddEquiv U.toScheme B n)
  erw [hg ((A.cohomologyPresheaf n).map i x)]
  have hn := congrArg (fun f => f x) (g.naturality i)
  change g.app (op W) ((A.cohomologyPresheaf n).map i x) =
    (B.cohomologyPresheaf n).map ((Opens.map U.ι.base).op.map i)
      (g.app (op U) x) at hn
  rw [hn]
  change ((B.cohomologyPresheaf n).map ((Opens.map U.ι.base).op.map i) ≫
    (B.cohomologyPresheaf n).map q.op) (g.app (op U) x) = _
  rw [← (B.cohomologyPresheaf n).map_comp]
  have h : (Opens.map U.ι.base).op.map i ≫ q.op = k.op := Subsingleton.elim _ _
  rw [h]
  rfl

/-- The structural-ring-linear open comparison retains the original module restriction
unit and the original geometric map. -/
theorem moduleHPrimeOpenLinearEquiv_geometric (X : Scheme.{u}) {R : Type u} [CommRing R]
    (α : R →+* Γ(X, ⊤)) (M : X.Modules) (U : X.Opens) (n : ℕ)
    (x : Sheaf.H'.{u + 1} (moduleAddSheaf X M) n U) :
    letI := moduleHPrimeModuleOfHom X α M n U
    letI := moduleCohomologyModuleOfHom U.toScheme (U.ι.appTop.hom.comp α) (M.restrict U.ι) n
    moduleHPrimeOpenLinearEquiv X α M U n x =
      sheafHPrimeTopAddEquiv U.toScheme (moduleAddSheaf U.toScheme (M.restrict U.ι)) n
        (((moduleAddSheaf U.toScheme (M.restrict U.ι)).cohomologyPresheaf n).map
          (eqToHom U.ι_preimage_self.symm).op
            ((zariskiCohomologyOpenMap U.ι (moduleAddSheaf X M)
              (moduleAddSheaf U.toScheme (M.restrict U.ι))
              (moduleCoefficientPullback U.ι ((Scheme.Modules.restrictAdjunction U.ι).unit.app M))
              n).app (op U) x)) := by
  let := moduleHPrimeModuleOfHom X α M n U
  let := moduleCohomologyModuleOfHom U.toScheme (U.ι.appTop.hom.comp α) (M.restrict U.ι) n
  change sheafHPrimeOpenRestrictionAddEquiv X U (moduleAddSheaf X M) n x = _
  have h := sheafHPrimeOpenRestrictionAddEquiv_geometric X U (moduleAddSheaf X M) n x
  erw [← moduleCoefficientPullback_restrictUnit X U M] at h
  exact h

end AlgebraicGeometry.Scheme.Cohomology
