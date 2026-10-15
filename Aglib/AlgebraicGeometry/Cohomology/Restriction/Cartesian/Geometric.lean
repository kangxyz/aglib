/-
Copyright (c) 2026 algebraic-geometry contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.Cohomology.Restriction.Cartesian
public import Aglib.AlgebraicGeometry.Cohomology.Restriction.Coefficients
public import Aglib.AlgebraicGeometry.Cohomology.MayerVietoris.GeometricTop

/-! # Geometric compatibility of the original open-restriction equivalence

The original native open comparison intertwines geometric pullback with
the actual pullback/restriction mate. The coefficient map is the original
inverse mate, and all comparisons retain their original units and forward
maps on unchanged `Sheaf.H`.
-/

@[expose] public section

noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry TopologicalSpace Opposite

namespace AlgebraicGeometry.Scheme.Cohomology

variable {X Y : Scheme.{u}}

set_option maxHeartbeats 300000 in
-- Converting the native composed open maps to the original pointwise formulas is costly.
/-- The original open equivalence commutes with geometric pullback through the actual
inverse cartesian pullback/restriction mate and original coefficient map. -/
theorem moduleHPrimeOpenRestrictionAddEquiv_pullback (p : Y ⟶ X) (M : X.Modules)
    (U : X.Opens) (n : ℕ) (x : Sheaf.H'.{u + 1} (moduleAddSheaf X M) n U) :
    let V := p ⁻¹ᵁ U
    let a := V.ι
    let b := p ∣_ U
    let j := U.ι
    let h : IsPullback a b p j := (isPullback_morphismRestrict p U).flip
    let N : Y.Modules := (Scheme.Modules.pullback p).obj M
    let P : V.toScheme.Modules := (Scheme.Modules.pullback b).obj (M.restrict j)
    let ε : N.restrict a ⟶ P :=
      inv ((Scheme.Modules.cartesianPullbackBaseChangeMate a b p j h).app M)
    let φp : M ⟶ (Scheme.Modules.pushforward p).obj N :=
      (Scheme.Modules.pullbackPushforwardAdjunction p).unit.app M
    let φb : M.restrict j ⟶ (Scheme.Modules.pushforward b).obj P :=
      (Scheme.Modules.pullbackPushforwardAdjunction b).unit.app (M.restrict j)
    Sheaf.H.map ((SheafOfModules.toSheaf V.toScheme.ringCatSheaf).map ε) n
        (sheafHPrimeOpenRestrictionAddEquiv Y V (moduleAddSheaf Y N) n
          ((zariskiCohomologyOpenMap p (moduleAddSheaf X M) (moduleAddSheaf Y N)
            (moduleCoefficientPullback p (M := M) (N := N) φp) n).app (op U) x)) =
      moduleCohomologyMapAlong b φb n
        (sheafHPrimeOpenRestrictionAddEquiv X U (moduleAddSheaf X M) n x) := by
  let V := p ⁻¹ᵁ U
  let a := V.ι
  let b := p ∣_ U
  let j := U.ι
  let h : IsPullback a b p j := (isPullback_morphismRestrict p U).flip
  let N : Y.Modules := (Scheme.Modules.pullback p).obj M
  let P : V.toScheme.Modules := (Scheme.Modules.pullback b).obj (M.restrict j)
  let ε : N.restrict a ⟶ P :=
    inv ((Scheme.Modules.cartesianPullbackBaseChangeMate a b p j h).app M)
  let φp : M ⟶ (Scheme.Modules.pushforward p).obj N :=
    (Scheme.Modules.pullbackPushforwardAdjunction p).unit.app M
  let φj : M ⟶ (Scheme.Modules.pushforward j).obj (M.restrict j) :=
    (Scheme.Modules.restrictAdjunction j).unit.app M
  let φb : M.restrict j ⟶ (Scheme.Modules.pushforward b).obj P :=
    (Scheme.Modules.pullbackPushforwardAdjunction b).unit.app (M.restrict j)
  let y : Sheaf.H'.{u + 1} (moduleAddSheaf U.toScheme (M.restrict j)) n ⊤ :=
    (Sheaf.cohomologyPresheaf.{u + 1}
      (moduleAddSheaf U.toScheme (M.restrict j)) n).map
        (eqToHom U.ι_preimage_self.symm).op
          ((zariskiCohomologyOpenMap j (moduleAddSheaf X M)
            (moduleAddSheaf U.toScheme (M.restrict j))
            (moduleCoefficientPullback j (M := M) (N := M.restrict j) φj) n).app (op U) x)
  have hL := moduleHPrimeOpenRestrictionAddEquiv_postcomp Y V N ε n
    ((zariskiCohomologyOpenMap p (moduleAddSheaf X M) (moduleAddSheaf Y N)
      (moduleCoefficientPullback p (M := M) (N := N) φp) n).app (op U) x)
  have hraw := ConcreteCategory.congr_hom (moduleHPrimeOpenMap_pullback_restrict p M U n) x
  simp only [ConcreteCategory.comp_apply] at hraw
  have hT := congrArg (sheafHPrimeTopAddEquiv V.toScheme (moduleAddSheaf V.toScheme P) n) hraw
  have hR := sheafHPrimeTopAddEquiv_geometric b
    (moduleAddSheaf U.toScheme (M.restrict j)) (moduleAddSheaf V.toScheme P)
    (moduleCoefficientPullback b (M := M.restrict j) (N := P) φb) n y
  have hU := moduleHPrimeOpenRestrictionAddEquiv_geometric X U M n x
  have hR' : sheafHPrimeTopAddEquiv V.toScheme (moduleAddSheaf V.toScheme P) n
      ((zariskiCohomologyOpenMap b (moduleAddSheaf U.toScheme (M.restrict j))
        (moduleAddSheaf V.toScheme P)
        (moduleCoefficientPullback b (M := M.restrict j) (N := P) φb) n).app (op ⊤) y) =
    moduleCohomologyMapAlong b φb n
      (sheafHPrimeOpenRestrictionAddEquiv X U (moduleAddSheaf X M) n x) :=
    hR.trans (congrArg (moduleCohomologyMapAlong b φb n) hU.symm)
  refine hL.trans ?_
  refine hT.trans ?_
  dsimp only [y] at hR'
  exact hR'

end AlgebraicGeometry.Scheme.Cohomology
