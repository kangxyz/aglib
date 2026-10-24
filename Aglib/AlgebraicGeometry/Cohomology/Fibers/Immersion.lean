/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.Cohomology.Fibers.Basic
public import Aglib.AlgebraicGeometry.Cohomology.Functoriality.Modules.Isomorphism
public import Aglib.AlgebraicGeometry.Cohomology.BaseChange.Modules.Sections
public import Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion

/-! # Actual point-fibre cohomology under residue-preserving base change

A Cartesian square and an isomorphism on the original residue fields identify
the literal native point fibres. The same original scheme map and coefficient
pullback comparison induce an isomorphism of original module cohomology after
restriction along the actual residue-field map. Hence actual fibre dimensions
agree. Surjective stalk maps, in particular closed immersions, provide the
residue-field isomorphism.

No properness, quasicoherence, finiteness, flatness or cohomological base-change
hypothesis is used: this is invariance under the actual fibre isomorphism.
-/

@[expose] public noncomputable section

set_option backward.isDefEq.respectTransparency false

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits

universe u

namespace AlgebraicGeometry

/-- A surjective actual stalk map induces an isomorphism of the corresponding
actual residue fields. -/
theorem residueFieldMap_isIso_of_surjectiveOnStalks {X Y : Scheme.{u}}
    (g : X ⟶ Y) [SurjectiveOnStalks g] (x : X) : IsIso (g.residueFieldMap x) := by
  apply (ConcreteCategory.isIso_iff_bijective _).mpr
  refine ⟨(g.residueFieldMap x).hom.injective, ?_⟩
  have h : Function.Surjective (Y.residue (g x) ≫ g.residueFieldMap x) := by
    rw [Scheme.residue_residueFieldMap]
    exact (X.residue_surjective x).comp (g.stalkMap_surjective x)
  intro z
  obtain ⟨a, ha⟩ := h z
  exact ⟨Y.residue (g x) a, ha⟩

namespace Scheme.Cohomology

variable {W X V Y : Scheme.{u}} {a : W ⟶ X} {b : W ⟶ V} {f : X ⟶ Y} {g : V ⟶ Y}
  (h : IsPullback a b f g) (y : V) [IsIso (g.residueFieldMap y)]

include h

/-- The native fibre map in a Cartesian square is an isomorphism whenever the
actual map on the two residue fields is an isomorphism. -/
def modulePointFiberBaseChangeIso : b.fiber y ≅ f.fiber (g y) := by
  let t : b.fiber y ⟶ f.fiber (g y) :=
    pullback.map b (V.fromSpecResidueField y) f (Y.fromSpecResidueField (g y))
      a (Spec.map (g.residueFieldMap y)) g h.w.symm (by simp)
  have ht := isPullback_fiberToSpecResidueField_of_isPullback h y
  let : IsIso t := ht.isIso_fst_of_isIso
  exact asIso t

/-- The fibre isomorphism preserves the actual maps to the original source. -/
@[reassoc]
theorem modulePointFiberBaseChangeIso_hom_fiberι :
    (modulePointFiberBaseChangeIso h y).hom ≫ f.fiberι (g y) = b.fiberι y ≫ a := by
  simp [modulePointFiberBaseChangeIso, Scheme.Hom.fiberι]

/-- The fibre isomorphism retains the actual residue-field map on its base. -/
@[reassoc]
theorem modulePointFiberBaseChangeIso_hom_toSpec :
    (modulePointFiberBaseChangeIso h y).hom ≫ f.fiberToSpecResidueField (g y) =
      b.fiberToSpecResidueField y ≫ Spec.map (g.residueFieldMap y) := by
  simp [modulePointFiberBaseChangeIso, Scheme.Hom.fiberToSpecResidueField]

/-- The actual coefficient comparison uses the same fibre map and the native
pullback-composition isomorphisms. -/
def modulePointFiberBaseChangeCoefficientIso (M : X.Modules) :
    (Modules.pullback (modulePointFiberBaseChangeIso h y).hom).obj
        ((Modules.pullback (f.fiberι (g y))).obj M) ≅
      (Modules.pullback (b.fiberι y)).obj ((Modules.pullback a).obj M) :=
  (Modules.pullbackComp (modulePointFiberBaseChangeIso h y).hom (f.fiberι (g y))).app M ≪≫
    (Modules.pullbackCongr (modulePointFiberBaseChangeIso_hom_fiberι h y)).app M ≪≫
      ((Modules.pullbackComp (b.fiberι y) a).app M).symm

/-- The original cohomology isomorphism, with the original residue-field map
rather than an unidentified field equivalence. -/
def modulePointFiberCohomologyBaseChangeIso (M : X.Modules) (q : ℕ) :
    modulePointFiberCohomology f M q (g y) ≅
      (ModuleCat.restrictScalars (g.residueFieldMap y).hom).obj
        (modulePointFiberCohomology b ((Modules.pullback a).obj M) q y) := by
  let L := (Modules.pullback (f.fiberι (g y))).obj M
  let α := (f.fiberToSpecResidueField (g y)).appTop.hom.comp
    (Scheme.ΓSpecIso (Y.residueField (g y))).inv.hom
  let β := (b.fiberToSpecResidueField y).appTop.hom.comp
    (Scheme.ΓSpecIso (V.residueField y)).inv.hom
  let e := modulePointFiberBaseChangeIso h y
  let κ := (g.residueFieldMap y).hom
  have hs := moduleSectionsBaseChangeScalars e.hom (b.fiberToSpecResidueField y)
    (f.fiberToSpecResidueField (g y)) κ (modulePointFiberBaseChangeIso_hom_toSpec h y)
  exact moduleCohomologyRestrictionIsoOfPullbackIso e.hom κ α β hs L
    (modulePointFiberBaseChangeCoefficientIso h y M) q

/-- Original point-fibre cohomology dimensions agree under any actual
Cartesian base change that preserves the residue field at the point. -/
theorem modulePointFiberCohomologyDimension_baseChange (M : X.Modules) (q : ℕ) :
    modulePointFiberCohomologyDimension f M q (g y) =
      modulePointFiberCohomologyDimension b ((Modules.pullback a).obj M) q y := by
  let κ := (asIso (g.residueFieldMap y)).commRingCatIsoToRingEquiv
  let E : modulePointFiberCohomology f M q (g y) ≃+
      modulePointFiberCohomology b ((Modules.pullback a).obj M) q y :=
    (modulePointFiberCohomologyBaseChangeIso h y M q).toLinearEquiv.toAddEquiv
  have hs (r : Y.residueField (g y)) (x : modulePointFiberCohomology f M q (g y)) :
      E (r • x) = κ r • E x :=
    (modulePointFiberCohomologyBaseChangeIso h y M q).toLinearEquiv.map_smul r x
  have hr := lift_rank_eq_of_equiv_equiv κ E κ.bijective hs
  simpa only [modulePointFiberCohomologyDimension, Module.finrank, Cardinal.toNat_lift]
    using congrArg Cardinal.toNat hr

omit [IsIso (g.residueFieldMap y)] in
/-- Closed immersions, and more generally morphisms surjective on stalks,
retain the original point-fibre cohomology dimensions after Cartesian pullback. -/
theorem modulePointFiberCohomologyDimension_baseChange_of_surjectiveOnStalks
    [SurjectiveOnStalks g] (M : X.Modules) (q : ℕ) :
    modulePointFiberCohomologyDimension f M q (g y) =
      modulePointFiberCohomologyDimension b ((Modules.pullback a).obj M) q y := by
  let : IsIso (g.residueFieldMap y) := residueFieldMap_isIso_of_surjectiveOnStalks g y
  exact modulePointFiberCohomologyDimension_baseChange h y M q

end Scheme.Cohomology

end AlgebraicGeometry
