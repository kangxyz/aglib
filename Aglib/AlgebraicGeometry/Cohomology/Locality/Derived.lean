/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.Cohomology.Functoriality.Restriction
public import Aglib.AlgebraicGeometry.Cohomology.BaseChange.Flat
public import Aglib.AlgebraicGeometry.Modules.Locality.Exactness
public import Aglib.Algebra.Homology.DerivedCategory.RightDerivedFunctorPlus.Homology

/-! # Open-cover reflection in the bounded-below derived category

Source:
`Quillen/AlgebraicGeometry/Scheme/Sheaf/DerivedOpenCoverConservativity.lean`
at LOCAL Quillen
`189a8e779f0c68b2dfc6f8195daebb3e684a5905`.
Source SHA-256:
`06bd4bcc7ba3b48a5adadfa2f5cd8e75ee2191242c37b83d38144188411fd60e`.
Selected declarations: isIso_of_derivedRestriction_openCover,
  isIso_of_derivedOpenPullback_openCover.
Source:
`Quillen/AlgebraicGeometry/PerfectComplexes/ProjectiveLine/P5NativeNegativeVanishing.lean`
at LOCAL Quillen
`189a8e779f0c68b2dfc6f8195daebb3e684a5905`.
Source SHA-256:
`a4dfe13e4c931d2b2b2852fdb372a9d01c0730549cbcd3c437f9a145ddc0b24d`.
Selected declarations: isZero_of_derivedOpenCover.
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true

universe u v
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
attribute [local instance] Abelian.hasFiniteBiproducts
namespace AlgebraicGeometry.Scheme.Modules
/-- The standard derived-category model for module sheaves on `X` in open-cover comparisons. -/
local instance openCoverDerivedStandard (X : Scheme.{u}) :
    HasDerivedCategory.{u + 1} X.Modules := HasDerivedCategory.standard _

variable {X : Scheme.{u}} {ι : Type v} (Y : ι → Scheme.{u}) (a : ∀ i, Y i ⟶ X)
  [∀ i, IsOpenImmersion (a i)] (hcover : ∀ x : X, ∃ (i : ι) (y : Y i), a i y = x)

include hcover in
theorem isIso_of_derivedRestriction_openCover {K L : DerivedCategory.Plus X.Modules}
    (q : K ⟶ L) (hq : ∀ i, IsIso ((derivedRestrictionPlus (a i)).map q)) : IsIso q := by
  apply (DerivedCategory.Plus.isIso_iff q).mpr
  intro n
  apply isIso_of_restrict_openCover Y a hcover
  intro i
  let := hq i
  exact (NatIso.isIso_map_iff
    ((Scheme.Modules.restrictFunctor (a i)).rightDerivedFunctorPlusHomologyIso n) q).mp
    (show IsIso (((derivedRestrictionPlus (a i)) ⋙
      DerivedCategory.Plus.homologyFunctor (Y i).Modules n).map q) from by
        change IsIso ((DerivedCategory.Plus.homologyFunctor (Y i).Modules n).map
          ((derivedRestrictionPlus (a i)).map q))
        infer_instance)

include hcover in
theorem isIso_of_derivedOpenPullback_openCover {K L : DerivedCategory.Plus X.Modules}
    (q : K ⟶ L) (hq : ∀ i, IsIso ((derivedFlatPullbackPlus (a i)).map q)) : IsIso q := by
  apply isIso_of_derivedRestriction_openCover Y a hcover q
  intro i
  let := hq i
  exact (NatIso.isIso_map_iff
    ((Scheme.Modules.restrictFunctor (a i)).rightDerivedFunctorPlusIso
      (Scheme.Modules.restrictFunctorIsoPullback (a i))) q).mpr
    (show IsIso ((derivedFlatPullbackPlus (a i)).map q) from inferInstance)

theorem isZero_of_derivedOpenCover {X : Scheme.{u}} {ι : Type v}
    (Y : ι → Scheme.{u}) (a : ∀ i, Y i ⟶ X) [∀ i, IsOpenImmersion (a i)]
    (hc : ∀ x : X, ∃ i y, a i y = x) (K : DerivedCategory.Plus X.Modules)
    (hK : ∀ i, IsZero ((derivedFlatPullbackPlus (a i)).obj K)) : IsZero K := by
  have : IsIso (0 : K ⟶ K) := by
    apply isIso_of_derivedOpenPullback_openCover Y a hc
    intro i
    let : (derivedFlatPullbackPlus (a i)).Additive := by
      dsimp [derivedFlatPullbackPlus]
      infer_instance
    rw [Functor.map_zero]
    exact (hK i).isIso (hK i) 0
  exact (isIsoZero_iff_source_target_isZero K K).mp this |>.1

end AlgebraicGeometry.Scheme.Modules
