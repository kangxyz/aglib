/-
Copyright (c) 2026 algebraic-geometry contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.Cohomology.DirectImage.Affine.Localization.ScalarMate
public import Aglib.AlgebraicGeometry.Cohomology.BaseChange.Modules.Separated.Cartesian

/-! # Original localization from the actual scalar mate

The original scalar-adjunction unit converts invertibility of the original
cohomology tensor mate into localization of its original geometric map.
This complete lower construction is shared by qcqs and separated producers.
-/

@[expose] public section

noncomputable section

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry TopologicalSpace Opposite

namespace AlgebraicGeometry.Scheme.Cohomology

universe u

variable {R S : Type u} [CommRing R] [CommRing S] {X Y : Scheme.{u}}

/-- The actual cohomology pullback map in the supplied localization square localizes original
cohomology of every quasicoherent coefficient on a quasi-compact separated source. -/
theorem moduleCohomologyRestrictionMap_isLocalizedModule_of_isPullback_of_isSeparated
    (p : Y ⟶ X) (q : Y ⟶ Spec (CommRingCat.of S))
    (f : X ⟶ Spec (CommRingCat.of R)) [QuasiCompact f] [IsSeparated f]
    (T : Submonoid R) (σ : R →+* S)
    (h : IsPullback p q f (Spec.map (CommRingCat.ofHom σ)))
    (hloc : letI := σ.toAlgebra; IsLocalization T S)
    (M : X.Modules) [M.IsQuasicoherent] (n : ℕ) :
    let α := f.appTop.hom.comp (Scheme.ΓSpecIso (CommRingCat.of R)).inv.hom
    let β := q.appTop.hom.comp (Scheme.ΓSpecIso (CommRingCat.of S)).inv.hom
    let hs := moduleSectionsBaseChangeScalars p q f σ h.w
    let N : Y.Modules := (Scheme.Modules.pullback p).obj M
    let φp : M ⟶ (Scheme.Modules.pushforward p).obj N :=
      (Scheme.Modules.pullbackPushforwardAdjunction p).unit.app M
    letI := moduleCohomologyModuleOfHom X α M n
    letI := moduleCohomologyModuleOfHom Y β N n
    IsLocalizedModule T (moduleCohomologyRestrictionMap p σ α β hs φp n).hom := by
  let : Algebra R S := σ.toAlgebra
  let : IsLocalization T S := hloc
  exact moduleCohomologyRestrictionMap_isLocalizedModule_of_isPullback_of_tensor_isIso
    p q f T σ h hloc M n
    (moduleCohomologyTensorMap_isIso_of_isPullback
      p q f σ h (IsLocalization.flat S T) M n)

end AlgebraicGeometry.Scheme.Cohomology
