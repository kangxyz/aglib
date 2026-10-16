/-
Copyright (c) 2026 algebraic-geometry contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.Algebra.Category.ModuleCat.Localization.ScalarExtension
public import Aglib.AlgebraicGeometry.Cohomology.BaseChange.Modules.Qcqs

/-!
# Original cohomology pullback at a localization

The proved canonical qcqs flat base-change map is the native scalar mate
of the original geometric cohomology map. At a ring localization, its
original adjunction unit therefore proves that this actual geometric map
is the module-localization map. The supplied cartesian square, original
module pullback unit, scalar actions and unchanged `Sheaf.H` are retained.
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
cohomology of every quasicoherent coefficient on a qcqs source. -/
theorem moduleCohomologyRestrictionMap_isLocalizedModule_of_isPullback
    (p : Y ⟶ X) (q : Y ⟶ Spec (CommRingCat.of S))
    (f : X ⟶ Spec (CommRingCat.of R)) [QuasiCompact f] [QuasiSeparated f]
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
  have hflat : σ.Flat := IsLocalization.flat S T
  let α := f.appTop.hom.comp (Scheme.ΓSpecIso (CommRingCat.of R)).inv.hom
  let β := q.appTop.hom.comp (Scheme.ΓSpecIso (CommRingCat.of S)).inv.hom
  let hs := moduleSectionsBaseChangeScalars p q f σ h.w
  let N : Y.Modules := (Scheme.Modules.pullback p).obj M
  let φp : M ⟶ (Scheme.Modules.pushforward p).obj N :=
    (Scheme.Modules.pullbackPushforwardAdjunction p).unit.app M
  let := moduleCohomologyModuleOfHom X α M n
  let := moduleCohomologyModuleOfHom Y β N n
  let : IsIso (moduleCohomologyTensorMap p σ α β hs φp n) :=
    moduleCohomologyTensorMap_isIso_of_quasiSeparated_of_isPullback
      p q f σ h hflat M n
  let : IsIso
      (((ModuleCat.extendRestrictScalarsAdj.{u + 1, u, u} σ).homEquiv
        (ModuleCat.of R (Sheaf.H.{u + 1} (moduleAddSheaf X M) n))
        (ModuleCat.of S (Sheaf.H.{u + 1} (moduleAddSheaf Y N) n))).symm
          (moduleCohomologyRestrictionMap p σ α β hs φp n)) := by
    change IsIso (moduleCohomologyTensorMap p σ α β hs φp n)
    infer_instance
  exact ModuleCat.isLocalizedModule_of_isIso_adjoint.{u, u, u + 1} T σ hloc
    (moduleCohomologyRestrictionMap p σ α β hs φp n)

end AlgebraicGeometry.Scheme.Cohomology
