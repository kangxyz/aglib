/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz, Codex
-/
module

public import Aglib.AlgebraicGeometry.Modules.LocallyFree.LocalSplitting
public import Aglib.AlgebraicGeometry.Modules.Tensor.Restriction
public import Aglib.AlgebraicGeometry.Modules.Locality.Exactness
public import Aglib.AlgebraicGeometry.Modules.Tensor.Symmetry

/-! # Arbitrary coefficient tensor on a locally split exact sequence

Source:
`Quillen/AlgebraicGeometry/PerfectComplexes/ProjectiveLine/P5LocallySplitTensor.lean`
at LOCAL Quillen
`189a8e779f0c68b2dfc6f8195daebb3e684a5905`.
Source SHA-256:
`761c5e4f310c183b34150bb0b1e6e86594b8babb17405062b283a47d25413765`.
Selected declarations: shortExact_tensorLeft_of_finiteLocallyFree_quotient,
  shortExact_tensorRight_of_finiteLocallyFree_quotient.
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true

universe u
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
attribute [local instance] Abelian.hasFiniteBiproducts
namespace AlgebraicGeometry.Scheme.Modules

theorem shortExact_tensorLeft_of_finiteLocallyFree_quotient {X : Scheme.{u}}
    (M : X.Modules) {S : ShortComplex X.Modules} (hS : S.ShortExact)
    [IsFiniteLocallyFree X S.X₃] : (S.map (moduleTensorLeftFunctor X M)).ShortExact := by
  classical
  choose U hx hs using fun x : X => exists_local_splitting hS x
  apply shortExact_of_restrict_openCover (fun x => (U x).toScheme) (fun x => (U x).ι)
    (fun x => ⟨x, ⟨x, hx x⟩, rfl⟩)
  intro x
  have : (Scheme.Modules.overEquiv (U x)).functor.Additive := by
    let := preservesBinaryBiproducts_of_preservesBinaryProducts
      (Scheme.Modules.overEquiv (U x)).functor
    exact Functor.additive_of_preservesBinaryBiproducts _
  have : (SheafOfModules.overFunctor.{u} X.ringCatSheaf (U x)).Additive :=
    overRestriction_additive (U x)
  let sU : (S.map (Scheme.Modules.restrictFunctor (U x).ι)).Splitting :=
    ((Classical.choice (hs x)).map (Scheme.Modules.overEquiv (U x)).functor).ofIso
      (S.mapNatIso (Scheme.Modules.overFunctorEquiv (U x)))
  exact ((sU.map (moduleTensorLeftFunctor (U x).toScheme (M.restrict (U x).ι))).ofIso
    (S.mapNatIso (tensorRestrictionNatIso (U x).ι M))).shortExact

theorem shortExact_tensorRight_of_finiteLocallyFree_quotient {X : Scheme.{u}}
    (M : X.Modules) {S : ShortComplex X.Modules} (hS : S.ShortExact)
    [IsFiniteLocallyFree X S.X₃] :
    (S.map (moduleTensorRightFunctor X M)).ShortExact :=
  ShortComplex.shortExact_of_iso
    (S.mapNatIso ((moduleTensorRightLeftIso X M).symm))
    (shortExact_tensorLeft_of_finiteLocallyFree_quotient M hS)

end AlgebraicGeometry.Scheme.Modules
