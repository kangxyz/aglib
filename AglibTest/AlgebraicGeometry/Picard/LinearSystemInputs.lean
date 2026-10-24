/-
Copyright (c) 2026 kangxyz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/

module

public import Aglib.AlgebraicGeometry.Modules.ProjectionFormula.PushforwardTensorPullback
public import Aglib.AlgebraicGeometry.Modules.LocallyFree.LineSubbundle
public import Aglib.AlgebraicGeometry.EffectiveCartierDivisor.Relative.ZeroScheme
public import Aglib.AlgebraicGeometry.Cohomology.BaseChange.ResidueFieldConcentration
public import Aglib.AlgebraicGeometry.Cohomology.BaseChange.ResidueFieldPushforward

/-! Focused consumer of the cohomological inputs of `LinSys` in the locally free regime
(Kleiman, arXiv:math/0504020v1, 3.10 and Thm 3.13, pp. 24–26; Picard plan row F15): the
degree-zero projection formula, line subbundles from fibrewise nonzero maps, zero schemes of
fibrewise nonzero maps on integral fibres, and geometric fibre concentration from residue-field
fibres, with axiom guards. -/

@[expose] public section

open CategoryTheory Limits AlgebraicGeometry

universe u

/-- The degree-zero projection formula in Kleiman's order (3.10 (iii)). -/
noncomputable example {X S : Scheme.{u}} (f : X ⟶ S) (L : X.Modules) (N : S.Modules)
    [Scheme.Modules.IsFiniteLocallyFree S N] :
    (Scheme.Modules.pushforward f).obj
        ((Scheme.Modules.moduleTensorLeftFunctor X L).obj ((Scheme.Modules.pullback f).obj N)) ≅
      (Scheme.Modules.moduleTensorLeftFunctor S ((Scheme.Modules.pushforward f).obj L)).obj N :=
  Scheme.Modules.pushforwardTensorPullbackIso f L N

/-- A map from a line bundle to a rank-`r` vector bundle that is nonzero on every geometric
fibre is a monomorphism with locally free cokernel of rank `r - 1` (Thm 3.13, p. 25). -/
example {X : Scheme.{u}} {N E : X.Modules} (hN : Scheme.Modules.Invertible.IsLocallyRankOne X N)
    [Scheme.Modules.IsFiniteLocallyFree X E] (u : N ⟶ E)
    (hu : ∀ (K : Type u) [Field K] [IsAlgClosed K] (t : Spec (.of K) ⟶ X),
      (Scheme.Modules.pullback t).map u ≠ 0)
    {r : ℕ} (hE : Scheme.Modules.SheafHasRank E r) :
    Mono u ∧ Scheme.Modules.SheafHasRank (cokernel u) (r - 1) :=
  ⟨Scheme.Modules.mono_of_pullback_map_ne_zero hN u
      (Scheme.Modules.pullback_map_ne_zero_of_isAlgClosed u hu),
    Scheme.Modules.sheafHasRank_cokernel_of_pullback_map_ne_zero hN u
      (Scheme.Modules.pullback_map_ne_zero_of_isAlgClosed u hu) hE⟩

/-- Conversely, the kernel inclusion of a rank-one subbundle is nonzero on every field fibre. -/
example {X : Scheme.{u}} {S : ShortComplex X.Modules} (hS : S.ShortExact)
    (h₁ : Scheme.Modules.Invertible.IsLocallyRankOne X S.X₁)
    [Scheme.Modules.IsFiniteLocallyFree X S.X₃] (K : Type u) [Field K]
    (t : Spec (.of K) ⟶ X) :
    (Scheme.Modules.pullback t).map S.f ≠ 0 :=
  Scheme.Modules.pullback_map_f_ne_zero_of_shortExact hS h₁ K t

/-- On a flat, finitely presented family with geometrically integral fibres, a line-bundle map
to the structure sheaf that is nonzero on every geometric fibre cuts out a relative effective
Cartier divisor (Thm 3.13, proof, p. 26). -/
example {X S : Scheme.{u}} (f : X ⟶ S) [Flat f] [LocallyOfFinitePresentation f]
    [GeometricallyIntegral f] (L : Scheme.Modules.Invertible.LineBundle X)
    (φ : (show X.Modules from L.val) ⟶ (show X.Modules from SheafOfModules.unit X.ringCatSheaf))
    (hφ : ∀ (K : Type u) [Field K] [IsAlgClosed K] (t : Spec (.of K) ⟶ S),
      (Scheme.Modules.pullback (pullback.fst f t)).map φ ≠ 0) :
    Scheme.Hom.IsRelativeEffectiveCartier (Scheme.Modules.Hom.zeroInclusion φ) f :=
  Scheme.Modules.Invertible.isRelativeEffectiveCartier_zeroInclusion_of_geometricallyIntegral
    f L φ hφ

/-- The same conclusion for a section `σ : O ⟶ M` of a line bundle, through its dual map
`M^∨ ⟶ O`. -/
example {X S : Scheme.{u}} (f : X ⟶ S) [Flat f] [LocallyOfFinitePresentation f]
    [GeometricallyIntegral f] (M : Scheme.Modules.Invertible.LineBundle X)
    (σ : (show X.Modules from SheafOfModules.unit X.ringCatSheaf) ⟶ (show X.Modules from M.val))
    (hσ : ∀ (K : Type u) [Field K] [IsAlgClosed K] (t : Spec (.of K) ⟶ S),
      (Scheme.Modules.pullback (pullback.fst f t)).map σ ≠ 0) :
    Scheme.Hom.IsRelativeEffectiveCartier
      (Scheme.Modules.Hom.zeroInclusion (Scheme.Modules.Invertible.sectionContraction M σ)) f :=
  Scheme.Modules.Invertible.isRelativeEffectiveCartier_zeroInclusion_sectionContraction_of_geometricallyIntegral
    f M σ hσ

/-- Residue-field fibre conditions give geometric fibre concentration. -/
example {X S : Scheme.{u}} (f : X ⟶ S) [QuasiCompact f] [QuasiSeparated f] (M : X.Modules)
    [M.IsQuasicoherent] (r : ℕ)
    (h0 : ∀ s : S, Scheme.Cohomology.modulePointFiberCohomologyDimension f M 0 s = r)
    (hpos : ∀ (s : S) (n : ℕ), 0 < n →
      Subsingleton (Scheme.Cohomology.modulePointFiberCohomology f M n s)) :
    Scheme.Cohomology.FibreCohomologyConcentrated f M r :=
  Scheme.Cohomology.fibreCohomologyConcentrated_of_modulePointFiberCohomology f M r h0 hpos

/-- Statement 15a: on an open of the base where `h^0 = r` and the higher fibre cohomology
vanishes, the restricted direct image has rank `r` and commutes with every base change. -/
example {X S : Scheme.{u}} [IsLocallyNoetherian S] (f : X ⟶ S) [IsProper f]
    [LocallyOfFinitePresentation f] [Flat f] (M : X.Modules)
    [Scheme.Modules.IsFiniteLocallyFree X M]
    (hpos : ∀ (s : S) (n : ℕ), 0 < n →
      Subsingleton (Scheme.Cohomology.modulePointFiberCohomology f M n s))
    (r : ℕ) (U : S.Opens)
    (hU : ∀ s ∈ U, Scheme.Cohomology.modulePointFiberCohomologyDimension f M 0 s = r) :
    Scheme.Modules.SheafHasRank ((Scheme.Modules.pushforward (pullback.snd f U.ι)).obj
        ((Scheme.Modules.pullback (pullback.fst f U.ι)).obj M)) r :=
  (Scheme.Cohomology.sheafHasRank_and_isIso_moduleBaseChangeMap_of_modulePointFiberCohomology
    f M hpos r U hU).1

/--
info: 'AlgebraicGeometry.Scheme.Modules.pushforwardTensorPullbackNatIso' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms AlgebraicGeometry.Scheme.Modules.pushforwardTensorPullbackNatIso

/--
info: 'AlgebraicGeometry.Scheme.Modules.pushforwardTensorPullbackIso_inv' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms AlgebraicGeometry.Scheme.Modules.pushforwardTensorPullbackIso_inv

/--
info: 'AlgebraicGeometry.Scheme.Modules.pushforwardTensorPullbackIso_hom_naturality' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms AlgebraicGeometry.Scheme.Modules.pushforwardTensorPullbackIso_hom_naturality

/--
info: 'AlgebraicGeometry.Scheme.Modules.exists_isSplitMono_pullback_map_of_fibre_ne_zero' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms AlgebraicGeometry.Scheme.Modules.exists_isSplitMono_pullback_map_of_fibre_ne_zero

/--
info: 'AlgebraicGeometry.Scheme.Modules.mono_of_pullback_map_ne_zero' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms AlgebraicGeometry.Scheme.Modules.mono_of_pullback_map_ne_zero

/--
info: 'AlgebraicGeometry.Scheme.Modules.isFiniteLocallyFree_cokernel_of_pullback_map_ne_zero' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms AlgebraicGeometry.Scheme.Modules.isFiniteLocallyFree_cokernel_of_pullback_map_ne_zero

/--
info: 'AlgebraicGeometry.Scheme.Modules.shortExact_cokernel_of_pullback_map_ne_zero' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms AlgebraicGeometry.Scheme.Modules.shortExact_cokernel_of_pullback_map_ne_zero

/--
info: 'AlgebraicGeometry.Scheme.Modules.sheafHasRank_cokernel_of_pullback_map_ne_zero' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms AlgebraicGeometry.Scheme.Modules.sheafHasRank_cokernel_of_pullback_map_ne_zero

/--
info: 'AlgebraicGeometry.Scheme.Modules.pullback_map_f_ne_zero_of_shortExact' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms AlgebraicGeometry.Scheme.Modules.pullback_map_f_ne_zero_of_shortExact

/--
info: 'AlgebraicGeometry.Scheme.Modules.pullback_map_ne_zero_of_isAlgClosed' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms AlgebraicGeometry.Scheme.Modules.pullback_map_ne_zero_of_isAlgClosed

/--
info: 'AlgebraicGeometry.Scheme.Modules.Invertible.geometricFibreRegular_of_isIntegral_of_fibre_ne_zero' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms
  AlgebraicGeometry.Scheme.Modules.Invertible.geometricFibreRegular_of_isIntegral_of_fibre_ne_zero

/--
info: 'AlgebraicGeometry.Scheme.Modules.Invertible.isRelativeEffectiveCartier_zeroInclusion_of_geometricallyIntegral' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms
  AlgebraicGeometry.Scheme.Modules.Invertible.isRelativeEffectiveCartier_zeroInclusion_of_geometricallyIntegral

/--
info: 'AlgebraicGeometry.Scheme.Cohomology.fibreCohomology_residueField_comparison' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms AlgebraicGeometry.Scheme.Cohomology.fibreCohomology_residueField_comparison

/--
info: 'AlgebraicGeometry.Scheme.Cohomology.fibreCohomologyConcentrated_of_modulePointFiberCohomology' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms
  AlgebraicGeometry.Scheme.Cohomology.fibreCohomologyConcentrated_of_modulePointFiberCohomology

/--
info: 'AlgebraicGeometry.Scheme.Cohomology.isClopen_setOf_modulePointFiberCohomologyDimension_zero_eq' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms
  AlgebraicGeometry.Scheme.Cohomology.isClopen_setOf_modulePointFiberCohomologyDimension_zero_eq

/--
info: 'AlgebraicGeometry.Scheme.Cohomology.fibreCohomologyConcentrated_pullback_of_range_subset' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms
  AlgebraicGeometry.Scheme.Cohomology.fibreCohomologyConcentrated_pullback_of_range_subset

/--
info: 'AlgebraicGeometry.Scheme.Cohomology.sheafHasRank_and_isIso_moduleBaseChangeMap_of_modulePointFiberCohomology' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms
  AlgebraicGeometry.Scheme.Cohomology.sheafHasRank_and_isIso_moduleBaseChangeMap_of_modulePointFiberCohomology

/--
info: 'AlgebraicGeometry.Scheme.Modules.Invertible.pullback_map_sectionContraction_ne_zero' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms AlgebraicGeometry.Scheme.Modules.Invertible.pullback_map_sectionContraction_ne_zero

/--
info: 'AlgebraicGeometry.Scheme.Modules.Invertible.isRelativeEffectiveCartier_zeroInclusion_sectionContraction_of_geometricallyIntegral' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms
  AlgebraicGeometry.Scheme.Modules.Invertible.isRelativeEffectiveCartier_zeroInclusion_sectionContraction_of_geometricallyIntegral
