/-
Copyright (c) 2026 kangxyz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/

module

public import Aglib.AlgebraicGeometry.Cohomology.BaseChange.LocallyNoetherian
public import Aglib.AlgebraicGeometry.Cohomology.BaseChange.HigherDirectImage.Nonflat.Affine
public import Aglib.AlgebraicGeometry.Modules.BaseChange.Affine.Square
public import Aglib.Algebra.Homology.FiniteProjective.SingleModel
public import Aglib.Algebra.Homology.FiniteProjective.BaseChange
public import Aglib.Algebra.Homology.CochainComplex.ProjectiveCokernel
public import Aglib.Algebra.Category.ModuleCat.ChangeOfRings.Flat
public import Aglib.Algebra.Category.ModuleCat.ChangeOfRings.Algebra
public import Aglib.AlgebraicGeometry.Cohomology.Proper.FiniteModel
public import Aglib.AlgebraicGeometry.Cohomology.FiniteModel.BaseChangeCriterion
public import Aglib.AlgebraicGeometry.Cohomology.BaseChange.Relative
public import Mathlib.RingTheory.Flat.FaithfullyFlat.Basic
public import Mathlib.RingTheory.LocalProperties.Submodule
public import Mathlib.RingTheory.Localization.BaseChange
public import Aglib.AlgebraicGeometry.Cohomology.Functoriality.Modules.Isomorphism
public import Aglib.AlgebraicGeometry.Cohomology.DirectImage.Proper.Grauert
public import Aglib.AlgebraicGeometry.Modules.QuasiCoherent.FiniteType.FinitePresentation
public import Aglib.AlgebraicGeometry.Cohomology.BaseChange.HigherDirectImage.Nonflat.Cartesian
public import Aglib.AlgebraicGeometry.Cohomology.BaseChange.HigherDirectImage.Nonflat.Charts
public import Aglib.AlgebraicGeometry.Cohomology.BaseChange.HigherDirectImage.Nonflat.ChartCover
public import Aglib.AlgebraicGeometry.Modules.BaseChange.Composition
public import Aglib.AlgebraicGeometry.Modules.BaseChange.OpenImmersion.Pullback
public import Aglib.AlgebraicGeometry.Modules.Locality.Exactness
public import Aglib.AlgebraicGeometry.Modules.Flat.Relative.Coproduct
public import Aglib.AlgebraicGeometry.Modules.Flat.Relative.Unit
public import Aglib.AlgebraicGeometry.Modules.Flat.Generic.Spec

/-!
# Proper rank and original base change over locally Noetherian bases

The original geometric-fibre concentration hypothesis supplies finite local
rank and the original ordinary moduleBaseChangeMap for every change of base.
Only the original base is locally Noetherian; it may be nonreduced.

Native source basis: Aglib b001ca8814edba7b56866202765094b724ad0c9e.
The affine scalar proof uses Proper/FiniteModel:63-91, FiniteModel/BaseChangeCriterion:46-72,
FiniteProjective/SingleModel:118-211, and CochainComplex/ProjectiveCokernel:109-155.
The actual degree-zero mate is identified using DirectImage/Affine/Cohomology:328-336,
Nonflat/Affine:203-227, and Modules/BaseChange/Affine/Square:222-236. Ordinary cartesian
pasting and affine open locality globalize this same map. The rank conclusion uses
Modules/LocallyFree/Rank:140-143 after obtaining actual finite local bases.
-/


/-!
Native migration from `R5Lab.Aglib.AlgebraicGeometry.Cohomology.BaseChange.NoetherianPushforward`
at R5 revision
`f8a3314ddecffcada2ec721d26d56a937bed9690`, SHA-256
`9978961754cc04a3fc231dea67c67f79fb774ff6a76b6ae2e11d2f2ac16b2c6c`.
Original objects, maps, universes and explicit hypotheses are retained.
Native providers replace duplicate implementations.
-/

@[expose] public section

noncomputable section
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

universe u
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Opposite HomologicalComplex
open scoped TensorProduct ChangeOfRings

namespace AlgebraicGeometry.Scheme.Cohomology

private theorem moduleCohomologyMapAlong_equivZero_app
    {X Y : Scheme.{u}} (p : Y ⟶ X) {M : X.Modules} {N : Y.Modules}
    (ψ : M ⟶ (Scheme.Modules.pushforward p).obj N)
    (x : Sheaf.H.{u + 1} (moduleAddSheaf X M) 0) :
    Sheaf.H.equiv₀ (moduleAddSheaf Y N) isTerminalTop
        (moduleCohomologyMapAlong p ψ 0 x) =
      ψ.app ⊤ (Sheaf.H.equiv₀ (moduleAddSheaf X M) isTerminalTop x) := by
  rw [moduleCohomologyMapAlong_equiv₀]
  simp [pushforwardSectionsIso, modulePushforwardAddSheafIso]
  rfl

/-- The affine higher-image section comparison in degree zero is the ordinary
section map of the canonical right-derived-zero isomorphism. -/
theorem moduleHigherDirectImageAffineSectionsLinearEquiv_zero_apply
    {R : Type u} [CommRing R] {X : Scheme.{u}}
    (f : X ⟶ Spec (CommRingCat.of R)) [QuasiCompact f] [QuasiSeparated f]
    (M : X.Modules) [M.IsQuasicoherent]
    (x : moduleSpecΓFunctor.obj
      (((Scheme.Modules.pushforward f).rightDerived 0).obj M)) :
    Sheaf.H.equiv₀ (moduleAddSheaf X M) isTerminalTop
        (moduleHigherDirectImageAffineSectionsLinearEquiv f M (injectiveResolution M) 0 x) =
      ((Scheme.Modules.pushforward f).rightDerivedZeroIsoSelf.hom.app M).app ⊤ x := by
  let F := Scheme.Modules.pushforward f
  let π := F.rightDerivedZeroIsoSelf.hom.app M
  let z := F.toRightDerivedZero.app M
  have hx : moduleSpecΓFunctor.map z
      (moduleSpecΓFunctor.map π x) = x := by
    let G := moduleSpecΓFunctor (R := CommRingCat.of R)
    have hid : G.map π ≫ G.map z = 𝟙 _ := by
      rw [← G.map_comp]
      change G.map (F.rightDerivedZeroIsoSelf.hom.app M ≫ F.toRightDerivedZero.app M) = 𝟙 _
      rw [F.rightDerivedZeroIsoSelf_hom_inv_id_app]
      exact G.map_id _
    exact ConcreteCategory.congr_hom hid x
  have h := moduleHigherDirectImageAffineSectionsLinearEquiv_toRightDerivedZero f M
    (injectiveResolution M) (moduleSpecΓFunctor.map π x)
  rw [hx] at h
  exact h

end AlgebraicGeometry.Scheme.Cohomology

namespace AlgebraicGeometry.Scheme.Modules

open Cohomology

/-- The degree-zero higher-image comparison for a commuting affine-base
square is the original ordinary mate conjugated by the canonical R0 maps. -/
theorem higherDirectImageAffineMap_unit_zero_eq_square
    {R S : Type u} [CommRing R] [CommRing S] {X Y : Scheme.{u}}
    (a : Y ⟶ X) (b : Y ⟶ Spec (CommRingCat.of S))
    (f : X ⟶ Spec (CommRingCat.of R)) (σ : R →+* S)
    [QuasiCompact f] [QuasiSeparated f] [QuasiCompact b] [QuasiSeparated b]
    (w : a ≫ f = b ≫ Spec.map (CommRingCat.ofHom σ)) (M : X.Modules) [M.IsQuasicoherent] :
    higherDirectImageAffineMap (M := M) (N := (pullback a).obj M) a b f (CommRingCat.ofHom σ) w
        ((pullbackPushforwardAdjunction a).unit.app M) 0 =
      (pullback (Spec.map (CommRingCat.ofHom σ))).map
          ((pushforward f).rightDerivedZeroIsoSelf.hom.app M) ≫
        BaseChange.Affine.Square.moduleSquareBaseChangeMap a b f
          (Spec.map (CommRingCat.ofHom σ)) w M ≫
        (pushforward b).toRightDerivedZero.app ((pullback a).obj M) := by
  let g := Spec.map (CommRingCat.ofHom σ)
  let N := (pullback a).obj M
  let π := (pushforward f).rightDerivedZeroIsoSelf.hom.app M
  let z := (pushforward b).toRightDerivedZero.app N
  let π' := (pushforward b).rightDerivedZeroIsoSelf.hom.app N
  let β : (pullback g).obj ((pushforward f).obj M) ⟶ (pushforward b).obj N :=
    BaseChange.Affine.Square.moduleSquareBaseChangeMap a b f g w M
  let k := (pullback g).map π ≫ β ≫ z
  let : (((pushforward f).rightDerived 0).obj M).IsQuasicoherent :=
    moduleHigherDirectImageAffine_isQuasicoherent f M 0
  change higherDirectImageAffineMap (M := M) (N := N) a b f (CommRingCat.ofHom σ) w
    ((pullbackPushforwardAdjunction a).unit.app M) 0 = k
  symm
  apply higherDirectImageAffineMap_eq_of_one_tmul (M := M) (N := N)
    a b f (CommRingCat.ofHom σ) w
    ((pullbackPushforwardAdjunction a).unit.app M) 0 k
  intro _ x
  apply (Sheaf.H.equiv₀ (moduleAddSheaf Y N) isTerminalTop).injective
  rw [moduleCohomologyMapAlong_equivZero_app]
  rw [moduleHigherDirectImageAffineSectionsLinearEquiv_zero_apply,
    moduleHigherDirectImageAffineSectionsLinearEquiv_zero_apply]
  let y := (affinePullbackGlobalSectionsIso (CommRingCat.ofHom σ)
    (((pushforward f).rightDerived 0).obj M)).hom ((1 : S) ⊗ₜ[R,σ] x)
  have hzπ : z ≫ π' = 𝟙 ((pushforward b).obj N) :=
    (pushforward b).rightDerivedZeroIsoSelf_inv_hom_id_app N
  have hk : k ≫ π' = (pullback g).map π ≫ β := by
    calc
      k ≫ π' = ((pullback g).map π ≫ β) ≫ (z ≫ π') := by
        simp only [k, Category.assoc]
      _ = ((pullback g).map π ≫ β) ≫ 𝟙 ((pushforward b).obj N) :=
        congrArg (fun t => ((pullback g).map π ≫ β) ≫ t) hzπ
      _ = _ := Category.comp_id _
  have hky := congrArg (fun φ => moduleSpecΓFunctor.map φ y) hk
  simp only [Functor.map_comp, ConcreteCategory.comp_apply] at hky
  change moduleSpecΓFunctor.map π' (moduleSpecΓFunctor.map k y) = _
  rw [hky]
  dsimp only [y]
  rw [affinePullbackGlobalSectionsIso_one_tmul]
  have hn := congrArg (fun φ => φ.app ⊤ x)
    ((pullbackPushforwardAdjunction g).unit.naturality π)
  change ((pullbackPushforwardAdjunction g).unit.app ((pushforward f).obj M)).app ⊤
      (π.app ⊤ x) =
    ((pullback g).map π).app ⊤
      (((pullbackPushforwardAdjunction g).unit.app
        (((pushforward f).rightDerived 0).obj M)).app ⊤ x) at hn
  change β.app ⊤ (((pullback g).map π).app ⊤
    (((pullbackPushforwardAdjunction g).unit.app
      (((pushforward f).rightDerived 0).obj M)).app ⊤ x)) = _
  rw [← hn]
  exact BaseChange.Affine.Square.moduleSquareBaseChangeMap_unit_appTop
    a b f g w M (π.app ⊤ x)


/-- In degree zero the native affine higher-image base-change map is exactly the
original ordinary adjunction mate conjugated by the canonical derived-zero maps.
The new scalar ring and the scalar map are arbitrary. -/
theorem higherDirectImageAffineBaseChangeMap_zero_eq_ordinary
    {R S : Type u} [CommRing R] [CommRing S] {X : Scheme.{u}}
    (f : X ⟶ Spec (CommRingCat.of R)) [QuasiCompact f] [QuasiSeparated f]
    (σ : R →+* S) (M : X.Modules) [M.IsQuasicoherent] :
    higherDirectImageAffineBaseChangeMap f σ 0 M =
      (pullback (Spec.map (CommRingCat.ofHom σ))).map
          ((pushforward f).rightDerivedZeroIsoSelf.hom.app M) ≫
        moduleBaseChangeMap f (Spec.map (CommRingCat.ofHom σ)) M ≫
        (pushforward (Limits.pullback.snd f (Spec.map (CommRingCat.ofHom
            σ)))).toRightDerivedZero.app
          ((pullback (Limits.pullback.fst f (Spec.map (CommRingCat.ofHom σ)))).obj M) := by
  simpa only [higherDirectImageAffineBaseChangeMap,
    BaseChange.Affine.Square.moduleSquareBaseChangeMap_eq] using
      (higherDirectImageAffineMap_unit_zero_eq_square
        (Limits.pullback.fst f (Spec.map (CommRingCat.ofHom σ)))
        (Limits.pullback.snd f (Spec.map (CommRingCat.ofHom σ)))
        f σ Limits.pullback.condition M)

/-- An invertible ORIGINAL scalar cohomology comparison in degree zero makes
the ORIGINAL ordinary sheaf mate invertible over affine bases. -/
theorem moduleBaseChangeMap_isIso_of_scalar_cohomology_zero
    {R S : Type u} [CommRing R] [CommRing S] {X : Scheme.{u}}
    (f : X ⟶ Spec (CommRingCat.of R)) [QuasiCompact f] [QuasiSeparated f]
    (σ : R →+* S) (M : X.Modules) [M.IsQuasicoherent]
    (h : IsIso (moduleCohomologyBaseChangeMap f σ M 0)) :
    IsIso (moduleBaseChangeMap f (Spec.map (CommRingCat.ofHom σ)) M) := by
  have hh := higherDirectImageAffineBaseChangeMap_isIso f σ 0 M h
  rw [higherDirectImageAffineBaseChangeMap_zero_eq_ordinary] at hh
  let g := Spec.map (CommRingCat.ofHom σ)
  let π := (pullback g).map ((pushforward f).rightDerivedZeroIsoSelf.hom.app M)
  let z := (pushforward (Limits.pullback.snd f g)).toRightDerivedZero.app
    ((pullback (Limits.pullback.fst f g)).obj M)
  have : IsIso (moduleBaseChangeMap f g M ≫ z) := IsIso.of_isIso_comp_left π _
  exact IsIso.of_isIso_comp_right _ z

end AlgebraicGeometry.Scheme.Modules

namespace CochainComplex

private theorem isZero_homology_of_field_extension
    {k K : Type u} [Field k] [Field K] (σ : k →+* K)
    (L : CochainComplex (ModuleCat.{u} k) ℤ) (i : ℤ)
    (hz : IsZero ((((ModuleCat.extendScalars σ).mapHomologicalComplex (.up ℤ)).obj L).homology i)) :
    IsZero (L.homology i) := by
  let := σ.toAlgebra
  have hσ : σ.Flat := by change Module.Flat k K; infer_instance
  let F := ModuleCat.extendScalars σ
  let : PreservesFiniteLimits F := ModuleCat.extendScalars_preservesFiniteLimits_of_flat σ hσ
  let : PreservesFiniteColimits F := ModuleCat.extendScalars_preservesFiniteColimits_of_flat σ hσ
  let e := (L.sc i).mapHomologyIso F
  have hz' : IsZero (F.obj (L.homology i)) := hz.of_iso e.symm
  have ht : Subsingleton (K ⊗[k] (L.homology i)) := ModuleCat.subsingleton_of_isZero hz'
  let : Subsingleton (L.homology i) :=
    (Module.FaithfullyFlat.subsingleton_tensorProduct_iff_right k K).mp ht
  exact ModuleCat.isZero_of_subsingleton _

/-- Vanishing after algebraically closed extensions detects positive homology
over every field, using exactness and faithful flatness of field extensions. -/
theorem isZero_field_homology_of_geometric_vanishing
    {A : Type u} [CommRing A] (P : CochainComplex (ModuleCat.{u} A) ℤ)
    (hgeom : ∀ (K : Type u) [Field K] [IsAlgClosed K] (σ : A →+* K)
      (q : ℕ), 0 < q → IsZero
        ((((ModuleCat.extendScalars σ).mapHomologicalComplex (.up ℤ)).obj P).homology (q : ℤ)))
    (k : Type u) [Field k] (ρ : A →+* k) (q : ℕ) (hq : 0 < q) :
    IsZero ((((ModuleCat.extendScalars ρ).mapHomologicalComplex (.up ℤ)).obj P).homology (q :
        ℤ)) := by
  let K := AlgebraicClosure k
  let τ := algebraMap k K
  let L := ((ModuleCat.extendScalars ρ).mapHomologicalComplex (.up ℤ)).obj P
  let e := (Functor.mapHomologicalComplexCompIso (ModuleCat.extendScalarsComp ρ τ).symm
    (.up ℤ)).app P
  have hz := hgeom K (τ.comp ρ) q hq
  have hz' : IsZero ((((ModuleCat.extendScalars τ).mapHomologicalComplex (.up ℤ)).obj L).homology
      (q : ℤ)) :=
    hz.of_iso ((homologyFunctor (ModuleCat.{u} K) (.up ℤ) (q : ℤ)).mapIso e)
  exact isZero_homology_of_field_extension τ L (q : ℤ) hz'

/-- A bounded finite-projective complex with vanishing positive geometric
fibres has vanishing positive homology over the original ring. The argument
uses native local residue concentration, not a reduced-base dimension test. -/
theorem isZero_homology_of_geometric_vanishing
    {A : Type u} [CommRing A] (P : CochainComplex (ModuleCat.{u} A) ℤ) (n : ℕ)
    [P.IsStrictlyGE 0] [P.IsStrictlyLE (n : ℤ)]
    [∀ i, Module.Finite A (P.X i)] [∀ i, Module.Projective A (P.X i)]
    (hgeom : ∀ (K : Type u) [Field K] [IsAlgClosed K] (σ : A →+* K)
      (q : ℕ), 0 < q → IsZero
        ((((ModuleCat.extendScalars σ).mapHomologicalComplex (.up ℤ)).obj P).homology (q : ℤ)))
    (q : ℕ) (hq : 0 < q) : IsZero (P.homology (q : ℤ)) := by
  apply ModuleCat.isZero_iff_subsingleton.mpr
  apply Module.subsingleton_of_localization_maximal (R := A)
    (fun m => Localization.AtPrime m ⊗[A] (P.homology (q : ℤ)))
    (fun m => TensorProduct.mk A (Localization.AtPrime m) (P.homology (q : ℤ)) 1)
  intro m hm
  let R := Localization.AtPrime m
  let ρ := algebraMap A R
  let L : CochainComplex (ModuleCat.{u} R) ℤ :=
    ((ModuleCat.extendScalars ρ).mapHomologicalComplex (.up ℤ)).obj P
  let (i : ℤ) : Module.Finite R (L.X i) := finite_X_extendScalars ρ P i
  let (i : ℤ) : Module.Projective R (L.X i) := projective_X_extendScalars ρ P i
  let k := IsLocalRing.ResidueField R
  let τ := algebraMap R k
  let Q : CochainComplex (ModuleCat.{u} k) ℤ :=
    ((ModuleCat.extendScalars τ).mapHomologicalComplex (.up ℤ)).obj L
  have hres : ∀ i : ℤ, i ≠ 0 → IsZero (Q.homology i) := by
    intro i hi
    by_cases hneg : i < 0
    · exact Q.isZero_of_isGE 0 i (by omega)
    · let j := i.toNat
      have hj : (j : ℤ) = i := by dsimp [j]; omega
      have hjpos : 0 < j := by omega
      rw [← hj]
      let e := (Functor.mapHomologicalComplexCompIso
        (ModuleCat.extendScalarsComp ρ τ).symm (.up ℤ)).app P
      exact (P.isZero_field_homology_of_geometric_vanishing hgeom k (τ.comp ρ) j hjpos).of_iso
        ((homologyFunctor (ModuleCat.{u} k) (.up ℤ) (j : ℤ)).mapIso e)
  have hz : IsZero (L.homology (q : ℤ)) :=
    isZero_homology_of_residue_concentration 0 (n : ℤ) L hres (q : ℤ) (by omega)
  have hρ : ρ.Flat := RingHom.flat_algebraMap_iff.mpr inferInstance
  let F := ModuleCat.extendScalars ρ
  let : PreservesFiniteLimits F := ModuleCat.extendScalars_preservesFiniteLimits_of_flat ρ hρ
  let : PreservesFiniteColimits F := ModuleCat.extendScalars_preservesFiniteColimits_of_flat ρ hρ
  let e := (P.sc (q : ℤ)).mapHomologyIso F
  let t := ModuleCat.extendScalarsAlgebraObjIso A R (P.homology (q : ℤ))
  exact ModuleCat.subsingleton_of_isZero ((hz.of_iso e.symm).of_iso t.symm)

end CochainComplex

namespace AlgebraicGeometry.Scheme.Cohomology

open Scheme.Modules.QuasiCoherent

/-- Geometric concentration gives finite projective original degree-zero
cohomology and every original scalar base-change comparison over a Noetherian
affine base, which may be nonreduced. No local-ring condition is imposed. -/
theorem properCohomology_of_geometric_concentration
    {A : Type u} [CommRing A] [IsNoetherianRing A]
    {X : Scheme.{u}} (f : X ⟶ Spec (CommRingCat.of A)) [IsProper f]
    (M : X.Modules) (hM : affineLocallyFiniteType X M)
    (hflat : Scheme.Modules.relativeFlat f M) (r : ℕ)
    (hgeom : FibreCohomologyConcentrated f M r) :
    let α := f.appTop.hom.comp (Scheme.ΓSpecIso (CommRingCat.of A)).inv.hom
    letI := moduleCohomologyModuleOfHom X α M 0
    Module.Finite A (Sheaf.H.{u + 1} (moduleAddSheaf X M) 0) ∧
      Module.Projective A (Sheaf.H.{u + 1} (moduleAddSheaf X M) 0) ∧
      ∀ (B : Type u) [CommRing B] (σ : A →+* B) (q : ℕ),
        IsIso (moduleCohomologyBaseChangeMap f σ M q) := by
  let : X.IsSeparated := ⟨by rw [← terminal.comp_from f]; infer_instance⟩
  let : M.IsQuasicoherent := quasicoherent_of_affineCharts M (fun R j _ => (hM R j).1)
  obtain ⟨n, U, hU, hcover, ⟨D⟩⟩ :=
    exists_finiteCechCohomologyModel_of_proper (CommRingCat.of A) f M hM hflat
  let (i : ℤ) : Module.Finite A (D.complex.X i) := D.finite_X i
  let (i : ℤ) : Module.Projective A (D.complex.X i) := D.projective_X i
  let : D.complex.IsStrictlyGE 0 := D.lowerBound
  let : D.complex.IsStrictlyLE (n : ℤ) := D.upperBound
  have hmodel : ∀ (K : Type u) [Field K] [IsAlgClosed K] (σ : A →+* K)
      (q : ℕ), 0 < q → IsZero
        ((((ModuleCat.extendScalars σ).mapHomologicalComplex (.up ℤ)).obj D.complex).homology
          (q : ℤ)) := by
    intro K _ _ σ q hq
    let : Subsingleton (Sheaf.H.{u + 1}
        (moduleAddSheaf (Limits.pullback f (Spec.map (CommRingCat.ofHom σ)))
          ((Scheme.Modules.pullback
            (Limits.pullback.fst f (Spec.map (CommRingCat.ofHom σ)))).obj M)) q) :=
      (hgeom K (Spec.map (CommRingCat.ofHom σ))).2 q hq
    let : Subsingleton
        ((((ModuleCat.extendScalars σ).mapHomologicalComplex (.up ℤ)).obj D.complex).homology
          (q : ℤ)) :=
      (D.baseChangeCohomologyLinearEquiv hU hcover Equiv.ulift hflat σ q).injective.subsingleton
    exact ModuleCat.isZero_of_subsingleton _
  have hvan (q : ℕ) (hq : q ≠ 0) : IsZero (D.complex.homology (q : ℤ)) :=
    D.complex.isZero_homology_of_geometric_vanishing n hmodel q (Nat.pos_of_ne_zero hq)
  let : Module.Projective A (D.complex.homology 0) :=
    D.complex.projective_homology_zero_of_vanishing n hvan
  let α := f.appTop.hom.comp (Scheme.ΓSpecIso (CommRingCat.of A)).inv.hom
  let := moduleCohomologyModuleOfHom X α M 0
  dsimp only
  refine ⟨moduleCohomology_finite_of_proper A f M hM 0,
    Module.Projective.of_equiv (D.cohomologyLinearEquiv hU hcover Equiv.ulift 0), ?_⟩
  intro B _ σ q
  exact (D.moduleCohomologyBaseChangeMap_isIso_iff hU hcover Equiv.ulift hflat σ q).mpr
    (D.complex.extendScalarsHomologyMap_isIso_of_vanishing n hvan σ q)

end AlgebraicGeometry.Scheme.Cohomology

namespace AlgebraicGeometry.Scheme.Cohomology

/-- The actual geometric fibre concentration profile is preserved by arbitrary
base change. This only identifies iterated ordinary fibres and coefficients. -/
theorem FibreCohomologyConcentrated.pullback
    {X S T : Scheme.{u}} (f : X ⟶ S) (g : T ⟶ S) (M : X.Modules) (r : ℕ)
    (hM : FibreCohomologyConcentrated f M r) :
    FibreCohomologyConcentrated (Limits.pullback.snd f g)
      ((Scheme.Modules.pullback (Limits.pullback.fst f g)).obj M) r := by
  intro K _ _ t
  let e := pullbackLeftPullbackSndIso f g t
  let p := Limits.pullback.fst f (t ≫ g)
  let a := Limits.pullback.fst (Limits.pullback.snd f g) t
  let c := Limits.pullback.fst f g
  let b := Limits.pullback.snd f (t ≫ g)
  let d := Limits.pullback.snd (Limits.pullback.snd f g) t
  let P := (Scheme.Modules.pullback p).obj M
  let N := (Scheme.Modules.pullback a).obj ((Scheme.Modules.pullback c).obj M)
  let C : (Scheme.Modules.pullback e.hom).obj P ≅ N :=
    (Scheme.Modules.pullbackComp e.hom p).app M ≪≫
      (Scheme.Modules.pullbackCongr (pullbackLeftPullbackSndIso_hom_fst f g t)).app M ≪≫
        ((Scheme.Modules.pullbackComp a c).app M).symm
  have hw : e.hom ≫ b = d := pullbackLeftPullbackSndIso_hom_snd f g t
  let α := b.appTop.hom.comp (Scheme.ΓSpecIso (CommRingCat.of K)).inv.hom
  let β := d.appTop.hom.comp (Scheme.ΓSpecIso (CommRingCat.of K)).inv.hom
  have hα : e.hom.appTop.hom.comp α = β.comp (RingHom.id K) := by
    dsimp only [α, β]
    rw [← hw, Scheme.Hom.comp_appTop]
    rfl
  let (q : ℕ) : Module K (Sheaf.H.{u + 1} (moduleAddSheaf _ P) q) :=
    moduleCohomologyModuleOfHom _ α P q
  let (q : ℕ) : Module K (Sheaf.H.{u + 1} (moduleAddSheaf _ N) q) :=
    moduleCohomologyModuleOfHom _ β N q
  let E (q : ℕ) := moduleCohomologyRestrictionIsoOfPullbackIso e.hom
    (RingHom.id K) α β hα P C q ≪≫
      ModuleCat.restrictScalarsId'App (RingHom.id K) rfl _
  have hr := (hM K (t ≫ g)).1
  refine ⟨?_, ?_⟩
  · exact (E 0).toLinearEquiv.finrank_eq.symm.trans hr
  · intro q hq
    let : Subsingleton (Sheaf.H.{u + 1} (moduleAddSheaf _ P) q) :=
      (hM K (t ≫ g)).2 q hq
    exact (E q).symm.toLinearEquiv.injective.subsingleton

end AlgebraicGeometry.Scheme.Cohomology

namespace AlgebraicGeometry.Scheme.Modules

open Cohomology QuasiCoherent

/-- Proper geometric concentration gives finite local freeness of the actual
ordinary pushforward over a locally Noetherian base, including nonreduced bases. -/
theorem pushforward_finiteLocallyFree_of_geometric_concentration
    {X S : Scheme.{u}} [IsLocallyNoetherian S]
    (f : X ⟶ S) [IsProper f] (M : X.Modules)
    (hM : affineLocallyFiniteType X M) (hflat : relativeFlat f M)
    (r : ℕ) (hgeom : FibreCohomologyConcentrated f M r) :
    IsFiniteLocallyFree S ((pushforward f).obj M) := by
  let H := ((pushforward f).rightDerived 0).obj M
  have hH : affineLocallyFiniteType S H := moduleHigherDirectImage_coherent_of_proper f M hM 0
  have hLF : IsFiniteLocallyFree S H := by
    let U := S.affineOpenCover
    apply finiteLocallyFree_of_affineCharts H U.X U.f (fun y => ⟨U.idx y, U.covers y⟩)
    intro i
    let A := U.X i
    let j := U.f i
    let : IsLocallyNoetherian (Spec A) := isLocallyNoetherian_of_isOpenImmersion j
    let : IsNoetherianRing A := isLocallyNoetherian_Spec.mp inferInstance
    let a := Limits.pullback.fst f j
    let b := Limits.pullback.snd f j
    let W := Limits.pullback f j
    let N := (pullback a).obj M
    let C := (restrictFunctorIsoPullback a).app M
    have hN : affineLocallyFiniteType W N :=
      (affineLocallyFiniteType W).prop_of_iso C (affineLocallyFiniteType_restrict a hM)
    let : N.IsQuasicoherent := quasicoherent_of_affineCharts N (fun B k _ => (hN B k).1)
    have hflatN : relativeFlat b N := relativeFlat_pullback_of_isOpenImmersion f j hflat
    have hgeomN : FibreCohomologyConcentrated b N r :=
      FibreCohomologyConcentrated.pullback f j M r hgeom
    let α := b.appTop.hom.comp (Scheme.ΓSpecIso A).inv.hom
    let := moduleCohomologyModuleOfHom W α N 0
    obtain ⟨_, hp, _⟩ := properCohomology_of_geometric_concentration (A := A) b N hN hflatN r hgeomN
    let : Module.Projective A (Sheaf.H.{u + 1} (moduleAddSheaf W N) 0) := hp
    let Hj := H.restrict j
    let E := (higherDirectImageOpenRestrictionIso a b f j
      (IsPullback.of_hasPullback f j) 0).app M ≪≫ ((pushforward b).rightDerived 0).mapIso C
    let EΓ := ((moduleSpecΓFunctor (R := A)).mapIso E).toLinearEquiv.trans
      (moduleHigherDirectImageAffineSectionsLinearEquiv (R := A) b N (injectiveResolution N) 0)
    let : Module.Projective A ((moduleSpecΓFunctor (R := A)).obj Hj) :=
      Module.Projective.of_equiv' EΓ.symm
    let : Module.Finite A ((moduleSpecΓFunctor (R := A)).obj Hj) := (hH A j).2
    let : Hj.IsQuasicoherent := (hH A j).1
    have hproj : IsFiniteLocallyFree (Spec A) (tilde ((moduleSpecΓFunctor (R := A)).obj Hj)) :=
      finiteLocallyFree_tilde_of_finite_projective A _
    let ε : tilde ((moduleSpecΓFunctor (R := A)).obj Hj) ⟶ Hj := Hj.fromTildeΓ
    let : IsIso ε := isIso_fromTildeΓ_of_isQuasicoherent Hj
    exact finiteLocallyFree_of_iso (h := hproj) (asIso ε)
  exact finiteLocallyFree_of_iso (h := hLF) ((pushforward f).rightDerivedZeroIsoSelf.app M)

end AlgebraicGeometry.Scheme.Modules

namespace AlgebraicGeometry.Scheme.Modules

open Cohomology QuasiCoherent


theorem cartesianBaseChangeMap_isIso_of_scalar_cohomology_zero
    {R S : Type u} [CommRing R] [CommRing S] {X Y : Scheme.{u}}
    (a : Y ⟶ X) (b : Y ⟶ Spec (CommRingCat.of S))
    (f : X ⟶ Spec (CommRingCat.of R)) (σ : R →+* S)
    [QuasiCompact f] [QuasiSeparated f]
    (h : IsPullback a b f (Spec.map (CommRingCat.ofHom σ)))
    (M : X.Modules) [M.IsQuasicoherent]
    (hβ : IsIso (moduleCohomologyBaseChangeMap f σ M 0)) :
    IsIso ((cartesianBaseChangeMap a b f (Spec.map (CommRingCat.ofHom σ)) h).app M) := by
  let : QuasiCompact b := MorphismProperty.of_isPullback h inferInstance
  let : QuasiSeparated b := MorphismProperty.of_isPullback h inferInstance
  have hs := (moduleCohomologyTensorMap_isIso_iff_baseChangeMap_of_isPullback
    a b f σ h M 0).mpr hβ
  have hh := higherDirectImageAffineMap_isIso (M := M) (N := (pullback a).obj M)
    a b f (CommRingCat.ofHom σ) h.w
    ((pullbackPushforwardAdjunction a).unit.app M) 0 hs
  rw [higherDirectImageAffineMap_unit_zero_eq_square] at hh
  let g := Spec.map (CommRingCat.ofHom σ)
  let π := (pullback g).map ((pushforward f).rightDerivedZeroIsoSelf.hom.app M)
  let z := (pushforward b).toRightDerivedZero.app ((pullback a).obj M)
  let β := BaseChange.Affine.Square.moduleSquareBaseChangeMap a b f g h.w M
  have : IsIso (β ≫ z) := IsIso.of_isIso_comp_left π _
  have hβ' : IsIso β := IsIso.of_isIso_comp_right _ z
  rw [cartesianBaseChangeMap_eq_counit]
  exact hβ'

/-- Affine scalar H0 comparisons detect invertibility of the original ordinary
sheaf mate, using only ordinary open base change and its pasting equation. -/
theorem moduleBaseChangeMap_isIso_of_affine_cohomology_zero
    {X S T : Scheme.{u}} (f : X ⟶ S) (g : T ⟶ S)
    [QuasiCompact f] [QuasiSeparated f] (M : X.Modules) [M.IsQuasicoherent]
    (hβ : ∀ C : Nonflat.AffineBaseChangeChart g,
      IsIso (moduleCohomologyBaseChangeMap (Limits.pullback.snd f C.source) C.scalar.hom
        ((pullback (Limits.pullback.fst f C.source)).obj M) 0)) :
    IsIso (moduleBaseChangeMap f g M) := by
  rw [moduleBaseChangeMap_eq_cartesianBaseChangeMap]
  let a := Limits.pullback.fst f g
  let b := Limits.pullback.snd f g
  let h := IsPullback.of_hasPullback f g
  let : QuasiCompact b := MorphismProperty.of_isPullback h inferInstance
  let : QuasiSeparated b := MorphismProperty.of_isPullback h inferInstance
  change IsIso ((cartesianBaseChangeMap a b f g h).app M)
  apply isIso_of_restrict_openCover
    (fun C : Nonflat.AffineBaseChangeChart g => Spec C.targetRing)
    (fun C => C.target) (Nonflat.affineBaseChangeCharts_cover g)
  intro C
  let j := C.source
  let v := C.target
  let s := Spec.map C.scalar
  let aU := Limits.pullback.fst f j
  let bU := Limits.pullback.snd f j
  let hU := IsPullback.of_hasPullback f j
  let c := Limits.pullback.fst b v
  let d := Limits.pullback.snd b v
  let hV := IsPullback.of_hasPullback b v
  let e := Nonflat.chartUpper a b f g h j v C.scalar C.comm
  have he : e ≫ aU = c ≫ a := Nonflat.chartUpper_fst a b f g h j v C.scalar C.comm
  have hlocal : IsPullback e d bU s :=
    Nonflat.chartUpper_isPullback a b f g h j v C.scalar C.comm
  let Hlocal := hlocal.paste_horiz hU
  let H := hV.paste_horiz h
  let N := (pullback aU).obj M
  let : N.IsQuasicoherent := quasicoherent_pullback aU M
  let : IsIso ((cartesianBaseChangeMap aU bU f j hU).app M) :=
    isIso_cartesianBaseChangeMap_of_isOpenImmersion aU bU f j hU M
  let : IsIso ((cartesianBaseChangeMap e d bU s hlocal).app N) :=
    cartesianBaseChangeMap_isIso_of_scalar_cohomology_zero e d bU C.scalar.hom hlocal N (hβ C)
  have hcomp := cartesianBaseChangeMap_comp aU bU f j hU e d s hlocal Hlocal M
  have houter : IsIso ((cartesianBaseChangeMap (e ≫ aU) d f (s ≫ j) Hlocal).app M) := by
    have : IsIso ((pullbackComp s j).hom.app ((pushforward f).obj M) ≫
        (cartesianBaseChangeMap (e ≫ aU) d f (s ≫ j) Hlocal).app M) := by
      rw [hcomp]
      infer_instance
    exact IsIso.of_isIso_comp_left ((pullbackComp s j).hom.app ((pushforward f).obj M)) _
  have htransport (a₁ a₂ : Limits.pullback b v ⟶ X) (g₁ g₂ : Spec C.targetRing ⟶ S)
      (ha : a₁ = a₂) (hg : g₁ = g₂)
      (H₁ : IsPullback a₁ d f g₁) (H₂ : IsPullback a₂ d f g₂) :
      IsIso ((cartesianBaseChangeMap a₁ d f g₁ H₁).app M) ↔
        IsIso ((cartesianBaseChangeMap a₂ d f g₂ H₂).app M) := by
    subst a₂
    subst g₂
    rfl
  have houter' : IsIso ((cartesianBaseChangeMap (c ≫ a) d f (v ≫ g) H).app M) :=
    (htransport (e ≫ aU) (c ≫ a) (s ≫ j) (v ≫ g) he C.comm Hlocal H).mp houter
  let : IsIso ((cartesianBaseChangeMap c d b v hV).app ((pullback a).obj M)) :=
    isIso_cartesianBaseChangeMap_of_isOpenImmersion c d b v hV ((pullback a).obj M)
  have hcomp' := cartesianBaseChangeMap_comp a b f g h c d v hV H M
  have : IsIso ((pullback v).map ((cartesianBaseChangeMap a b f g h).app M) ≫
      (cartesianBaseChangeMap c d b v hV).app ((pullback a).obj M) ≫
      (pushforward d).map ((pullbackComp c a).hom.app M)) := by
    rw [← hcomp']
    infer_instance
  have : IsIso ((pullback v).map ((cartesianBaseChangeMap a b f g h).app M) ≫
      (cartesianBaseChangeMap c d b v hV).app ((pullback a).obj M)) :=
    IsIso.of_isIso_comp_right _ ((pushforward d).map ((pullbackComp c a).hom.app M))
  have hp : IsIso ((pullback v).map ((cartesianBaseChangeMap a b f g h).app M)) :=
    IsIso.of_isIso_comp_right _ ((cartesianBaseChangeMap c d b v hV).app ((pullback a).obj M))
  exact (NatIso.isIso_map_iff (restrictFunctorIsoPullback v)
    ((cartesianBaseChangeMap a b f g h).app M)).mpr hp

/-- Proper geometric concentration over a locally Noetherian original base
makes the original ordinary base-change mate invertible for every new scheme. -/
theorem moduleBaseChangeMap_isIso_of_geometric_concentration
    {X S T : Scheme.{u}} [IsLocallyNoetherian S]
    (f : X ⟶ S) [IsProper f] (M : X.Modules)
    (hM : affineLocallyFiniteType X M) (hflat : relativeFlat f M)
    (r : ℕ) (hgeom : FibreCohomologyConcentrated f M r) (g : T ⟶ S) :
    IsIso (moduleBaseChangeMap f g M) := by
  let : M.IsQuasicoherent := quasicoherent_of_affineCharts M (fun A j _ => (hM A j).1)
  apply moduleBaseChangeMap_isIso_of_affine_cohomology_zero f g M
  intro C
  let A := C.sourceRing
  let j := C.source
  let : IsLocallyNoetherian (Spec A) := isLocallyNoetherian_of_isOpenImmersion j
  let : IsNoetherianRing A := isLocallyNoetherian_Spec.mp inferInstance
  let a := Limits.pullback.fst f j
  let b := Limits.pullback.snd f j
  let N := (pullback a).obj M
  have hN : affineLocallyFiniteType (Limits.pullback f j) N :=
    (affineLocallyFiniteType _).prop_of_iso ((restrictFunctorIsoPullback a).app M)
      (affineLocallyFiniteType_restrict a hM)
  have hflatN : relativeFlat b N := relativeFlat_pullback_of_isOpenImmersion f j hflat
  have hgeomN : FibreCohomologyConcentrated b N r :=
    FibreCohomologyConcentrated.pullback f j M r hgeom
  exact (properCohomology_of_geometric_concentration (A := A) b N hN hflatN r hgeomN).2.2
    C.targetRing C.scalar.hom 0

/-- The finite locally free ordinary pushforward has the original prescribed
geometric fibre rank, with literal rank-r local basis witnesses. -/
theorem pushforward_hasRank_of_geometric_concentration
    {X S : Scheme.{u}} [IsLocallyNoetherian S]
    (f : X ⟶ S) [IsProper f] (M : X.Modules)
    (hM : affineLocallyFiniteType X M) (hflat : relativeFlat f M)
    (r : ℕ) (hgeom : FibreCohomologyConcentrated f M r) :
    SheafHasRank ((pushforward f).obj M) r := by
  let : IsFiniteLocallyFree S ((pushforward f).obj M) :=
    pushforward_finiteLocallyFree_of_geometric_concentration f M hM hflat r hgeom
  apply (sheafHasRank_iff_geometric_fibres ((pushforward f).obj M) r).mpr
  intro K _ _ t
  let : IsIso (moduleBaseChangeMap f t M) :=
    moduleBaseChangeMap_isIso_of_geometric_concentration f M hM hflat r hgeom t
  let b := Limits.pullback.snd f t
  let N := (pullback (Limits.pullback.fst f t)).obj M
  let E : moduleFibre K ((pushforward f).obj M) t ≃ₗ[K] fibreCohomology f M K t 0 :=
    (fieldSectionsIso K (asIso (moduleBaseChangeMap f t M))).trans
      (moduleH0Equiv (Over.mk b) N).symm
  exact E.finrank_eq.trans (hgeom K t).1

/-- A locally free coefficient is flat over the base of a flat morphism. -/
theorem relativeFlat_of_isLocallyFree_of_flat
    {X S : Scheme.{u}} (f : X ⟶ S) [Flat f] (M : X.Modules)
    [SheafOfModules.IsLocallyFree.{u} M] : relativeFlat f M := by
  obtain ⟨q, hq⟩ := SheafOfModules.IsLocallyFree.exists_isLocallyFreeData (M := M)
  intro x
  obtain ⟨i, hi⟩ := (_root_.Opens.coversTop_iff X q.X).mp q.coversTop |>.exists_mem x
  let U : X.Opens := q.X i
  let E : M.restrict U.ι ≅
      SheafOfModules.free (R := U.toScheme.ringCatSheaf) (q.generators i).I :=
    (restrictFunctorIsoPullback U.ι).app M ≪≫ (localBasisRestrictedIso M q hq i).symm
  have hfree : relativeFlat (U.ι ≫ f)
      (SheafOfModules.free (R := U.toScheme.ringCatSheaf) (q.generators i).I) :=
    relativeFlat_coproduct (U.ι ≫ f)
      (fun _ : (q.generators i).I => SheafOfModules.unit U.toScheme.ringCatSheaf)
      (fun _ => relativeFlat_unit_of_flat (U.ι ≫ f))
  have hlocal : relativeFlat (U.ι ≫ f) (M.restrict U.ι) :=
    relativeFlat_of_iso (U.ι ≫ f) E hfree
  exact flat_stalk_of_flat_stalk_restrict U.ι f M ⟨x, hi⟩ (hlocal ⟨x, hi⟩)

end AlgebraicGeometry.Scheme.Modules

namespace AlgebraicGeometry.Scheme.Cohomology

/-- The original rank and canonical-mate conclusion on a locally Noetherian
original base. Nonreduced bases and every arbitrary new target are retained.

The finite-presentation scope instance is intentionally retained to match
the proper/finite-presentation/flat interface used by `directImageLineBundle`;
the Noetherian proof does not need this instance. -/
theorem localFreeCohomologyBaseChange_of_isLocallyNoetherian
    {X S : Scheme.{u}} [IsLocallyNoetherian S]
    (f : X ⟶ S) [IsProper f] [_finitePresentationScope : LocallyOfFinitePresentation f]
    [Flat f] (M : X.Modules) [SheafOfModules.IsLocallyFree.{u} M] [M.IsFinitePresentation]
    (r : ℕ) (hgeom : FibreCohomologyConcentrated f M r) :
    Modules.SheafHasRank ((Modules.pushforward f).obj M) r ∧
      ∀ (T : Scheme.{u}) (g : T ⟶ S), IsIso (Modules.moduleBaseChangeMap f g M) := by
  have hM := Modules.QuasiCoherent.affineLocallyFiniteType_of_finitePresentation M
  have hflat := Modules.relativeFlat_of_isLocallyFree_of_flat f M
  exact ⟨Modules.pushforward_hasRank_of_geometric_concentration f M hM hflat r hgeom,
    fun T g => Modules.moduleBaseChangeMap_isIso_of_geometric_concentration f M hM hflat r hgeom g⟩

end AlgebraicGeometry.Scheme.Cohomology
