/-
Copyright (c) 2026 algebraic-geometry contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.Modules.QuasiCoherent.Affine.ChartPullbackCoordinateSections
public import Aglib.AlgebraicGeometry.Modules.Locality.AffineChartRestriction
public import Aglib.AlgebraicGeometry.Modules.Locality.ChartSections
public import Aglib.AlgebraicGeometry.Modules.QuasiCoherent.Affine.ChartRestrictionCoordinates

/-! # Original coordinate units under affine-chart restriction

The section-restriction constructor is the original restriction unit followed
by the native affine pushforward and chart-rebracketing comparisons. Its
compatibility with pullback coordinate units is proved for arbitrary target
chart rings and coefficients, before any concrete geometry is substituted.
-/

@[expose] public noncomputable section
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

universe u
open CategoryTheory Opposite
open scoped TensorProduct

namespace AlgebraicGeometry.Scheme.Modules

/-- Original restriction of sections between the supplied commuting affine charts. -/
def affineChartSectionRestriction {Z : Scheme.{u}} {R S : CommRingCat.{u}}
    (φ : R ⟶ S) (c : Spec R ⟶ Z) (d : Spec S ⟶ Z)
    [IsOpenImmersion c] [IsOpenImmersion d] [IsOpenImmersion (Spec.map φ)]
    (hc : Spec.map φ ≫ c = d) (Q : Z.Modules) :
    moduleSpecΓFunctor.obj (Q.restrict c) → moduleSpecΓFunctor.obj (Q.restrict d) :=
  fun x => moduleSpecΓFunctor.map (affineChartRestrictionIso φ c d hc Q).hom
    ((pushforwardGlobalSectionsIso φ).hom.app ((Q.restrict c).restrict (Spec.map φ))
      (moduleSpecΓFunctor.map ((restrictAdjunction (Spec.map φ)).unit.app (Q.restrict c)) x))

/-- The shared chart section restriction is the original presheaf restriction. -/
theorem affineChartSectionRestriction_eq_restriction
    {Z : Scheme.{u}} {R S : CommRingCat.{u}}
    (φ : R ⟶ S) (c : Spec R ⟶ Z) (d : Spec S ⟶ Z)
    [IsOpenImmersion c] [IsOpenImmersion d] [IsOpenImmersion (Spec.map φ)]
    (hc : Spec.map φ ≫ c = d) (Q : Z.Modules)
    (x : moduleSpecΓFunctor.obj (Q.restrict c)) :
    affineChartSectionRestriction φ c d hc Q x =
      Q.presheaf.map (homOfLE (affineChart_image_le φ c d hc)).op x :=
  affineChartRestrictionIso_unit φ c d hc Q x

section Refinement

variable {R R' S T : Type u} [CommRing R] [CommRing R'] [CommRing S] [CommRing T]
  [Algebra R S] [Algebra R' T]
  {X Z : Scheme.{u}} (p : Z ⟶ X)
  (j : Spec (CommRingCat.of R) ⟶ X) (j' : Spec (CommRingCat.of R') ⟶ X)
  [IsOpenImmersion j] [IsOpenImmersion j']
  (c : Spec (CommRingCat.of S) ⟶ Z) (d : Spec (CommRingCat.of T) ⟶ Z)
  [IsOpenImmersion c] [IsOpenImmersion d]
  (φ : CommRingCat.of S ⟶ CommRingCat.of T) [IsOpenImmersion (Spec.map φ)]
  (hc : Spec.map φ ≫ c = d)
  (HU : c ≫ p = Spec.map (CommRingCat.ofHom (algebraMap R S)) ≫ j)
  (HV : d ≫ p = Spec.map (CommRingCat.ofHom (algebraMap R' T)) ≫ j')
  (M : X.Modules) [M.IsQuasicoherent]
  {N : ModuleCat.{u} R} {N' : ModuleCat.{u} R'}
  (e : moduleSpecΓFunctor.obj (M.restrict j) ≅ N)
  (e' : moduleSpecΓFunctor.obj (M.restrict j') ≅ N') (r : N → N') (m : N)

/-- The original target-chart restriction preserves unit coordinates under
specified source coordinates and a specified source section restriction. -/
def chartPullbackCoordinatesRefinementEquation : Prop :=
  affineChartSectionRestriction φ c d hc ((pullback p).obj M)
      ((chartPullbackCoordinatesIso p j c HU M e).inv ((1 : S) ⊗ₜ[R] m)) =
    (chartPullbackCoordinatesIso p j' d HV M e').inv ((1 : T) ⊗ₜ[R'] r m)

/-- Source-coordinate compatibility gives the original target-chart restriction
identity before any chart rings or source coefficients are specialized. -/
theorem chartPullbackCoordinatesRefinementEquation_of_coordinates
    (ha : j' ''ᵁ (⊤ : (Spec (CommRingCat.of R')).Opens) ≤
      j ''ᵁ (⊤ : (Spec (CommRingCat.of R)).Opens))
    (hr : M.presheaf.map (homOfLE ha).op (e.inv m) = e'.inv (r m)) :
    chartPullbackCoordinatesRefinementEquation p j j' c d φ hc HU HV M e e' r m := by
  have hU := chartPullbackCoordinatesIso_inv_one_tmul p j c HU M e m
  have hV := chartPullbackCoordinatesIso_inv_one_tmul p j' d HV M e' (r m)
  have hu := congrArg (affineChartSectionRestriction φ c d hc ((pullback p).obj M)) hU
  have hs := affineChartSectionRestriction_eq_restriction φ c d hc ((pullback p).obj M)
    ((Nonflat.chartCoefficient p j c (Spec.map (CommRingCat.ofHom (algebraMap R S)))
      HU.symm ((pullbackPushforwardAdjunction p).unit.app M)).app ⊤ (e.inv m))
  have ht := Nonflat.chartCoefficient_top_restrict p j c
    (Spec.map (CommRingCat.ofHom (algebraMap R S))) j' d
    (Spec.map (CommRingCat.ofHom (algebraMap R' T))) HU.symm HV.symm ha
    (affineChart_image_le φ c d hc) ((pullbackPushforwardAdjunction p).unit.app M) (e.inv m)
  have he := congrArg
    ((Nonflat.chartCoefficient p j' d (Spec.map (CommRingCat.ofHom (algebraMap R' T)))
      HV.symm ((pullbackPushforwardAdjunction p).unit.app M)).app ⊤) hr
  have hresult := hu.trans (hs.trans (ht.trans (he.trans hV.symm)))
  exact hresult

end Refinement

variable {X Z : Scheme.{u}} (p : Z ⟶ X)
  (U V : X.affineOpens) (h : V.val ≤ U.val)
  {S T : Type u} [CommRing S] [CommRing T]
  [Algebra Γ(X, U) S] [Algebra Γ(X, V) T]
  (c : Spec (CommRingCat.of S) ⟶ Z) (d : Spec (CommRingCat.of T) ⟶ Z)
  [IsOpenImmersion c] [IsOpenImmersion d]
  (φ : CommRingCat.of S ⟶ CommRingCat.of T) [IsOpenImmersion (Spec.map φ)]
  (hc : Spec.map φ ≫ c = d)
  (HU : c ≫ p = Spec.map (CommRingCat.ofHom (algebraMap Γ(X, U) S)) ≫
    U.property.fromSpec)
  (HV : d ≫ p = Spec.map (CommRingCat.ofHom (algebraMap Γ(X, V) T)) ≫
    V.property.fromSpec)
  (M : X.Modules) [M.IsQuasicoherent]

/-- The original target-chart restriction preserves coordinate unit tensors
of the original source coefficient sections. -/
def chartPullbackCoordinatesRestrictionEquation (m : Γ(M, U)) : Prop :=
  chartPullbackCoordinatesRefinementEquation p U.property.fromSpec V.property.fromSpec
    c d φ hc HU HV M (affineChartΓIso U M) (affineChartΓIso V M)
    (fun x => M.presheaf.map (homOfLE h).op x) m

/-- The native pullback coordinates satisfy the original affine restriction
identity on every section, with no flatness or Cartesian hypothesis. -/
theorem chartPullbackCoordinatesRestrictionEquation_of_coordinates (m : Γ(M, U)) :
    chartPullbackCoordinatesRestrictionEquation p U V h c d φ hc HU HV M m := by
  have ha : V.property.fromSpec ''ᵁ (⊤ : (Spec Γ(X, V)).Opens) ≤
      U.property.fromSpec ''ᵁ (⊤ : (Spec Γ(X, U)).Opens) := by
    simpa only [Scheme.Hom.image_top_eq_opensRange, IsAffineOpen.opensRange_fromSpec] using h
  dsimp only [chartPullbackCoordinatesRestrictionEquation]
  refine chartPullbackCoordinatesRefinementEquation_of_coordinates p U.property.fromSpec
    V.property.fromSpec c d φ hc HU HV M (affineChartΓIso U M) (affineChartΓIso V M)
    (fun x => M.presheaf.map (homOfLE h).op x) m ha ?_
  exact affineChartΓIso_inv_restrict M U V (homOfLE h) ha m

end AlgebraicGeometry.Scheme.Modules
