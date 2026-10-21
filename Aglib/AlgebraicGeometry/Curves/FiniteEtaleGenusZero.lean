/-
Copyright (c) 2026 kangxyz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.Curves.RiemannHurwitz
public import Aglib.AlgebraicGeometry.Morphisms.FiniteFlat.RankOne
public import Aglib.AlgebraicGeometry.Geometrically.Connected.PointedCurve

/-!
# Finite étale covers of actual genus-zero curves

The rank and triviality statements concern the same finite étale map and coherent genus. All
canonical-degree, product-formula, norm-order and rank-family premises of the source
Riemann–Hurwitz use remain explicit. For a connected cover with an actual rational section,
smoothness, properness and Noetherianity are derived and the native pointed-curve criterion
supplies geometric connectedness.

R5 revision `f8a3314ddecffcada2ec721d26d56a937bed9690`.
`Curves/Cyclic/Covers/Components.lean`: source ranges [[84, 149]];
SHA-256 `593810951171d1f9d65135289e94a3a63ca57073cfb37055f5afd0cdb7f3a5aa`.
-/

@[expose] public noncomputable section

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory Limits AlgebraicGeometry
open AlgebraicGeometry.Scheme
open AlgebraicGeometry.Scheme.OverField
open AlgebraicGeometry.Scheme.Hom
open AlgebraicGeometry.Scheme.OverField.Curve
namespace AlgebraicGeometry.Scheme.OverField.Curve
universe u
variable (hnormal : SmoothFieldNormality.{u}) (hcomp : NormalComponentsOpen.{u})
variable (hreg : SmoothFieldRegularity.{u}) (hclosed : SmoothClosedPointDimension.{u})
variable (hdim : SmoothFieldDimension.{u}) (hprod : Picard.Degree.ProperCurveProductFormula.{u})
variable (hbase : _root_.AlgebraicGeometry.Scheme.Modules.AffineModuleBaseChange.{u})
variable (hgen : Scheme.Hom.FiniteFlat.FiniteDominantGenericFibre.{u})
variable (hnorm : Picard.NormDegree.FiniteMorphismNormOrder.{u})
variable (hfree : FiniteFlatPresentationLocallyFree.{u})
variable (hcanonical : SmoothCanonicalDegree.{u})
variable {F : Type u} [Field F] {X Y : FScheme F}
include hnormal hcomp hreg hclosed hdim hprod hbase hgen hnorm hfree hcanonical
/-- The rank of an actual finite étale map of geometrically connected curves
onto a genus-zero target is one. The degree and surjectivity are derived. -/
theorem finiteEtale_genusZero_finrank (f : X ⟶ Y)
    (hX : Properties X) (hY : Properties Y)
    [IsFinite f.left] [Etale f.left] (hzero : coherentGenus F Y = 0) (y : Y.left) :
    f.left.finrank y = 1 := by
  let := curveProperties_connectedSpace hY
  obtain ⟨x⟩ := curveProperties_nonempty hX
  let n := f.left.finrank (f.left x)
  have hpos : 1 ≤ n := f.left.one_le_finrank_map x
  have hr (z : Y.left) : f.left.finrank z = n :=
    f.left.isLocallyConstant_finrank.apply_eq_of_preconnectedSpace z (f.left x)
  have hsurj : Surjective f.left := (Scheme.Hom.one_le_finrank_iff_surjective f.left).mp
    (fun z => by rw [hr z]; exact hpos)
  have hrank (K : Type u) [Field K] (p : Spec (.of K) ⟶ Y.left) :
      letI : Algebra K Γ(pullback f.left p, ⊤) :=
        coordinateAlgebra K (Over.mk (pullback.snd f.left p))
      Module.finrank K Γ(pullback f.left p, ⊤) = n := by
    rw [← Scheme.Hom.FiniteFlat.nativeRank_geometricFibre]
    exact hr _
  have hfibre : HasGeometricFibreRank f n := by
    intro K _ _ t z
    exact hrank K z.left
  have hdegree : HasGeometricDegree f n :=
    (hasGeometricFibreRank_iff_hasGeometricDegree f n).mp hfibre
  have hRH := unramifiedRiemannHurwitz hnormal hcomp hreg hclosed hdim hprod
    hbase hgen hnorm hfree hcanonical
    f n hX hY inferInstance inferInstance hsurj hdegree
  rw [hzero] at hRH
  have hn : n = 1 := by omega
  exact (hr y).trans hn

/-- The same actual finite étale morphism is an isomorphism, using native rank. -/
theorem finiteEtale_genusZero_isIso (f : X ⟶ Y)
    (hX : Properties X) (hY : Properties Y)
    [IsFinite f.left] [Etale f.left] (hzero : coherentGenus F Y = 0) : IsIso f.left := by
  apply (Scheme.Hom.isIso_iff_finrank_eq f.left).mpr
  ext y
  exact finiteEtale_genusZero_finrank hnormal hcomp hreg hclosed hdim hprod
    hbase hgen hnorm hfree hcanonical f hX hY hzero y


omit hnormal hcomp hreg hclosed hdim hprod hbase hgen hnorm hfree hcanonical in
/-- Source curve properties derive from a connected actual finite étale cover
with an actual rational point, using the proved smooth proper Noetherian criterion. -/
theorem connectedPointedFiniteEtale_curveProperties
    (f : X ⟶ Y)
    (hY : Properties Y) [IsFinite f.left] [Etale f.left] [ConnectedSpace X.left]
    (o : Spec (.of F) ⟶ X.left) (ho : o ≫ X.hom = 𝟙 _) : Properties X := by
  let := hY.smooth
  let := hY.proper
  let : SmoothOfRelativeDimension 1 X.hom := by
    have h := smoothOfRelativeDimension_comp 0 1 f.left Y.hom
    simpa only [Over.w f, Nat.zero_add] using h
  let : IsProper X.hom := by
    rw [← Over.w f]
    infer_instance
  let : IsLocallyNoetherian X.left := LocallyOfFiniteType.isLocallyNoetherian X.hom
  let : CompactSpace X.left := QuasiCompact.compactSpace_of_compactSpace X.hom
  let : IsNoetherian X.left := ⟨⟩
  exact ⟨inferInstance, inferInstance,
    Scheme.geometricallyConnected_of_pointed_proper_smooth_curve X.hom o ho⟩

/-- A connected, rationally pointed finite étale cover of an actual genus-zero
curve is trivial over that SAME target, over the original field. -/
theorem connectedPointedFiniteEtale_genusZero_isIso
    (f : X ⟶ Y)
    (hY : Properties Y) [IsFinite f.left] [Etale f.left] [ConnectedSpace X.left]
    (o : Spec (.of F) ⟶ X.left) (ho : o ≫ X.hom = 𝟙 _) (hzero : coherentGenus F Y = 0) :
    IsIso f.left :=
  finiteEtale_genusZero_isIso hnormal hcomp hreg hclosed hdim hprod
    hbase hgen hnorm hfree hcanonical f
    (connectedPointedFiniteEtale_curveProperties f hY o ho) hY hzero


end AlgebraicGeometry.Scheme.OverField.Curve
