/-
Copyright (c) 2026 kangxyz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/

module

public import Aglib.AlgebraicGeometry.Morphisms.FiniteEtale.Descent.FiniteFieldLocalMaps
public import Aglib.AlgebraicGeometry.Morphisms.FiniteEtale.Descent.GlobalExplicitDescent

/-! Chart coordinates turning affine-derived local models into the exact inputs for global gluing.
-/

@[expose] public section

noncomputable section
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Opposite
open _root_.AlgebraicGeometry.Scheme.FiniteEtale (baseChange baseChangeComp)
namespace AlgebraicGeometry.Scheme.FiniteEtale.FieldCoverDescent
universe u
variable (K Ω : Type u) [Field K] [Field Ω] [Algebra K Ω]
  {X : Scheme.{u}} (p : X ⟶ Spec (.of K)) (𝒰 : X.OpenCover.{u}) (s : Finset Ω)

/-- The structural map to `X` from the field stage indexed by `s` . -/
abbrev stageBase := ((FieldLimit.schemeDiagram K Ω p).obj (op s)).hom
/-- The projection from the `Ω` -base change of `X` to its field stage indexed by `s` . -/
abbrev projection := FieldLimit.fieldProjection K Ω p (op s)
/-- The open cover `𝒰` pulled back to the field stage indexed by `s` . -/
abbrev stageCover := 𝒰.pullback₁ (stageBase K Ω p s)

/-- The pulled-back chart equals the actual field stage of the chart. -/
def stageChartIso (i : 𝒰.I₀) : (stageCover K Ω p 𝒰 s).X i ≅
    ((FieldLimit.schemeDiagram K Ω (𝒰.f i ≫ p)).obj (op s)).left :=
  pullbackLeftPullbackSndIso (Spec.algebraMap K (FieldLimit.finiteField K Ω s)) p (𝒰.f i)

@[reassoc (attr := simp)] theorem stageChartIso_hom_base (i : 𝒰.I₀) :
    (stageChartIso K Ω p 𝒰 s i).hom ≫
      ((FieldLimit.schemeDiagram K Ω (𝒰.f i ≫ p)).obj (op s)).hom =
        pullback.snd (stageBase K Ω p s) (𝒰.f i) :=
  pullbackLeftPullbackSndIso_hom_snd _ _ _

@[reassoc (attr := simp)] theorem stageChartIso_hom_field (i : 𝒰.I₀) :
    (stageChartIso K Ω p 𝒰 s i).hom ≫
      pullback.fst (Spec.algebraMap K (FieldLimit.finiteField K Ω s)) (𝒰.f i ≫ p) =
        pullback.fst (stageBase K Ω p s) (𝒰.f i) ≫
          pullback.fst (Spec.algebraMap K (FieldLimit.finiteField K Ω s)) p :=
  pullbackLeftPullbackSndIso_hom_fst _ _ _

/-- The pullback of the stage chart along the projection from the `Ω` -base change. -/
abbrev chartGeometricBase (i : 𝒰.I₀) :=
  pullback ((stageCover K Ω p 𝒰 s).f i) (projection K Ω p s)

/-- The local structural equation seen from the actual double pullback. -/
theorem chartGeometricBase_equation (i : 𝒰.I₀) :
    pullback.fst ((stageCover K Ω p 𝒰 s).f i) (projection K Ω p s) ≫
        pullback.snd (stageBase K Ω p s) (𝒰.f i) ≫ 𝒰.f i =
      pullback.snd ((stageCover K Ω p 𝒰 s).f i) (projection K Ω p s) ≫
        pullback.fst p (Spec.algebraMap K Ω) := by
  rw [← pullback.condition]
  change _ ≫ (stageCover K Ω p 𝒰 s).f i ≫ stageBase K Ω p s = _
  rw [← Category.assoc, pullback.condition, Category.assoc]
  exact congrArg (fun k ↦ pullback.snd ((stageCover K Ω p 𝒰 s).f i)
    (projection K Ω p s) ≫ k) (FieldLimit.fieldProjection_base K Ω p (op s))

/-- Map from the geometric pullback of a stage chart to the chart's standard field extension. -/
def chartGeometricMap (i : 𝒰.I₀) : chartGeometricBase K Ω p 𝒰 s i ⟶
    pullback (𝒰.f i ≫ p) (Spec.algebraMap K Ω) :=
  pullback.lift
    (pullback.fst ((stageCover K Ω p 𝒰 s).f i) (projection K Ω p s) ≫
      pullback.snd (stageBase K Ω p s) (𝒰.f i))
    (pullback.snd ((stageCover K Ω p 𝒰 s).f i) (projection K Ω p s) ≫
      pullback.snd p (Spec.algebraMap K Ω)) (by
      simpa only [Category.assoc, pullback.condition] using
        congrArg (fun k ↦ k ≫ p) (chartGeometricBase_equation K Ω p 𝒰 s i))

@[reassoc] theorem chartGeometricMap_to_global (i : 𝒰.I₀) :
    chartGeometricMap K Ω p 𝒰 s i ≫
      geometricMap K Ω (𝒰.f i ≫ p) p (𝒰.f i) rfl =
        pullback.snd ((stageCover K Ω p 𝒰 s).f i) (projection K Ω p s) := by
  apply pullback.hom_ext
  · rw [Category.assoc, geometricMap_fst, ← Category.assoc,
      chartGeometricMap, pullback.lift_fst]
    simpa only [Category.assoc] using chartGeometricBase_equation K Ω p 𝒰 s i
  · simp [chartGeometricMap, Category.assoc]

@[reassoc] theorem chartGeometricMap_projection (i : 𝒰.I₀) :
    chartGeometricMap K Ω p 𝒰 s i ≫
      FieldLimit.fieldProjection K Ω (𝒰.f i ≫ p) (op s) =
        pullback.fst ((stageCover K Ω p 𝒰 s).f i) (projection K Ω p s) ≫
          (stageChartIso K Ω p 𝒰 s i).hom := by
  apply pullback.hom_ext (f := Spec.algebraMap K (FieldLimit.finiteField K Ω s))
    (g := 𝒰.f i ≫ p)
  · simp only [Category.assoc, fieldProjection_field, stageChartIso_hom_field]
    rw [← Category.assoc, chartGeometricMap, pullback.lift_snd]
    change _ = pullback.fst ((stageCover K Ω p 𝒰 s).f i) (projection K Ω p s) ≫
      (stageCover K Ω p 𝒰 s).f i ≫ _
    rw [← Category.assoc, pullback.condition]
    simpa only [Category.assoc] using
      congrArg (fun k ↦ pullback.snd ((stageCover K Ω p 𝒰 s).f i) (projection K Ω p s) ≫ k)
        (fieldProjection_field K Ω p s).symm
  · change _ ≫ ((FieldLimit.schemeDiagram K Ω (𝒰.f i ≫ p)).obj (op s)).hom =
      _ ≫ ((FieldLimit.schemeDiagram K Ω (𝒰.f i ≫ p)).obj (op s)).hom
    simp [FieldLimit.fieldProjection_base, chartGeometricMap, Category.assoc]

variable (Y : Scheme.FiniteEtale (pullback p (Spec.algebraMap K Ω)))
  (M : ∀ i : 𝒰.I₀, Scheme.FiniteEtale (((FieldLimit.schemeDiagram K Ω (𝒰.f i ≫ p)).obj
    (op s)).left))
  (e : ∀ i : 𝒰.I₀,
    (baseChange (FieldLimit.fieldProjection K Ω (𝒰.f i ≫ p) (op s))).obj (M i) ≅
      (baseChange (geometricMap K Ω (𝒰.f i ≫ p) p (𝒰.f i) rfl)).obj Y)

/-- The local finite étale model `M i` transported to the pulled-back chart by `stageChartIso`
. -/
def chartModel (i : 𝒰.I₀) : Scheme.FiniteEtale ((stageCover K Ω p 𝒰 s).X i) :=
  (baseChange (stageChartIso K Ω p 𝒰 s i).hom).obj (M i)

/-- Actual local reconstruction at the common stage, with the literal global field projection. -/
def chartModelIso (i : 𝒰.I₀) :
    (baseChange (pullback.fst ((stageCover K Ω p 𝒰 s).f i) (projection K Ω p s))).obj
      (chartModel K Ω p 𝒰 s M i) ≅
        (baseChange (pullback.snd ((stageCover K Ω p 𝒰 s).f i) (projection K Ω p s))).obj Y :=
  restrictDescentIso _ _ (stageChartIso K Ω p 𝒰 s i).hom (chartGeometricMap K Ω p 𝒰 s i)
    (chartGeometricMap_projection K Ω p 𝒰 s i).symm (M i) _ (e i) ≪≫
      (baseChangeComp (geometricMap K Ω (𝒰.f i ≫ p) p (𝒰.f i) rfl)
        (chartGeometricMap K Ω p 𝒰 s i)).symm.app Y ≪≫
      eqToIso (congrArg (fun k ↦ (baseChange k).obj Y) (chartGeometricMap_to_global K Ω p 𝒰 s i))

end AlgebraicGeometry.Scheme.FiniteEtale.FieldCoverDescent

/- Migration source: the R5Lab/Aglib mirror; exact module in the migration record.
R5 revision c82abf3a72ce1e1cedf4a4f1fe08bea994ad4df5.
SHA256 7a37a7de80c50f73e5e35facf0a65f4827ad613ac9e5dd6a590e8e9bd9374971.
Definitions, hypotheses and universes are retained modulo native names. -/
