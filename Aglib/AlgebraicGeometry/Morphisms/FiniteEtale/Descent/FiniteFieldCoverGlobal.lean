/-
Copyright (c) 2026 kangxyz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/

module

public import Aglib.AlgebraicGeometry.Morphisms.FiniteEtale.Descent.FiniteFieldGlobalFromModels
public import Aglib.AlgebraicGeometry.Morphisms.FiniteEtale.Descent.FiniteFieldChartModels
public import Aglib.AlgebraicGeometry.Morphisms.FiniteEtale.Descent.FiniteFieldInitialModels

/-!
# Actual finite-field-stage cover descent for any qcqs scheme

The local models are constructed from the accepted finite-etale algebra model on arbitrary
commutative coefficient rings. A finite intersection cover reduces overlap arrows to a finite
family of genuine scheme morphisms. The actual affine inverse limit descends those morphisms;
faithful-flat reflection supplies their equations and the shared gluing producer reconstructs
an actual cover over one of the original finite-subset field stages.
-/

@[expose] public section

noncomputable section
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Opposite TopologicalSpace
open _root_.AlgebraicGeometry.Scheme.FiniteEtale (baseChange)
open AlgebraicGeometry.Scheme.FiniteEtale.PurelyInseparable.Global
namespace AlgebraicGeometry.Scheme.FiniteEtale.FieldCoverDescent
universe u
variable (K Ω : Type u) [Field K] [Field Ω] [Algebra K Ω] [Algebra.IsAlgebraic K Ω]
  {X : Scheme.{u}} [CompactSpace X] [QuasiSeparatedSpace X] (p : X ⟶ Spec (.of K))
  (Y : Scheme.FiniteEtale (pullback p (Spec.algebraMap K Ω)))

/-- Finite etale cover objects descend through algebraic field extension on every qcqs scheme. -/
theorem exists_qcqs_cover :
    ∃ (s : Finset Ω) (Z : Scheme.FiniteEtale (((FieldLimit.schemeDiagram K Ω p).obj (op s)).left)),
      Nonempty ((baseChange (FieldLimit.fieldProjection K Ω p (op s))).obj Z ≅ Y) := by
  let 𝒜 := X.affineCover.finiteSubcover
  let U : 𝒜.I₀ → X.Opens := fun j ↦ (𝒜.f j).opensRange
  have hU : IsOpenCover U := 𝒜.isOpenCover_opensRange
  have hAffine (j : 𝒜.I₀) : IsAffineOpen (U j) := isAffineOpen_opensRange (𝒜.f j)
  let 𝒰 := intersectionCover U hU
  have (i : 𝒰.I₀) : CompactSpace (𝒰.X i) :=
    intersectionCover_compact U hU (fun j ↦ (hAffine j).isCompact) i
  have (i : 𝒰.I₀) : QuasiSeparatedSpace (𝒰.X i) :=
    intersectionCover_quasiSeparated U hU i
  let L := intersectionModels K Ω p Y U hU hAffine
  let s := L.1
  let 𝒱 := stageCover K Ω p 𝒰 s
  have (i : 𝒱.I₀) : CompactSpace (𝒱.X i) :=
    QuasiCompact.compactSpace_of_compactSpace (pullback.snd (stageBase K Ω p s) (𝒰.f i))
  have (i : 𝒱.I₀) : QuasiSeparatedSpace (𝒱.X i) :=
    quasiSeparatedSpace_of_quasiSeparated (pullback.snd (stageBase K Ω p s) (𝒰.f i))
  let M := chartModel K Ω p 𝒰 s L.2.1
  let e := chartModelIso K Ω p 𝒰 s Y L.2.1 L.2.2
  let f := FieldLimit.fieldProjection K Ω p (op s)
  let A := Explicit.modelOver 𝒱 M
  let m := Explicit.modelStructure 𝒱 M
  let α := Explicit.modelIso f 𝒱 Y M e
  have hm := Explicit.modelIso_structure f 𝒱 Y M e
  have (i : 𝒱.I₀) : IsFinite (m i).left := inferInstanceAs (IsFinite (M i).obj.hom)
  have (i : 𝒱.I₀) : Etale (m i).left := inferInstanceAs (Etale (M i).obj.hom)
  let D := fieldSchemeDiagram K Ω p
  let c := standardFieldCone K Ω p
  have {i j : (Finset Ω)ᵒᵖ} (a : i ⟶ j) : IsAffineHom (D.map a) :=
    inferInstanceAs (IsAffineHom ((FieldLimit.schemeDiagram K Ω p).map a).left)
  have (i : (Finset Ω)ᵒᵖ) : Surjective (c.π.app i) := fieldProjection_surjective K Ω p i.unop
  have (i : (Finset Ω)ᵒᵖ) : Flat (c.π.app i) := fieldProjection_flat K Ω p i.unop
  have (i : (Finset Ω)ᵒᵖ) : QuasiCompact (c.π.app i) := fieldProjection_quasiCompact K Ω p i.unop
  let : Quiver.IsThin 𝒱.I₀ := inferInstanceAs (Quiver.IsThin 𝒰.I₀)
  let : Finite 𝒱.I₀ := inferInstanceAs (Finite 𝒰.I₀)
  obtain ⟨j, Z, hZ⟩ := exists_globalCover_from_localModels D c
    (standardFieldConeIsLimit K Ω p) (op s) 𝒱 Y A m α hm
  exact ⟨j.left.unop, Z, hZ⟩

/-- Actual producer at the original `Finset Ω` stage, including the reconstruction isomorphism. -/
def qcqsCoverDescent :
    Σ s : Finset Ω, Σ Z : Scheme.FiniteEtale (((FieldLimit.schemeDiagram K Ω p).obj (op s)).left),
      (baseChange (FieldLimit.fieldProjection K Ω p (op s))).obj Z ≅ Y :=
  ⟨(exists_qcqs_cover K Ω p Y).choose,
    (exists_qcqs_cover K Ω p Y).choose_spec.choose,
    (exists_qcqs_cover K Ω p Y).choose_spec.choose_spec.some⟩

end AlgebraicGeometry.Scheme.FiniteEtale.FieldCoverDescent

/- Migration source: the R5Lab/Aglib mirror; exact module in the migration record.
R5 revision c82abf3a72ce1e1cedf4a4f1fe08bea994ad4df5.
SHA256 f27c388e0ee170fd399ff603af6433d693e31b372fba492022ad6cc51345926b.
Definitions, hypotheses and universes are retained modulo native names. -/
