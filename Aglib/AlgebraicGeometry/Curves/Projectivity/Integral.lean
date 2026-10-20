/-
Copyright (c) 2026 kangxyz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.Curves.Projectivity.Embedding
public import Aglib.AlgebraicGeometry.Curves.Projectivity.PrincipalBoundary
public import Aglib.AlgebraicGeometry.Cohomology.Proper.PrincipalChain
public import Aglib.AlgebraicGeometry.ProjectiveSpace.PrincipalPencil

/-!
# Projectivity of proper integral field curves

A principal boundary on the original curve supplies an actual chain of line
modules with finite closed-support quotients. Proper coherent finiteness and
stabilization lift one quotient section. The original two sections define an
actual pencil whose first coordinate open has precisely the original boundary
complement as inverse image. Its generic point and a boundary point have
distinct images, so the pencil is dominant and finite. The generic finite-cover
embedding theorem then gives a closed embedding of the original curve.

Every field and field universe is allowed. No normality, smoothness, geometric
integrality or prior projectivity of the curve is supplied. The accepted native
proper-cohomology theorem uses Chow modification internally. Reducible,
nonreduced and zero-dimensional cases of the broader Stacks theorem remain
outside these integral dimension-one endpoints.
-/




@[expose] public section

noncomputable section
open AlgebraicGeometry.Scheme.ProjectiveLine.TwoChart
open AlgebraicGeometry.Scheme

open CategoryTheory AlgebraicGeometry TopologicalSpace Opposite
open _root_.AlgebraicGeometry.Scheme.OverField (FScheme)
open AlgebraicGeometry.Scheme.Modules.Invertible (PrincipalChain)
open _root_.AlgebraicGeometry.Scheme.ProjectiveLine.TwoChart (twoChartLine)
open _root_.AlgebraicGeometry.Scheme.Cohomology
open AlgebraicGeometry.Scheme.OverField.Curve.Projectivity

universe u

namespace AlgebraicGeometry.Scheme.OverField.Curve.Projectivity

/-- The actual principal boundary supplies the generic line-module chain inputs. -/
def PrincipalBoundary.principalChain {X : Scheme.{u}} (b : PrincipalBoundary X) :
    PrincipalChain X where
  U := b.U
  W := b.W
  covers := b.covers
  f := b.f
  unit_overlap := b.unit_overlap
  regular := b.regular

private theorem isDominant_of_nonconstant_of_dimension_le_one
    {X Y : Scheme.{u}} [IrreducibleSpace X] [IrreducibleSpace Y]
    (f : X ⟶ Y) (hdim : topologicalKrullDim Y ≤ 1)
    (hnonconstant : ∃ x y : X, f x ≠ f y) : IsDominant f := by
  have hgen : f (genericPoint X) = genericPoint Y := by
    rcases DimensionOne.point_eq_generic_or_isClosed Y hdim (f (genericPoint X)) with
      hgen | hclosed
    · exact hgen
    · have heq (x : X) : f x = f (genericPoint X) := by
        have hx := specializes_iff_mem_closure.mp
          ((genericPoint_specializes x).map f.continuous)
        rwa [hclosed.closure_eq, Set.mem_singleton_iff] at hx
      obtain ⟨x, y, hxy⟩ := hnonconstant
      exact False.elim (hxy ((heq x).trans (heq y).symm))
  constructor
  rw [denseRange_iff_closure_range]
  apply Set.eq_univ_of_univ_subset
  rw [← genericPoint_closure Y]
  exact closure_mono (Set.singleton_subset_iff.mpr ⟨genericPoint X, hgen⟩)

variable (K : Type u) [Field K]

private def lineIsoNative :
    twoChartLine (.of K) ≅ ProjectiveSpace K (ULift.{u} (Fin 2)) :=
  (Over.forget _).mapIso ((twoChartLineOverIsoProjectiveP1 K) ≪≫
    AlgebraicGeometry.Scheme.OverField.Curve.ProjectiveLine.projectiveLineOverIsoNative K)

private theorem nativeP1_integral : IsIntegral (ProjectiveSpace K (ULift.{u} (Fin 2))) :=
  IsIntegral.of_isIso (lineIsoNative K).hom

private theorem nativeP1_dimension :
    topologicalKrullDim (ProjectiveSpace K (ULift.{u} (Fin 2))) = 1 :=
  (IsHomeomorph.topologicalKrullDim_eq _ (lineIsoNative K).hom.homeomorph.isHomeomorph).symm.trans
    (twoChartLine_topologicalKrullDim K)

variable {K}

/-- Every integral proper dimension-one field scheme admits an actual finite
dominant map to native P1, over its original field, without normality. -/
theorem exists_finite_dominant_map_to_nativeP1
    (X : FScheme K) [IsIntegral X.left] [IsProper X.hom]
    (hdim : topologicalKrullDim X.left = 1) :
    ∃ f : X ⟶ Over.mk
      (ProjectiveSpace.toSpec K (ULift.{u} (Fin 2))),
      IsFinite f.left ∧ IsDominant f.left := by
  let b := principalBoundaryOfProperIntegralCurve X hdim
  let C := b.principalChain
  have hfin : ((C.W : Set X.left)ᶜ).Finite := by
    change ((b.W : Set X.left)ᶜ).Finite
    rw [b.complement, compl_compl]
    exact b.Z_finite
  have hclosed : ∀ x : X.left, x ∉ C.W → IsClosed ({x} : Set X.left) := by
    intro x hx
    change x ∉ (b.W : Set X.left) at hx
    rw [b.complement] at hx
    exact b.point_closed x (not_not.mp hx)
  obtain ⟨n, τ, hτ⟩ := exists_lift_principalChain_quotientSection X C hfin hclosed
  obtain ⟨φ, hbase, hpre⟩ :=
    ProjectiveSpace.PrincipalPencil.exists_map X.hom C n τ b.overlap hτ
  change φ ⁻¹ᵁ ProjectiveSpace.coordinateOpen K (ULift.{u} (Fin 2))
    ProjectiveSpace.PrincipalPencil.first = b.W at hpre
  have : IsIntegral (ProjectiveSpace K (ULift.{u} (Fin 2))) := nativeP1_integral K
  have hnonconstant : ∃ x y : X.left, φ x ≠ φ y := by
    obtain ⟨z, hz⟩ := b.Z_nonempty
    have heta : φ (genericPoint X.left) ∈ ProjectiveSpace.coordinateOpen K
        (ULift.{u} (Fin 2)) ProjectiveSpace.PrincipalPencil.first := by
      change genericPoint X.left ∈ φ ⁻¹ᵁ ProjectiveSpace.coordinateOpen K
        (ULift.{u} (Fin 2)) ProjectiveSpace.PrincipalPencil.first
      rw [hpre]
      exact b.genericPoint_mem_W
    have hznot : φ z ∉ ProjectiveSpace.coordinateOpen K (ULift.{u} (Fin 2))
        ProjectiveSpace.PrincipalPencil.first := by
      intro hzmem
      have hzW : z ∈ b.W := by
        rw [← hpre]
        exact hzmem
      change z ∈ (b.W : Set X.left) at hzW
      rw [b.complement] at hzW
      exact hzW hz
    exact ⟨genericPoint X.left, z, fun heq => hznot (heq ▸ heta)⟩
  have hdom : IsDominant φ :=
    isDominant_of_nonconstant_of_dimension_le_one φ (nativeP1_dimension K).le hnonconstant
  have : IsProper (φ ≫ ProjectiveSpace.toSpec K (ULift.{u} (Fin 2))) := by
    rw [hbase]
    infer_instance
  have : IsProper φ :=
    IsProper.of_comp _ (ProjectiveSpace.toSpec K (ULift.{u} (Fin 2)))
  let : IsLocallyNoetherian X.left := LocallyOfFiniteType.isLocallyNoetherian X.hom
  let : CompactSpace X.left := QuasiCompact.compactSpace_of_compactSpace X.hom
  let : IsNoetherian X.left := ⟨⟩
  have hf : IsFinite φ :=
    proper_dominant_curve_isFinite φ hdim.le (nativeP1_dimension K)
  exact ⟨Over.homMk φ hbase, hf, hdom⟩

/-- Every integral proper dimension-one field scheme has an actual closed
projective embedding commuting with the original structure morphism. -/
theorem exists_projectiveEmbedding
    (X : FScheme K) [IsIntegral X.left] [IsProper X.hom]
    (hdim : topologicalKrullDim X.left = 1) :
    ∃ (n : ℕ) (i : X.left ⟶ ProjectiveSpace K (ULift.{u} (Fin (n + 1)))),
      IsClosedImmersion i ∧
        i ≫ ProjectiveSpace.toSpec K (ULift.{u} (Fin (n + 1))) = X.hom := by
  obtain ⟨f, hf, _⟩ := exists_finite_dominant_map_to_nativeP1 X hdim
  have := hf
  obtain ⟨n, i, hi, hbase⟩ :=
    ProjectiveSpace.FiniteEmbedding.exists_closedImmersion_of_isFinite f.left
  exact ⟨n, i, hi, hbase.trans f.w⟩

end AlgebraicGeometry.Scheme.OverField.Curve.Projectivity
