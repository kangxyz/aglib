/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.ProjectiveSpace.BinaryFormProduct.Basic
public import Aglib.AlgebraicGeometry.ProjectiveSpace.BinaryFormProduct.Algebra
public import Aglib.AlgebraicGeometry.Modules.Invertible.Gluing.Sheaf
public import Aglib.AlgebraicGeometry.Modules.Invertible.Gluing.Frames

/-!
# Actual local coefficients on the original binary-form product source

Each source chart chooses one original nonzero coordinate in each original
projective-line factor. The local product polynomial uses the original
pulled coordinate ratios. Products of their original transition units glue
the coefficient line and its original `n+1` coefficient sections.
-/

@[expose] public noncomputable section

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open CategoryTheory CategoryTheory.Limits TopologicalSpace Opposite
open AlgebraicGeometry.Scheme.Modules AlgebraicGeometry.Scheme.Modules.Invertible

namespace AlgebraicGeometry.ProjectiveSpace.BinaryFormProduct

universe u

variable (R : Type u) [CommRing R] (n : ℕ)

/-- A choice of one original projective-line coordinate in each original factor. -/
abbrev Chart : Type u := Fin n → ULift.{u} (Fin 2)

/-- The original simultaneous inverse-image coordinate open. -/
def sourceOpen (a : Chart.{u} n) : (source R n).Opens :=
  ⨅ i : Fin n, liftedProjection R n i ⁻¹ᵁ
    ProjectiveSpace.coordinateOpen R (ULift.{u} (Fin 2)) (a i)

theorem sourceOpen_le_coordinate (a : Chart.{u} n) (i : Fin n) :
    sourceOpen R n a ≤ liftedProjection R n i ⁻¹ᵁ
      ProjectiveSpace.coordinateOpen R (ULift.{u} (Fin 2)) (a i) :=
  iInf_le _ i

/-- The original simultaneous factor-coordinate opens cover the original product. -/
theorem iSup_sourceOpen_eq_top : (⨆ a : Chart.{u} n, sourceOpen R n a) = ⊤ := by
  classical
  apply top_unique
  intro x _
  have h (i : Fin n) : ∃ j : ULift.{u} (Fin 2),
      x ∈ liftedProjection R n i ⁻¹ᵁ
        ProjectiveSpace.coordinateOpen R (ULift.{u} (Fin 2)) j := by
    obtain ⟨j, hj⟩ := Opens.mem_iSup.mp (show liftedProjection R n i x ∈
        ⨆ j, ProjectiveSpace.coordinateOpen R (ULift.{u} (Fin 2)) j by
      rw [ProjectiveSpace.iSup_coordinateOpen_eq_top]
      trivial)
    exact ⟨j, hj⟩
  choose a ha using h
  apply Opens.mem_iSup.mpr
  refine ⟨a, ?_⟩
  change x ∈ ((sourceOpen R n a : (source R n).Opens) : Set (source R n))
  rw [sourceOpen, Opens.coe_iInf]
  exact Set.mem_iInter.mpr ha

/-- An original factor-coordinate ratio on an arbitrary subopen of a source chart. -/
def localRatio (a : Chart.{u} n) (i : Fin n) (j : ULift.{u} (Fin 2))
    (V : (source R n).Opens) (hV : V ≤ sourceOpen R n a) : Γ(source R n, V) :=
  ProjectiveSpace.ratioOn (liftedProjection R n i) (a i) j V
    (hV.trans (sourceOpen_le_coordinate R n a i))

@[simp]
theorem localRatio_selected (a : Chart.{u} n) (i : Fin n)
    (V : (source R n).Opens) (hV : V ≤ sourceOpen R n a) :
    localRatio R n a i (a i) V hV = 1 :=
  ProjectiveSpace.ratioOn_self _ _ _ _

@[simp]
theorem localRatio_restrict (a : Chart.{u} n) (i : Fin n) (j : ULift.{u} (Fin 2))
    {V W : (source R n).Opens} (h : W ≤ V) (hV : V ≤ sourceOpen R n a) :
    sectionRestrict (source R n) h (localRatio R n a i j V hV) =
      localRatio R n a i j W (h.trans hV) :=
  ProjectiveSpace.ratioOn_restrict _ _ _ _ _

theorem localRatio_overlap (a b : Chart.{u} n) (i : Fin n) (j : ULift.{u} (Fin 2))
    (V : (source R n).Opens) (ha : V ≤ sourceOpen R n a) (hb : V ≤ sourceOpen R n b) :
    localRatio R n a i j V ha =
      localRatio R n a i (b i) V ha * localRatio R n b i j V hb :=
  ProjectiveSpace.ratioOn_mul _ _ _ _ _ _ _

/-- The original product of factor transition units on the actual overlap. -/
def transitionUnit (a b : Chart.{u} n) :
    (Γ(source R n, sourceOpen R n a ⊓ sourceOpen R n b))ˣ := by
  let z := ∏ i : Fin n,
    localRatio R n a i (b i) (sourceOpen R n a ⊓ sourceOpen R n b) inf_le_left
  let w := ∏ i : Fin n,
    localRatio R n b i (a i) (sourceOpen R n a ⊓ sourceOpen R n b) inf_le_right
  have hzw : z * w = 1 := by
    rw [← Finset.prod_mul_distrib]
    apply Finset.prod_eq_one
    intro i _
    simpa only [localRatio_selected] using
      (localRatio_overlap R n a b i (a i)
        (sourceOpen R n a ⊓ sourceOpen R n b) inf_le_left inf_le_right).symm
  exact ⟨z, w, hzw, (mul_comm w z).trans hzw⟩

@[simp]
theorem transitionUnit_val (a b : Chart.{u} n) :
    (transitionUnit R n a b : Γ(source R n, sourceOpen R n a ⊓ sourceOpen R n b)) =
      ∏ i : Fin n,
        localRatio R n a i (b i) (sourceOpen R n a ⊓ sourceOpen R n b) inf_le_left := rfl

/-- The actual coefficient line has the products of the original factor-ratio transitions. -/
def coefficientCocycle : UnitCocycle (sourceOpen R n) where
  transition := transitionUnit R n
  cocycle a b c V ha hb hc := by
    apply Units.ext
    change sectionRestrict (source R n) (le_inf ha hb) (transitionUnit R n a b).val *
        sectionRestrict (source R n) (le_inf hb hc) (transitionUnit R n b c).val =
      sectionRestrict (source R n) (le_inf ha hc) (transitionUnit R n a c).val
    simp only [transitionUnit_val, map_prod, localRatio_restrict]
    rw [← Finset.prod_mul_distrib]
    apply Finset.prod_congr rfl
    intro i _
    exact (localRatio_overlap R n a b i (c i) V ha hb).symm

theorem coefficientCocycle_transitionOn_val (a b : Chart.{u} n)
    (V : (source R n).Opens) (ha : V ≤ sourceOpen R n a) (hb : V ≤ sourceOpen R n b) :
    ((coefficientCocycle R n).transitionOn a b ha hb : Γ(source R n, V)) =
      ∏ i : Fin n, localRatio R n a i (b i) V ha := by
  simp only [UnitCocycle.transitionOn, coefficientCocycle, Units.coe_map,
    transitionUnit_val, map_prod]
  apply Finset.prod_congr rfl
  intro i _
  change sectionRestrict (source R n) (le_inf ha hb)
    (localRatio R n a i (b i) (sourceOpen R n a ⊓ sourceOpen R n b) inf_le_left) = _
  exact localRatio_restrict R n a i (b i) (le_inf ha hb) inf_le_left

/-- The original output coefficient in the original source chart and on any subopen. -/
def localCoefficient (a : Chart.{u} n) (V : (source R n).Opens)
    (hV : V ≤ sourceOpen R n a) (k : Fin (n + 1)) : Γ(source R n, V) :=
  coefficient (fun i => localRatio R n a i (ULift.up 0) V hV)
    (fun i => localRatio R n a i (ULift.up 1) V hV) k

@[simp]
theorem localCoefficient_restrict (a : Chart.{u} n)
    {V W : (source R n).Opens} (h : W ≤ V) (hV : V ≤ sourceOpen R n a)
    (k : Fin (n + 1)) :
    sectionRestrict (source R n) h (localCoefficient R n a V hV k) =
      localCoefficient R n a W (h.trans hV) k := by
  simpa only [localCoefficient, localRatio_restrict] using
    (coefficient_map (sectionRestrict (source R n) h)
      (fun i => localRatio R n a i (ULift.up 0) V hV)
      (fun i => localRatio R n a i (ULift.up 1) V hV) k).symm

/-- The local original coefficient vectors differ by the same original transition unit. -/
theorem localCoefficient_overlap (a b : Chart.{u} n)
    (V : (source R n).Opens) (ha : V ≤ sourceOpen R n a) (hb : V ≤ sourceOpen R n b)
    (k : Fin (n + 1)) :
    localCoefficient R n a V ha k =
      ((coefficientCocycle R n).transitionOn a b ha hb : Γ(source R n, V)) *
        localCoefficient R n b V hb k := by
  have hx : (fun i => localRatio R n a i (ULift.up 0) V ha) =
      (fun i => localRatio R n a i (b i) V ha *
        localRatio R n b i (ULift.up 0) V hb) := by
    funext i
    exact localRatio_overlap R n a b i (ULift.up 0) V ha hb
  have hy : (fun i => localRatio R n a i (ULift.up 1) V ha) =
      (fun i => localRatio R n a i (b i) V ha *
        localRatio R n b i (ULift.up 1) V hb) := by
    funext i
    exact localRatio_overlap R n a b i (ULift.up 1) V ha hb
  unfold localCoefficient
  rw [hx, hy, coefficient_scale, coefficientCocycle_transitionOn_val]

/-- The actual matching section on every original source open. -/
def coefficientSectionValue (k : Fin (n + 1)) (V : (source R n).Opens) :
    (coefficientCocycle R n).Sections V :=
  ⟨fun a => localCoefficient R n a (V ⊓ sourceOpen R n a) inf_le_right k, by
    intro W hWV a b ha hb
    rw [localCoefficient_restrict, localCoefficient_restrict]
    exact localCoefficient_overlap R n a b W ha hb k⟩

/-- The original coefficient sections of the actual coefficient line. -/
def coefficientSection (k : ULift.{u} (Fin (n + 1))) :
    (coefficientCocycle R n).sheaf.sections :=
  PresheafOfModules.sectionsMk
    (fun V => coefficientSectionValue R n k.down V.unop) (by
      intro V W f
      apply Subtype.ext
      funext a
      exact localCoefficient_restrict R n a
        (inf_le_inf (leOfHom f.unop) le_rfl) inf_le_right k.down)

/-- The actual native frame projection reads the original normalized product coefficient. -/
theorem coefficientSection_localCoefficient (a : Chart.{u} n)
    (V : (source R n).Opens) (hV : V ≤ sourceOpen R n a)
    (k : ULift.{u} (Fin (n + 1))) :
    LocalFrames.coefficient (sourceOpen R n) (coefficientCocycle R n).sheaf
        (coefficientCocycle R n).localIso a hV ((coefficientSection R n k).val (op V)) =
      localCoefficient R n a V hV k.down := by
  change sectionRestrict (source R n) (le_inf le_rfl hV)
    (localCoefficient R n a (V ⊓ sourceOpen R n a) inf_le_right k.down) = _
  exact localCoefficient_restrict R n a (le_inf le_rfl hV) inf_le_right k.down

end AlgebraicGeometry.ProjectiveSpace.BinaryFormProduct
