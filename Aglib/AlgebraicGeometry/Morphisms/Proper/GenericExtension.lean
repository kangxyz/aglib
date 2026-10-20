/-
Copyright (c) 2026 kangxyz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.FunctionField.Map
public import Mathlib.AlgebraicGeometry.ValuativeCriterion
public import Mathlib.AlgebraicGeometry.SpreadingOut
public import Mathlib.AlgebraicGeometry.Gluing
public import Mathlib.RingTheory.DedekindDomain.Dvr

/-!
# Proper extension from actual valuation-ring stalks

Source: packet R5Lab.Aglib.AlgebraicGeometry.Morphisms.Proper.GenericExtension.
The valuative lift is spread and glued on the original source.
The structural and generic-stalk triangles are retained.
-/

@[expose] public section

noncomputable section
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
namespace AlgebraicGeometry.Scheme
universe u
variable {X Y S : Scheme.{u}} [IsIntegral X]

/-- The generic point belongs to every inhabited open subset. -/
theorem generic_mem_open (U : X.Opens) (hU : (U : Set X).Nonempty) : genericPoint X ∈ U :=
  (genericPoint_spec X).mem_open_set_iff U.isOpen |>.mpr (by simpa using hU)

/-- The generic-stalk morphism lifted to an inhabited open subset. -/
def genericToOpen (U : X.Opens) (hU : (U : Set X).Nonempty) :
    Spec X.functionField ⟶ U.toScheme :=
  U.fromSpecStalkOfMem (genericPoint X) (generic_mem_open U hU)

@[reassoc (attr := simp)]
theorem genericToOpen_ι (U : X.Opens) (hU : (U : Set X).Nonempty) :
    genericToOpen U hU ≫ U.ι = X.fromSpecStalk (genericPoint X) :=
  Scheme.Opens.fromSpecStalkOfMem_ι ..

/-- Generic localization followed by a local-spectrum inclusion is the same
literal generic map into the open subset. -/
theorem genericToOpen_factor (U : X.Opens) (x : X) (hx : x ∈ U) :
    Spec.map (CommRingCat.ofHom (algebraMap (X.presheaf.stalk x) X.functionField)) ≫
      U.fromSpecStalkOfMem x hx = genericToOpen U ⟨x, hx⟩ := by
  apply (cancel_mono U.ι).mp
  rw [Category.assoc, Scheme.Opens.fromSpecStalkOfMem_ι, genericToOpen_ι]
  exact Scheme.SpecMap_stalkSpecializes_fromSpecStalk (genericPoint_specializes x)

/-- Properness extends the original generic map to each valuation-ring stalk. -/
theorem exists_stalk_extension (sX : X ⟶ S) (sY : Y ⟶ S) [IsProper sY]
    (g : Spec X.functionField ⟶ Y)
    (hg : g ≫ sY = X.fromSpecStalk (genericPoint X) ≫ sX)
    (x : X) [ValuationRing (X.presheaf.stalk x)] :
    ∃ φ : Spec (X.presheaf.stalk x) ⟶ Y,
      Spec.map (CommRingCat.ofHom (algebraMap (X.presheaf.stalk x) X.functionField)) ≫ φ = g ∧
      φ ≫ sY = X.fromSpecStalk x ≫ sX := by
  let sq : ValuativeCommSq sY := {
    R := X.presheaf.stalk x
    K := X.functionField
    i₁ := g
    i₂ := X.fromSpecStalk x ≫ sX
    commSq := ⟨by
      rw [hg, ← Category.assoc]
      exact congrArg (fun m => m ≫ sX)
        (Scheme.SpecMap_stalkSpecializes_fromSpecStalk (genericPoint_specializes x)).symm⟩ }
  have hex : ValuativeCriterion.Existence sY := by
    have h : UniversallyClosed sY := inferInstance
    rw [UniversallyClosed.eq_valuativeCriterion] at h
    exact h.1
  let : sq.commSq.HasLift := hex sq
  exact ⟨sq.commSq.lift, sq.commSq.fac_left, sq.commSq.fac_right⟩

/-- The local valuative extension spreads to an actual open neighborhood. -/
theorem exists_open_extension (sX : X ⟶ S) (sY : Y ⟶ S) [IsProper sY]
    (g : Spec X.functionField ⟶ Y)
    (hg : g ≫ sY = X.fromSpecStalk (genericPoint X) ≫ sX)
    (x : X) [ValuationRing (X.presheaf.stalk x)] :
    ∃ (U : X.Opens) (hx : x ∈ U) (f : U.toScheme ⟶ Y),
      genericToOpen U ⟨x, hx⟩ ≫ f = g ∧ f ≫ sY = U.ι ≫ sX := by
  obtain ⟨φ, hφg, hφs⟩ := exists_stalk_extension sX sY g hg x
  obtain ⟨U, hx, f, hφ, hfs⟩ := spread_out_of_isGermInjective' sX sY φ hφs
  refine ⟨U, hx, f, ?_, hfs⟩
  rw [← genericToOpen_factor U x hx, Category.assoc, ← hφ]
  exact hφg

/-- Proper targets admit extension from the generic point of an integral
scheme with valuation-ring stalks, with both original triangles proved. -/
theorem exists_generic_extension (sX : X ⟶ S) (sY : Y ⟶ S) [IsProper sY]
    [∀ x : X, ValuationRing (X.presheaf.stalk x)]
    (g : Spec X.functionField ⟶ Y)
    (hg : g ≫ sY = X.fromSpecStalk (genericPoint X) ≫ sX) :
    ∃ f : X ⟶ Y, f ≫ sY = sX ∧ X.fromSpecStalk (genericPoint X) ≫ f = g := by
  classical
  choose U hx f hfg hfs using fun x => exists_open_extension sX sY g hg x
  let c : X.OpenCover := {
    I₀ := X
    X i := (U i).toScheme
    f i := (U i).ι
    mem₀ := by
      rw [Scheme.presieve₀_mem_precoverage_iff]
      exact ⟨fun x => ⟨x, by simpa using hx x⟩, inferInstance⟩ }
  have hcompat : ∀ i j, pullback.fst (c.f i) (c.f j) ≫ f i =
      pullback.snd (c.f i) (c.f j) ≫ f j := by
    intro i j
    let t : Spec X.functionField ⟶ pullback (c.f i) (c.f j) :=
      pullback.lift (genericToOpen (U i) ⟨i, hx i⟩) (genericToOpen (U j) ⟨j, hx j⟩)
        (by simp [c])
    let r : pullback (c.f i) (c.f j) ⟶ X := pullback.fst (c.f i) (c.f j) ≫ c.f i
    have hr : t ≫ r = X.fromSpecStalk (genericPoint X) := by
      simp [r, t, c]
    let : IsDominant (t ≫ r) := hr.symm ▸ inferInstance
    let : IsDominant t := IsDominant.of_comp_of_isOpenImmersion t r
    let : IsReduced (pullback (c.f i) (c.f j)) := isReduced_of_isOpenImmersion r
    apply ext_of_isDominant_of_isSeparated sY ?_ t ?_
    · simp only [Category.assoc, hfs]
      exact pullback.condition_assoc (f := c.f i) (g := c.f j) sX
    · simp [t, hfg]
  let F := c.glueMorphisms f hcompat
  have hF : ∀ i, c.f i ≫ F = f i := c.ι_glueMorphisms f hcompat
  refine ⟨F, c.hom_ext _ _ (fun i => ?_), ?_⟩
  · rw [← Category.assoc, hF]
    exact hfs i
  · let i := genericPoint X
    rw [← genericToOpen_ι (U i) ⟨i, hx i⟩, Category.assoc]
    change genericToOpen (U i) ⟨i, hx i⟩ ≫ (c.f i ≫ F) = g
    rw [hF]
    exact hfg i


end AlgebraicGeometry.Scheme
