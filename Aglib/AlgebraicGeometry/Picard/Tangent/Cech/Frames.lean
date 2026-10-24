/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.Picard.Tangent.Cech.Cocycle
public import Aglib.AlgebraicGeometry.Modules.Invertible.Gluing.Frames
public import Aglib.AlgebraicGeometry.Modules.Invertible.SquareZero.AffineMorphism

/-!
# Normalized frames: every class in the kernel of `i^*` comes from a pair cocycle

Let `i : X ⟶ Y`, `p : Y ⟶ X` with `i ≫ p = 𝟙 X` and an `IdealGenerator` `G` (for example the
dual numbers `X[ε]`), and let `U : ι → X.Opens` cover `X` by affine opens whose preimages
`p⁻¹ U j` and pairwise intersections `U j ⊓ U l` are affine.

* `IdealGenerator.chartInclusion U j : U j ⟶ p⁻¹ U j`, the restriction of `i`; its map on
  global sections is the reduction, which is surjective with square-zero kernel.
* `IdealGenerator.exists_frame`: a line bundle `L` on `Y` with `i^* L` trivial is trivial on
  every `p⁻¹ U j`, by lifting along `chartInclusion` with
  `exists_lineBundle_iso_lift_affine_of_square_zero`.
* `IdealGenerator.exists_cocycleClass_eq`: every class in the kernel of `i^*` is the class of
  `1 + ε b` for a pair cocycle `b` (`IdealGenerator.cocycleClass`).

The proof of the last statement normalizes the frames instead of lifting a prescribed
trivialization: the frames give a unit cocycle `g` with `L ≅ g`; its reduction `i^♯ g` glues to
`i^* L`, which is trivial, so `i^♯ g` is cohomologous to `1` through units `y j`; changing the
frames by `p^♯ (y j)⁻¹` gives a cocycle with reduction `1`, which is `1 + ε b` for a pair
cocycle `b`. The normalization is a route choice; compare Kleiman, arXiv:math/0504020v1, proof of
Thm 5.11, p. 43 (the kernel from the truncated exponential sequence), and Stacks, Tag 0B8R (Čech
`H^1` and torsors trivial on a cover).
-/

@[expose] public section

noncomputable section


open CategoryTheory CategoryTheory.Limits TopologicalSpace Opposite
open AlgebraicGeometry.Scheme.Modules
open AlgebraicGeometry.Scheme.Modules.Invertible
open AlgebraicGeometry.Scheme.Modules.Invertible.PullbackTensor.Local

universe u

namespace AlgebraicGeometry.Scheme.SplitThickening.IdealGenerator

variable {X Y : Scheme.{u}} {i : X ⟶ Y} {p : Y ⟶ X} {h : i ≫ p = 𝟙 X}
  (G : IdealGenerator i p h) {ι : Type u} (U : ι → X.Opens)

private theorem sq_comap_eq_bot {R S : Type u} [CommRing R] [CommRing S] (f : R →+* S)
    (hf : Function.Injective f) (I : Ideal S) (hI : I ^ 2 = ⊥) : (I.comap f) ^ 2 = ⊥ := by
  rw [pow_two]
  apply le_antisymm _ bot_le
  apply Ideal.mul_le.mpr
  intro x hx y hy
  apply Ideal.mem_bot.mpr
  apply hf
  rw [map_mul, map_zero]
  have hxy : f x * f y ∈ I ^ 2 := by
    rw [pow_two]
    exact Ideal.mul_mem_mul hx hy
  rw [hI] at hxy
  exact Ideal.mem_bot.mp hxy

variable (i p h) in
/-- The restriction `U j ⟶ p⁻¹ U j` of the closed fibre `i`. -/
abbrev chartInclusion (j : ι) : (U j).toScheme ⟶ (p ⁻¹ᵁ U j).toScheme :=
  i.resLE (p ⁻¹ᵁ U j) (U j) (preimage_preimage_eq i p h (U j)).ge

theorem chartInclusion_comp_ι (j : ι) :
    chartInclusion i p h U j ≫ (p ⁻¹ᵁ U j).ι = (U j).ι ≫ i :=
  Scheme.Hom.resLE_comp_ι _ _

-- Sections of `p_* 𝒪_Y` match the sections of `Y` over preimages only after unfolding.
set_option backward.isDefEq.respectTransparency false in
/-- On global sections, `chartInclusion` is the reduction. -/
theorem chartInclusion_appTop (j : ι) :
    (chartInclusion i p h U j).appTop = (p ⁻¹ᵁ U j).topIso.hom ≫
      (reduction i p h).hom.app (op (U j)) ≫ (U j).topIso.inv := by
  change (i.resLE (p ⁻¹ᵁ U j) (U j) _).app ⊤ = _
  rw [Scheme.Hom.resLE_app_top, appLE_eq_reduction]

theorem chartInclusion_appTop_surjective (j : ι) :
    Function.Surjective (chartInclusion i p h U j).appTop.hom := by
  rw [chartInclusion_appTop]
  simp only [CommRingCat.hom_comp, RingHom.coe_comp]
  refine (ConcreteCategory.bijective_of_isIso (U j).topIso.inv).surjective.comp
    (Function.Surjective.comp ?_
      (ConcreteCategory.bijective_of_isIso (p ⁻¹ᵁ U j).topIso.hom).surjective)
  intro a
  exact ⟨(p.app (U j)).hom a, reduction_projection i p h (op (U j)) a⟩

include G in
-- Sections of `p_* 𝒪_Y` match the sections of `Y` over preimages only after unfolding.
set_option backward.isDefEq.respectTransparency false in
theorem chartInclusion_ker_sq (j : ι) :
    RingHom.ker (chartInclusion i p h U j).appTop.hom ^ 2 = ⊥ := by
  have hinj := (ConcreteCategory.bijective_of_isIso (U j).topIso.inv).injective
  rw [chartInclusion_appTop, CommRingCat.hom_comp, CommRingCat.hom_comp, RingHom.comp_assoc,
    RingHom.ker_comp_of_injective _ hinj, ← RingHom.comap_ker]
  exact sq_comap_eq_bot _ (ConcreteCategory.bijective_of_isIso _).injective _
    (G.reduction_ker_sq (op (U j)))

variable (hU₁ : ∀ j, IsAffineOpen (U j)) (hV₁ : ∀ j, IsAffineOpen (p ⁻¹ᵁ U j))

include G hU₁ hV₁ in
/-- A line bundle whose pullback along `i` is trivial is trivial on every `p⁻¹ U j`. -/
theorem exists_frame (L : LineBundle Y)
    (t : (Scheme.Modules.pullback i).obj L.val ≅ SheafOfModules.unit X.ringCatSheaf) (j : ι) :
    Nonempty (L.val.over (p ⁻¹ᵁ U j) ≅
      SheafOfModules.unit (Y.ringCatSheaf.over (p ⁻¹ᵁ U j))) := by
  have : IsAffine (U j).toScheme := hU₁ j
  have : IsAffine (p ⁻¹ᵁ U j).toScheme := hV₁ j
  let ij := chartInclusion i p h U j
  let L₁ : LineBundle (p ⁻¹ᵁ U j).toScheme := pullbackLineBundle (p ⁻¹ᵁ U j).ι L
  let M₁ : LineBundle (p ⁻¹ᵁ U j).toScheme := trivialLineBundle _
  let e : (Scheme.Modules.pullback ij).obj L₁.val ≅ (Scheme.Modules.pullback ij).obj M₁.val :=
    (Scheme.Modules.pullbackComp ij (p ⁻¹ᵁ U j).ι).app L.val ≪≫
      (Scheme.Modules.pullbackCongr
        (chartInclusion_comp_ι (i := i) (p := p) (h := h) U j)).app L.val ≪≫
      ((Scheme.Modules.pullbackComp (U j).ι i).app L.val).symm ≪≫
      (Scheme.Modules.pullback (U j).ι).mapIso t ≪≫
      pullbackUnitIso (U j).ι ≪≫ (pullbackUnitIso ij).symm ≪≫
      (Scheme.Modules.pullback ij).mapIso (coproductUniqueIso
        (fun _ : PUnit.{u + 1} => SheafOfModules.unit (p ⁻¹ᵁ U j).toScheme.ringCatSheaf)).symm
  obtain ⟨e', -⟩ := exists_lineBundle_iso_lift_affine_of_square_zero ij
    (chartInclusion_appTop_surjective (i := i) (p := p) (h := h) U j)
    (G.chartInclusion_ker_sq U j) L₁ M₁ e
  exact ⟨(Scheme.Modules.overEquiv (p ⁻¹ᵁ U j)).functor.preimageIso
    ((Scheme.Modules.overFunctorEquiv (p ⁻¹ᵁ U j)).app L.val ≪≫
      (Scheme.Modules.restrictFunctorIsoPullback (p ⁻¹ᵁ U j).ι).app L.val ≪≫ e' ≪≫
      coproductUniqueIso
        (fun _ : PUnit.{u + 1} => SheafOfModules.unit (p ⁻¹ᵁ U j).toScheme.ringCatSheaf) ≪≫
      (overUnitIso (p ⁻¹ᵁ U j)).symm)⟩

/-- Reduction commutes with restriction on units. -/
theorem units_map_reduction_restrict {V W : X.Opens} (hVW : V ≤ W) (hp : p ⁻¹ᵁ V ≤ p ⁻¹ᵁ W)
    (g : (Γ(Y, p ⁻¹ᵁ W))ˣ) :
    Units.map ((reduction i p h).hom.app (op V)).hom.toMonoidHom
        (Units.map (sectionRestrict Y hp).toMonoidHom g) =
      Units.map (sectionRestrict X hVW).toMonoidHom
        (Units.map ((reduction i p h).hom.app (op W)).hom.toMonoidHom g) := by
  apply Units.ext
  have e := congrArg (fun φ => φ.hom (g : Γ(Y, p ⁻¹ᵁ W)))
    ((reduction i p h).hom.naturality (homOfLE hVW).op)
  simp only [CommRingCat.hom_comp] at e
  exact e

variable (hU : iSup U = ⊤)

include hU₁ hV₁ in
-- Sections of `p_* 𝒪_Y` match the sections of `Y` over preimages only after unfolding.
set_option backward.isDefEq.respectTransparency false in
/-- Every class in the kernel of `i^*` is the class of `1 + ε b` for a pair cocycle `b`. -/
theorem exists_cocycleClass_eq (hU₂ : ∀ j l, IsAffineOpen (U j ⊓ U l)) (c : PicardGroup Y)
    (hc : pullbackHom i c = 0) : ∃ b : pairCocycles U, G.cocycleClass U hU b = c := by
  induction c using Quotient.inductionOn with | h L =>
  have hV : iSup (fun j => p ⁻¹ᵁ U j) = ⊤ := p.iSup_preimage_eq_top hU
  -- A trivialization of `i^* L`.
  obtain ⟨t₀⟩ := (class_eq_iff X (pullbackLineBundle i L) (trivialLineBundle X)).mp hc
  let t : (Scheme.Modules.pullback i).obj L.val ≅ SheafOfModules.unit X.ringCatSheaf :=
    t₀ ≪≫ coproductUniqueIso (fun _ : PUnit.{u + 1} => SheafOfModules.unit X.ringCatSheaf)
  -- Frames of `L` on the preimages and their cocycle `g`.
  have hframe := fun j => G.exists_frame U hU₁ hV₁ L t j
  let e : ∀ j, L.val.over (p ⁻¹ᵁ U j) ≅ SheafOfModules.unit (Y.ringCatSheaf.over (p ⁻¹ᵁ U j)) :=
    fun j => (hframe j).some
  let g : UnitCocycle (fun j => p ⁻¹ᵁ U j) := LocalFrames.cocycle (fun j => p ⁻¹ᵁ U j) L.val e
  have hgL : classOf Y (g.lineBundle hV) = classOf Y L :=
    (class_eq_iff Y _ _).mpr ⟨LocalFrames.sheafIso (fun j => p ⁻¹ᵁ U j) L.val e hV⟩
  -- The reduction of `g` is cohomologous to `1`.
  have hpre : ∀ j, i ⁻¹ᵁ (p ⁻¹ᵁ U j) = U j := fun j => preimage_preimage_eq i p h (U j)
  let x : UnitCocycle U := g.pullbackCocycle i hpre
  have hx : classOf X (x.lineBundle hU) = 0 := by
    have h₁ := g.classOf_pullbackLineBundle i hpre hV
    have h₂ : classOf X (pullbackLineBundle i (g.lineBundle hV)) =
        classOf X (pullbackLineBundle i L) := congrArg (pullbackClass i) hgL
    exact h₁.symm.trans (h₂.trans hc)
  obtain ⟨y, hy⟩ := (UnitCocycle.classOf_lineBundle_eq_zero_iff hU x).mp hx
  -- Normalize the frames.
  let g' : UnitCocycle (fun j => p ⁻¹ᵁ U j) :=
    g.twist fun j => (Units.map (p.app (U j)).hom.toMonoidHom (y j))⁻¹
  have hg' : classOf Y (g'.lineBundle hV) = classOf Y L :=
    ((UnitCocycle.classOf_lineBundle_eq_iff hV g g').mpr ⟨_, g.cohomologous_twist
      fun j => (Units.map (p.app (U j)).hom.toMonoidHom (y j))⁻¹⟩).symm.trans hgL
  have hred : ∀ j l, Units.map ((reduction i p h).hom.app (op (U j ⊓ U l))).hom.toMonoidHom
      (g'.transition j l) = 1 := by
    intro j l
    have hyjl : x.transition j l * Units.map (sectionRestrict X inf_le_right).toMonoidHom (y l) =
        Units.map (sectionRestrict X inf_le_left).toMonoidHom (y j) := by
      have hyjl' := hy j l
      rw [UnitCocycle.one_transition, one_mul] at hyjl'
      exact hyjl'
    have hxjl : x.transition j l =
        Units.map ((reduction i p h).hom.app (op (U j ⊓ U l))).hom.toMonoidHom
          (g.transition j l) := by
      change Units.map (i.appLE (p ⁻¹ᵁ (U j ⊓ U l)) (U j ⊓ U l) _).hom.toMonoidHom
        (g.transition j l) = _
      rw [appLE_eq_reduction (h := h)]
      rfl
    have hj : Units.map ((reduction i p h).hom.app (op (U j ⊓ U l))).hom.toMonoidHom
        (Units.map (sectionRestrict Y
          (inf_le_left : p ⁻¹ᵁ U j ⊓ p ⁻¹ᵁ U l ≤ p ⁻¹ᵁ U j)).toMonoidHom
          (Units.map (p.app (U j)).hom.toMonoidHom (y j))) =
        Units.map (sectionRestrict X inf_le_left).toMonoidHom (y j) := by
      have e := units_map_reduction_restrict (h := h) (inf_le_left : U j ⊓ U l ≤ U j)
        ((Opens.map p.base).monotone inf_le_left) (Units.map (p.app (U j)).hom.toMonoidHom (y j))
      rw [reduction_units_map_projection] at e
      exact e
    have hl : Units.map ((reduction i p h).hom.app (op (U j ⊓ U l))).hom.toMonoidHom
        (Units.map (sectionRestrict Y
          (inf_le_right : p ⁻¹ᵁ U j ⊓ p ⁻¹ᵁ U l ≤ p ⁻¹ᵁ U l)).toMonoidHom
          (Units.map (p.app (U l)).hom.toMonoidHom (y l))) =
        Units.map (sectionRestrict X inf_le_right).toMonoidHom (y l) := by
      have e := units_map_reduction_restrict (h := h) (inf_le_right : U j ⊓ U l ≤ U l)
        ((Opens.map p.base).monotone inf_le_right) (Units.map (p.app (U l)).hom.toMonoidHom (y l))
      rw [reduction_units_map_projection] at e
      exact e
    change Units.map ((reduction i p h).hom.app (op (U j ⊓ U l))).hom.toMonoidHom
      ((g.twist fun j => (Units.map (p.app (U j)).hom.toMonoidHom (y j))⁻¹).transition j l) = 1
    rw [UnitCocycle.twist_transition]
    simp only [map_mul, map_inv, inv_inv]
    rw [hj, hl, ← hxjl, ← hyjl, mul_inv, mul_inv_cancel_left, inv_mul_cancel]
  -- The normalized cocycle is `1 + ε b`.
  choose b hb using fun j l => G.exists_oneAdd_eq (U j ⊓ U l) (hU₂ j l) (g'.transition j l)
    (hred j l)
  have hcoc : b ∈ pairCocycles U := by
    rw [mem_pairCocycles_iff]
    intro j l m T hj hl hm
    have hT : ∀ {W : X.Opens} (hW : T ≤ W), p ⁻¹ᵁ T ≤ p ⁻¹ᵁ W :=
      fun hW => (Opens.map p.base).monotone hW
    have hcoc' : Units.map (sectionRestrict Y (hT (le_inf hj hl))).toMonoidHom
          (G.oneAdd (U j ⊓ U l) (b j l)) *
        Units.map (sectionRestrict Y (hT (le_inf hl hm))).toMonoidHom
          (G.oneAdd (U l ⊓ U m) (b l m)) =
        Units.map (sectionRestrict Y (hT (le_inf hj hm))).toMonoidHom
          (G.oneAdd (U j ⊓ U m) (b j m)) := by
      have := g'.cocycle j l m (p ⁻¹ᵁ T) (hT hj) (hT hl) (hT hm)
      rw [← hb j l, ← hb l m, ← hb j m] at this
      exact this
    rw [G.units_map_oneAdd (le_inf hj hl), G.units_map_oneAdd (le_inf hl hm),
      G.units_map_oneAdd (le_inf hj hm), ← G.oneAdd_add] at hcoc'
    exact G.oneAdd_injective T hcoc'
  refine ⟨⟨b, hcoc⟩, ?_⟩
  have hg'b : G.oneAddCocycle U ⟨b, hcoc⟩ = g' := UnitCocycle.ext fun j l => hb j l
  rw [cocycleClass_apply, hg'b]
  exact hg'

end AlgebraicGeometry.Scheme.SplitThickening.IdealGenerator
