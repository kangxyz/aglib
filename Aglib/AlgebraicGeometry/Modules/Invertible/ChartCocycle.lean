/-
Copyright (c) 2026 algebraic-geometry contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.Modules.Invertible.Gluing
public import Aglib.AlgebraicGeometry.Modules.Invertible.Gluing.Morphisms
public import Aglib.AlgebraicGeometry.Modules.Invertible.Trivialization
public import Aglib.AlgebraicGeometry.Modules.Invertible.Dual
public import Aglib.Algebra.Category.ModuleCat.Presheaf.SheafificationRestriction

/-!
# The chart cocycle of a line bundle and smallness of the Picard group

Choose, for every point `x` of a scheme `X`, a unit chart `L|_{U_x} ≅ O_{U_x}` of a line
bundle `L` (`chartOpen`, `chartIso`). The chart coordinates of the chart generators on the
overlaps are units satisfying the cocycle identity (`chartCocycle`, a `UnitCocycle` indexed
by the points of `X`). The canonical morphism from the glued line bundle of this cocycle to
`L`, which sends each local generator to the chart generator, is bijective on every open
inside a chart and hence an isomorphism (`chartReconstructionIso`).

Consequently every class in `PicardGroup X` is the class of a line bundle glued from a
unit cocycle indexed by the points of `X`, and the data of such cocycles form a type in
`Type u`. This gives `Small.{u} (PicardGroup X)` for every `X : Scheme.{u}`
(`small_picardGroup`), with no hypothesis on `X`.

`Scheme.Modules.isIso_of_forall_bijective_app` is the local criterion used: a morphism of
module sheaves that is bijective on all sections over opens inside the members of an open
cover is an isomorphism.
-/

@[expose] public section

noncomputable section
-- Sections of `M.over W` and of `M` over `Over.mk (homOfLE h)` agree only after unfolding the
-- over-site and `X.Modules` abbreviations; most chart computations below need this, as in the
-- lower `Invertible.Gluing` and `Invertible.Trivialization` leaves.
set_option backward.isDefEq.respectTransparency false

open CategoryTheory AlgebraicGeometry Opposite TopologicalSpace

universe u

namespace AlgebraicGeometry.Scheme.Modules

variable {X : Scheme.{u}}

/-- A morphism of module sheaves is an isomorphism if every point has an open neighbourhood
on whose subopens all section maps are bijective. -/
theorem isIso_of_forall_bijective_app {M N : SheafOfModules.{u} X.ringCatSheaf} (φ : M ⟶ N)
    (h : ∀ x : X, ∃ U : X.Opens, x ∈ U ∧
      ∀ W : X.Opens, W ≤ U → Function.Bijective (φ.val.app (op W))) : IsIso φ := by
  have hinj : _root_.PresheafOfModules.IsLocallyInjective (Opens.grothendieckTopology X)
      φ.val := by
    constructor
    intro V s t hst x hxV
    obtain ⟨U, hxU, hf⟩ := h x
    let W := U ⊓ V.unop
    let i : W ⟶ V.unop := homOfLE inf_le_right
    refine ⟨W, i, ?_, hxU, hxV⟩
    apply (hf W inf_le_left).injective
    change φ.val.app (op W) (M.val.map i.op s) = φ.val.app (op W) (M.val.map i.op t)
    rw [_root_.PresheafOfModules.naturality_apply, _root_.PresheafOfModules.naturality_apply]
    exact congrArg (N.val.map i.op) hst
  have hsurj : _root_.PresheafOfModules.IsLocallySurjective (Opens.grothendieckTopology X)
      φ.val := by
    constructor
    intro V s x hxV
    obtain ⟨U, hxU, hf⟩ := h x
    let W := U ⊓ V
    let i : W ⟶ V := homOfLE inf_le_right
    refine ⟨W, i, ?_, hxU, hxV⟩
    exact (hf W inf_le_left).surjective (N.val.map i.op s)
  have : IsIso ((SheafOfModules.forget X.ringCatSheaf).map φ) :=
    _root_.PresheafOfModules.isIso_of_locallyBijective φ.val M.isSheaf N.isSheaf
  exact isIso_of_reflects_iso φ (SheafOfModules.forget _)

end AlgebraicGeometry.Scheme.Modules

namespace AlgebraicGeometry.Scheme.Modules.Invertible

variable {X : Scheme.{u}}

section Chart

variable (M : X.Modules) (W : X.Opens)
  (e : M.over W ≅ SheafOfModules.unit (X.ringCatSheaf.over W))

/-- The generator of a unit chart over a subopen `V ≤ W`. -/
abbrev chartGeneratorOn (V : X.Opens) (h : V ≤ W) : M.val.obj (op V) :=
  (chartSectionEquiv X M W e V h).symm 1

theorem chartSectionEquiv_chartGeneratorOn (V : X.Opens) (h : V ≤ W) :
    chartSectionEquiv X M W e V h (chartGeneratorOn M W e V h) = 1 :=
  LinearEquiv.apply_symm_apply _ _

/-- Every section in a unit chart is its coordinate times the chart generator. -/
theorem chartSectionEquiv_smul_chartGeneratorOn (V : X.Opens) (h : V ≤ W)
    (s : M.val.obj (op V)) :
    chartSectionEquiv X M W e V h s • chartGeneratorOn M W e V h = s := by
  apply (chartSectionEquiv X M W e V h).injective
  rw [LinearEquiv.map_smul, chartSectionEquiv_chartGeneratorOn, smul_eq_mul, mul_one]

/-- Chart coordinates commute with restriction. -/
theorem chartSectionEquiv_restrict {V V' : X.Opens} (h : V ≤ W) (h' : V' ≤ V)
    (s : M.val.obj (op V)) :
    chartSectionEquiv X M W e V' (h'.trans h) (M.val.map (homOfLE h').op s) =
      X.presheaf.map (homOfLE h').op (chartSectionEquiv X M W e V h s) := by
  let i : Over.mk (homOfLE (h'.trans h)) ⟶ Over.mk (homOfLE h) := Over.homMk (homOfLE h')
  exact _root_.PresheafOfModules.naturality_apply e.hom.val i.op s

theorem chartGeneratorOn_restrict {V V' : X.Opens} (h : V ≤ W) (h' : V' ≤ V) :
    M.val.map (homOfLE h').op (chartGeneratorOn M W e V h) =
      chartGeneratorOn M W e V' (h'.trans h) := by
  apply (chartSectionEquiv X M W e V' (h'.trans h)).injective
  rw [chartSectionEquiv_restrict M W e h h', chartSectionEquiv_chartGeneratorOn,
    chartSectionEquiv_chartGeneratorOn, map_one]

end Chart

section Cocycle

variable (L : LineBundle X)

theorem exists_chart (x : X) : ∃ U : X.Opens, x ∈ U ∧
    Nonempty (L.val.over U ≅ SheafOfModules.unit (X.ringCatSheaf.over U)) :=
  (isLocallyRankOne_iff_local_unit X L.val).mp L.property x

/-- A chosen unit-chart open of `L` around the point `x`. -/
def chartOpen (x : X) : X.Opens := (exists_chart L x).choose

theorem mem_chartOpen (x : X) : x ∈ chartOpen L x := (exists_chart L x).choose_spec.1

/-- The chosen unit chart of `L` around the point `x`. -/
def chartIso (x : X) :
    L.val.over (chartOpen L x) ≅ SheafOfModules.unit (X.ringCatSheaf.over (chartOpen L x)) :=
  (exists_chart L x).choose_spec.2.some

theorem iSup_chartOpen : iSup (chartOpen L) = ⊤ :=
  eq_top_iff.mpr fun x _ => Opens.mem_iSup.mpr ⟨x, mem_chartOpen L x⟩

/-- Coordinates in the chosen chart at `x`. -/
abbrev chartCoord (x : X) (V : X.Opens) (h : V ≤ chartOpen L x) :
    L.val.val.obj (op V) ≃ₗ[Γ(X, V)] Γ(X, V) :=
  chartSectionEquiv X L.val (chartOpen L x) (chartIso L x) V h

/-- The generator of the chosen chart at `x`, over a subopen. -/
abbrev chartGen (x : X) (V : X.Opens) (h : V ≤ chartOpen L x) : L.val.val.obj (op V) :=
  chartGeneratorOn L.val (chartOpen L x) (chartIso L x) V h

theorem chartCoord_chartGen_mul (x y z : X) (V : X.Opens) (hx : V ≤ chartOpen L x)
    (hy : V ≤ chartOpen L y) (hz : V ≤ chartOpen L z) :
    chartCoord L y V hy (chartGen L z V hz) * chartCoord L x V hx (chartGen L y V hy) =
      chartCoord L x V hx (chartGen L z V hz) := by
  conv_rhs => rw [← chartSectionEquiv_smul_chartGeneratorOn L.val (chartOpen L y) (chartIso L y)
    V hy (chartGen L z V hz)]
  rw [LinearEquiv.map_smul, smul_eq_mul]

theorem chartCoord_chartGen_self (x : X) (V : X.Opens) (hx : V ≤ chartOpen L x) :
    chartCoord L x V hx (chartGen L x V hx) = 1 :=
  chartSectionEquiv_chartGeneratorOn _ _ _ _ _

/-- The transition unit `chart_x(gen_y)` on the overlap of the charts at `x` and `y`. -/
def chartTransition (x y : X) : (Γ(X, chartOpen L x ⊓ chartOpen L y))ˣ where
  val := chartCoord L x _ inf_le_left (chartGen L y _ inf_le_right)
  inv := chartCoord L y _ inf_le_right (chartGen L x _ inf_le_left)
  val_inv := (chartCoord_chartGen_mul L y x y _ inf_le_right inf_le_left inf_le_right).trans
    (chartCoord_chartGen_self L y _ inf_le_right)
  inv_val := (chartCoord_chartGen_mul L x y x _ inf_le_left inf_le_right inf_le_left).trans
    (chartCoord_chartGen_self L x _ inf_le_left)

theorem chartTransition_restrict (x y : X) {V : X.Opens} (hx : V ≤ chartOpen L x)
    (hy : V ≤ chartOpen L y) :
    (Units.map (sectionRestrict X (le_inf hx hy)).toMonoidHom (chartTransition L x y)).val =
      chartCoord L x V hx (chartGen L y V hy) := by
  change X.presheaf.map (homOfLE (le_inf hx hy)).op
    (chartCoord L x _ inf_le_left (chartGen L y _ inf_le_right)) = _
  rw [← chartSectionEquiv_restrict, chartGeneratorOn_restrict]

/-- The transition cocycle of the chosen charts, indexed by the points of `X`. -/
def chartCocycle : UnitCocycle (chartOpen L) where
  transition := chartTransition L
  cocycle x y z V hx hy hz := by
    apply Units.ext
    rw [Units.val_mul, chartTransition_restrict, chartTransition_restrict,
      chartTransition_restrict, mul_comm]
    exact chartCoord_chartGen_mul L x y z V hx hy hz

theorem chartGenerator_restrict_eq_transition_smul (x y : X) (V : X.Opens)
    (hx : V ≤ chartOpen L x) (hy : V ≤ chartOpen L y) :
    L.val.val.map (homOfLE hy).op (chartGenerator X L.val (chartOpen L y) (chartIso L y)) =
      ((chartCocycle L).transitionOn x y hx hy).val •
        L.val.val.map (homOfLE hx).op (chartGenerator X L.val (chartOpen L x) (chartIso L x)) := by
  rw [chartGenerator_restrict, chartGenerator_restrict]
  change chartGen L y V hy = (Units.map (sectionRestrict X (le_inf hx hy)).toMonoidHom
    (chartTransition L x y)).val • chartGen L x V hx
  rw [chartTransition_restrict]
  exact (chartSectionEquiv_smul_chartGeneratorOn _ _ _ _ _ _).symm

/-- The canonical morphism from the glued line bundle of the chart cocycle to `L`, sending
each local generator to the chart generator. -/
def chartReconstructionHom : (chartCocycle L).sheaf ⟶ L.val :=
  (chartCocycle L).homOfLocalSections L.val (iSup_chartOpen L)
    (fun x => chartGenerator X L.val (chartOpen L x) (chartIso L x))
    (chartGenerator_restrict_eq_transition_smul L)

theorem chartReconstructionHom_app_bijective (x : X) (W : X.Opens)
    (hW : W ≤ chartOpen L x) :
    Function.Bijective ((chartReconstructionHom L).val.app (op W)) := by
  have hφ : ⇑((chartReconstructionHom L).val.app (op W)) =
      (fun r : Γ(X, W) => r • chartGen L x W hW) ∘ (chartCocycle L).localSectionsEquiv x hW := by
    funext s
    rw [Function.comp_apply, chartReconstructionHom,
      UnitCocycle.homOfLocalSections_apply _ _ _ _ _ x W hW s, chartGenerator_restrict]
  rw [hφ]
  refine Function.Bijective.comp ⟨fun r r' hr => ?_, fun s => ⟨chartCoord L x W hW s,
    chartSectionEquiv_smul_chartGeneratorOn _ _ _ _ _ s⟩⟩ (LinearEquiv.bijective _)
  have h := congrArg (chartCoord L x W hW) hr
  rw [LinearEquiv.map_smul, LinearEquiv.map_smul, chartCoord_chartGen_self, smul_eq_mul,
    smul_eq_mul, mul_one, mul_one] at h
  exact h

instance chartReconstructionHom_isIso : IsIso (chartReconstructionHom L) :=
  Scheme.Modules.isIso_of_forall_bijective_app _ fun x =>
    ⟨chartOpen L x, mem_chartOpen L x, fun W hW => chartReconstructionHom_app_bijective L x W hW⟩

/-- Every line bundle is isomorphic to the line bundle glued from its chart cocycle. -/
def chartReconstructionIso : (chartCocycle L).sheaf ≅ L.val :=
  asIso (chartReconstructionHom L)

theorem classOf_chartCocycle_lineBundle :
    classOf X ((chartCocycle L).lineBundle (iSup_chartOpen L)) = classOf X L :=
  Quotient.sound ⟨chartReconstructionIso L⟩

end Cocycle

/-- Every class in the Picard group is glued from a unit cocycle indexed by the points. -/
theorem exists_unitCocycle_classOf (a : PicardGroup X) :
    ∃ (U : X → X.Opens) (c : UnitCocycle U) (hU : iSup U = ⊤), classOf X (c.lineBundle hU) = a := by
  induction a using Quotient.inductionOn with
  | h L => exact ⟨chartOpen L, chartCocycle L, iSup_chartOpen L, classOf_chartCocycle_lineBundle L⟩

/-- The Picard group of a scheme in `Scheme.{u}` is `u`-small. -/
instance small_picardGroup : Small.{u} (PicardGroup X) := by
  let f : (Σ U : X → X.Opens, {c : UnitCocycle U // iSup U = ⊤}) → PicardGroup X :=
    fun d => classOf X (d.2.1.lineBundle d.2.2)
  refine small_of_surjective (f := f) fun a => ?_
  obtain ⟨U, c, hU, h⟩ := exists_unitCocycle_classOf a
  exact ⟨⟨U, c, hU⟩, h⟩

end AlgebraicGeometry.Scheme.Modules.Invertible
