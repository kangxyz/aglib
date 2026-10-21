/-
Copyright (c) 2026 kangxyz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/

module

public import Aglib.AlgebraicGeometry.Morphisms.FiniteEtale.Descent.FiniteSetLocalCharts
public import Mathlib.AlgebraicGeometry.Morphisms.UniversallyOpen

/-! Zariski-local reduction to a single surjective affine etale trivializing chart. -/

@[expose] public section

noncomputable section
set_option autoImplicit false
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open CategoryTheory CategoryTheory.Category CategoryTheory.Limits AlgebraicGeometry
open TopologicalSpace.Opens

namespace AlgebraicGeometry.Scheme.FiniteEtale.SheafDescent

universe u
variable {X : Scheme.{u}} (F : Scheme.EtaleCohomology.SetSheaf X) (x : X)

/-- An affine open neighborhood with one actual surjective affine etale chart
on which the original sheaf is the original finite constant value. -/
structure AffineTrivializingNeighborhood where
  /-- The affine open neighborhood of the chosen point `x`. -/
  base : Scheme.{u}
  affine_base : IsAffine base
  /-- The open immersion of the affine neighborhood into `X`. -/
  baseMap : base ⟶ X
  open_baseMap : IsOpenImmersion baseMap
  /-- The point of the neighborhood mapping to `x` by `point_eq`. -/
  point : base
  point_eq : baseMap point = x
  /-- The coordinate ring of the affine trivializing chart. -/
  ring : CommRingCat.{u}
  /-- The surjective étale morphism from `Spec ring` to the affine neighborhood. -/
  chart : Spec ring ⟶ base
  etale_chart : Etale chart
  surjective_chart : Surjective chart
  /-- The finite set of constant values on the trivializing chart. -/
  value : Type u
  finite_value : Finite value
  /-- The isomorphism from the pullback of `F` along `chart ≫ baseMap` to the constant
  sheaf with value `ULift value`. -/
  trivialization : (Scheme.EtaleCohomology.setInverseImage (chart ≫ baseMap)).obj F ≅
    (constantSheaf (Scheme.smallEtaleTopology (Spec ring)) (Type (u + 1))).obj (ULift.{u + 1} value)

attribute [instance] AffineTrivializingNeighborhood.affine_base
  AffineTrivializingNeighborhood.open_baseMap AffineTrivializingNeighborhood.etale_chart
  AffineTrivializingNeighborhood.surjective_chart AffineTrivializingNeighborhood.finite_value

end AlgebraicGeometry.Scheme.FiniteEtale.SheafDescent

namespace AlgebraicGeometry.Scheme.EtaleCohomology.FiniteSetLocalTrivialization

universe u
variable {X : Scheme.{u}} {F : Scheme.EtaleCohomology.SetSheaf X}

open AlgebraicGeometry.Scheme.FiniteEtale.SheafDescent

/-- Choose an affine neighborhood of `x` and a single surjective affine étale chart
trivializing `F`, from the supplied finite-set local trivialization `t`. -/
def affineTrivializingNeighborhood
    (t : Scheme.EtaleCohomology.FiniteSetLocalTrivialization F) (x : X) :
      AffineTrivializingNeighborhood
      F x := by
  apply Classical.choice
  obtain ⟨V₀, hV, hxV, _⟩ := isBasis_iff_nbhd.mp X.isBasis_affineOpens (mem_top x)
  let V : X.Opens := V₀
  have : IsAffine V.toScheme := hV
  let xV : V.toScheme := ⟨x, hxV⟩
  obtain ⟨i, y, hy⟩ := t.covers x
  let a := (t.chart i).hom
  obtain ⟨z, hz₁, hz₂⟩ := Scheme.Pullback.exists_preimage_pullback (f := a) (g := V.ι) y xV hy
  obtain ⟨W₀, hW, hzW, _⟩ := isBasis_iff_nbhd.mp
    (Limits.pullback a V.ι).isBasis_affineOpens (mem_top z)
  let W : (Limits.pullback a V.ι).Opens := W₀
  have : IsAffine W.toScheme := hW
  let p : W.toScheme ⟶ V.toScheme := W.ι ≫ pullback.snd a V.ι
  have : Etale p := by dsimp [p, a]; infer_instance
  let O : V.toScheme.Opens := ⟨Set.range p, by simpa using p.isOpenMap _ isOpen_univ⟩
  have hxO : xV ∈ O := by
    refine ⟨⟨z, hzW⟩, ?_⟩
    simpa [p] using hz₂
  obtain ⟨U₀, hU, hxU, hUO⟩ := isBasis_iff_nbhd.mp V.toScheme.isBasis_affineOpens hxO
  let U : V.toScheme.Opens := U₀
  have : IsAffine U.toScheme := hU
  have : IsAffineHom p := inferInstance
  let Q := Limits.pullback p U.ι
  have : IsAffine Q := by dsimp [Q]; infer_instance
  let q : Q ⟶ U.toScheme := pullback.snd p U.ι
  have : Etale q := by dsimp [q]; infer_instance
  have : Surjective q := by
    constructor
    intro u
    obtain ⟨w, hw⟩ := hUO u.property
    obtain ⟨v, hv₁, hv₂⟩ := Scheme.Pullback.exists_preimage_pullback (f := p) (g := U.ι) w u hw
    exact ⟨v, hv₂⟩
  let j : U.toScheme ⟶ X := U.ι ≫ V.ι
  let k : Q ⟶ (t.chart i).left := pullback.fst p U.ι ≫ W.ι ≫ pullback.fst a V.ι
  have square : q ≫ j = k ≫ a := by
    dsimp [q, j, k]
    rw [← Category.assoc, ← pullback.condition]
    dsimp [p]
    simp only [Category.assoc]
    rw [pullback.condition]
  let qS : Spec Γ(Q, ⊤) ⟶ U.toScheme := Q.isoSpec.inv ≫ q
  let kS : Spec Γ(Q, ⊤) ⟶ (t.chart i).left := Q.isoSpec.inv ≫ k
  have squareS : qS ≫ j = kS ≫ a := by
    dsimp [qS, kS]
    simpa only [Category.assoc] using Q.isoSpec.inv ≫= square
  refine ⟨{
    base := U.toScheme
    affine_base := inferInstance
    baseMap := j
    open_baseMap := by dsimp [j]; infer_instance
    point := ⟨xV, hxU⟩
    point_eq := rfl
    ring := Γ(Q, ⊤)
    chart := qS
    etale_chart := by dsimp [qS]; infer_instance
    surjective_chart := by dsimp [qS]; infer_instance
    value := t.smallValue i
    finite_value := inferInstance
    trivialization := ?_ }⟩
  exact eqToIso (congrArg (fun f => (Scheme.EtaleCohomology.setInverseImage f).obj F) squareS) ≪≫
    (setInverseImageComp a kS).app F ≪≫
    (Scheme.EtaleCohomology.setInverseImage kS).mapIso (t.smallTrivialization i) ≪≫
    (setInverseImageConstantIso kS).app (ULift.{u + 1} (t.smallValue i))

end AlgebraicGeometry.Scheme.EtaleCohomology.FiniteSetLocalTrivialization

/- Migration source: the R5Lab/Aglib mirror; exact module in the migration record.
R5 revision c82abf3a72ce1e1cedf4a4f1fe08bea994ad4df5.
SHA256 348ac5caafddfc21c1572906569cd40e7b6248c35a154af2ce3e0d53a26eca68.
Definitions, hypotheses and universes are retained modulo native names. -/
