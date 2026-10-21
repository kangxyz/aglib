/-
Copyright (c) 2026 kangxyz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/

module

/- Current interface basis: 46f53465aaf3b0167049e9c8e9e2294111bb4281.
Original construction and mathematical provenance are retained below. -/
public import Aglib.AlgebraicGeometry.EtaleCohomology.H1.EtaleRestriction
public import Aglib.AlgebraicGeometry.EtaleCohomology.H1.FiniteTrivialization

/-!
# Finite locally constant torsors and their actual finite étale representatives

Construction prerequisite for `K2-018#eq:k2018-pointed-character`, frozen basis
`7f86e4a1763cc4ec35e9b0a8acd659750355a0de`. Finite local constancy refers to
actual inverse-image isomorphisms with finite constant set sheaves. The sole
representability boundary is the existence direction of Stacks 03RV,
Lemma 59.64.4 (https://stacks.math.columbia.edu/tag/03RV), inspected 2026-10-09.
It is an explicit quantified premise and does not assume a classification,
marked fibre equivalence, group action, or cohomology comparison.
-/

@[expose] public section

noncomputable section
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Opposite
open _root_.AlgebraicGeometry.Scheme.FiniteEtale (forget)
namespace AlgebraicGeometry.Scheme.EtaleCohomology
universe u
attribute [local instance] hasSheafifyLarge etaleSubcanonical
variable {X : Scheme.{u}}

/-- Finite local constancy of a set sheaf, by actual étale inverse-image charts. -/
structure FiniteSetLocalTrivialization (F : SetSheaf X) where
  /-- The type indexing the étale charts used for the local trivializations. -/
  index : Type u
  /-- The étale chart over `X` attached to each index. -/
  chart : index → X.Etale
  covers : ∀ x : X, ∃ i, ∃ y : (chart i).left, (chart i).hom y = x
  /-- The type of constant values on each chart, with finiteness recorded by `finite_value` . -/
  value : index → Type (u + 1)
  finite_value : ∀ i, Finite (value i)
  /-- The isomorphism from the inverse image of `F` on each chart to its constant sheaf of
  values. -/
  trivialization : ∀ i, (setInverseImage (chart i).hom).obj F ≅
    (constantSheaf (Scheme.smallEtaleTopology (chart i).left) (Type (u + 1))).obj (value i)

/-- The condition that `F` admits étale local trivializations by finite constant set sheaves. -/
def IsFiniteLocallyConstantSet (F : SetSheaf X) : Prop :=
  Nonempty (FiniteSetLocalTrivialization F)

/-- The actual section sheaf of a finite étale scheme, with the explicit
universe lift used by set sheaves in this package. -/
def finiteRepresentedSetSheaf (Y : Scheme.FiniteEtale X) : SetSheaf X :=
  ⟨(Scheme.Etale.forget X).op ⋙ yoneda.obj Y.obj ⋙ uliftFunctor.{u + 1}, by
    apply (Scheme.Etale.forget X).op_comp_isSheaf_of_isSheaf
      (Scheme.smallEtaleTopology X) (Scheme.etaleTopology.over X)
    apply Presheaf.isSheaf_comp_of_isSheaf
    rw [isSheaf_iff_isSheaf_of_type]
    exact GrothendieckTopology.Subcanonical.isSheaf_of_isRepresentable _⟩

/-- Precisely the finite-locally-constant-to-finite-étale existence direction
of Stacks 03RV. The representative and its actual sheaf isomorphism are the
only output; no morphism, action, or fibre transport is supplied as a premise. -/
structure Stacks03RV (X : Scheme.{u}) : Prop where
  representable : ∀ (F : SetSheaf X), IsFiniteLocallyConstantSet F →
    ∃ Y : Scheme.FiniteEtale X, Nonempty (finiteRepresentedSetSheaf Y ≅ F)

namespace Torsor
variable {L : AbelianSheaf.{u, u + 1} X} (P : Torsor L)

/-- Restrict a section on one chart along an étale test scheme over that chart. -/
def restrictChartSection (U : X.Etale) (s : P.carrier.obj.obj (op U))
    (V : U.left.Etaleᵒᵖ) :
    P.carrier.obj.obj ((siteEtalePostcompose U.hom).op.obj V) :=
  P.carrier.obj.map (MorphismProperty.Over.homMk V.unop.hom rfl (by trivial)).op s

/-- A section on an actual étale chart gives a genuine sheaf isomorphism
between the restricted coefficient sheaf and the restricted torsor. -/
def chartTrivialization (U : X.Etale) (s : P.carrier.obj.obj (op U)) :
    underlyingSetSheaf ((etaleRestriction U.hom).obj L) ≅
      (setEtaleRestriction U.hom).obj P.carrier :=
  ObjectProperty.isoMk _ (NatIso.ofComponents
    (fun V => (P.sectionEquiv ((siteEtalePostcompose U.hom).op.obj V)
      (P.restrictChartSection U s V)).toIso)
    (fun {V W} f => by
      ext a
      change P.action _ (L.obj.map ((siteEtalePostcompose U.hom).op.map f) a)
          (P.restrictChartSection U s W) =
        P.carrier.obj.map ((siteEtalePostcompose U.hom).op.map f)
          (P.action _ a (P.restrictChartSection U s V))
      rw [P.naturality]
      congr 1
      change P.carrier.obj.map _ s = P.carrier.obj.map _ (P.carrier.obj.map _ s)
      rw [← Functor.map_comp_apply]
      apply congrArg (fun a => P.carrier.obj.map a s)
      apply congrArg Quiver.Hom.op
      apply MorphismProperty.Over.Hom.ext
      exact (MorphismProperty.Over.w f.unop).symm))

/-- A local coefficient chart and a torsor section give the actual finite
constant-sheaf chart of the torsor. Finiteness is imposed separately. -/
def finiteChartIso (U : X.Etale) (s : P.carrier.obj.obj (op U))
    (A : AddCommGrpCat.{u + 1})
    (e : (inverseImage U.hom).obj L ≅
      (constantSheaf (Scheme.smallEtaleTopology U.left) AddCommGrpCat.{u + 1}).obj A) :
    (setInverseImage U.hom).obj P.carrier ≅
      (constantSheaf (Scheme.smallEtaleTopology U.left) (Type (u + 1))).obj A :=
  (setInverseImageEtaleIso U.hom).app P.carrier ≪≫
    (P.chartTrivialization U s).symm ≪≫
    (underlyingSetFunctor U.left).mapIso ((inverseImageEtaleIso U.hom).symm.app L ≪≫ e) ≪≫
    (constantCommuteCompose (Scheme.smallEtaleTopology U.left)
      (CategoryTheory.forget AddCommGrpCat.{u + 1})).app A

/-- Simultaneously refine a coefficient chart and the torsor's local
nonemptiness. Every base point has an actual étale chart with both properties. -/
theorem exists_finite_chart (t : FiniteLocalTrivialization L) (x : X) :
    ∃ (U : X.Etale) (y : U.left), U.hom y = x ∧
      ∃ (A : AddCommGrpCat.{u + 1}), Finite A ∧
        Nonempty (P.carrier.obj.obj (op U)) ∧
        Nonempty ((inverseImage U.hom).obj L ≅
          (constantSheaf (Scheme.smallEtaleTopology U.left) AddCommGrpCat.{u + 1}).obj A) := by
  obtain ⟨i, z, hz⟩ := t.covers x
  have hR := P.locally_nonempty (t.chart i)
  change _ ∈ X.smallGrothendieckTopology @Etale (t.chart i) at hR
  rw [Scheme.smallGrothendieckTopology_eq_toGrothendieck_smallPretopology _ le_rfl,
    Scheme.mem_toGrothendieck_smallPretopology] at hR
  obtain ⟨V, g, v, hsec, hge, hv⟩ := hR z
  let : Etale g.left := hge
  refine ⟨V, v, ?_, t.value i, t.finite_value i, hsec, ?_⟩
  · rw [← MorphismProperty.Over.w g]
    change (t.chart i).hom (g.left v) = x
    rw [hv, hz]
  · rw [← MorphismProperty.Over.w g]
    exact ⟨(inverseImageComp (t.chart i).hom g.left).app L ≪≫
      (inverseImage g.left).mapIso (t.trivialization i) ≪≫
      (inverseImageConstantIso g.left).app (t.value i)⟩

/-- A torsor for a finite locally constant abelian sheaf is itself finite
locally constant. The charts and their actual set-sheaf isomorphisms are
constructed from the torsor action and local nonemptiness. -/
def finiteLocalTrivialization (t : FiniteLocalTrivialization L) :
    FiniteSetLocalTrivialization P.carrier := by
  classical
  choose U y hy A hA hs he using P.exists_finite_chart t
  exact {
    index := X
    chart := U
    covers := fun x => ⟨x, y x, hy x⟩
    value := fun x => A x
    finite_value := hA
    trivialization := fun x => P.finiteChartIso (U x) (Classical.choice (hs x)) (A x)
      (Classical.choice (he x)) }

theorem isFiniteLocallyConstant (hL : IsFiniteLocallyConstant L) :
    IsFiniteLocallyConstantSet P.carrier := by
  obtain ⟨t⟩ := hL
  exact ⟨P.finiteLocalTrivialization t⟩

/-- Under exactly Stacks 03RV, choose an actual finite étale representative
of the finite torsor. This is a scheme over X, not an abstract finite set. -/
def finiteEtaleRepresentative (h : Stacks03RV X) (hL : IsFiniteLocallyConstant L) :
    Scheme.FiniteEtale X :=
  Classical.choose (h.representable P.carrier (P.isFiniteLocallyConstant hL))

/-- The selected finite étale scheme represents the actual torsor carrier,
with an actual sheaf isomorphism and the explicit universe lift. -/
def finiteEtaleRepresentativeIso (h : Stacks03RV X) (hL : IsFiniteLocallyConstant L) :
    finiteRepresentedSetSheaf (P.finiteEtaleRepresentative h hL) ≅ P.carrier :=
  Classical.choice (Classical.choose_spec (h.representable P.carrier
    (P.isFiniteLocallyConstant hL)))

end Torsor
end AlgebraicGeometry.Scheme.EtaleCohomology

/- Migration source: the R5Lab/Aglib mirror; exact module in the migration record.
R5 revision c82abf3a72ce1e1cedf4a4f1fe08bea994ad4df5.
SHA256 bdfe2e53905bf1cbdd7ca4e81ee42fd49cb99271c2d47386ab781ffe4778838f.
Definitions, hypotheses and universes are retained modulo native names. -/
