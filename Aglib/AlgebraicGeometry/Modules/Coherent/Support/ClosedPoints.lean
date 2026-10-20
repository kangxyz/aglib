/-
Copyright (c) 2026 kangxyz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.Modules.Coherent.Support.StalkKernel
public import Aglib.AlgebraicGeometry.Modules.Coherent.Support.FinitePushforward

/-!
Native migration from `R5Lab.Aglib.AlgebraicGeometry.Modules.Support.ClosedPoints` at R5 revision
`f8a3314ddecffcada2ec721d26d56a937bed9690`, SHA-256
`fd3661a536bca3fe853d475608225c95f4e33b990f71bb6dcbffd291d697df15`.
Original objects, maps, universes and explicit hypotheses are retained.
Native providers replace duplicate implementations.
-/

@[expose] public section

noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry TopologicalSpace
open _root_.AlgebraicGeometry.Scheme.Modules (support)
open _root_.AlgebraicGeometry.Scheme.Modules.QuasiCoherent (FiniteTypeSheaves
    finiteType_support_isClosed)
open AlgebraicGeometry.Scheme.Modules.Coherent.Support
    AlgebraicGeometry.Scheme.Modules.Coherent.Support
    AlgebraicGeometry.Scheme.Modules.Coherent.Support
attribute [local instance] Abelian.hasFiniteBiproducts Classical.decEq
namespace AlgebraicGeometry.Scheme.Modules.Coherent.Support
universe u
variable (X : Scheme.{u}) [IsNoetherian X]

/-- The actual upper-small-model coherent category supported in S, defined
by the original local pullbacks at every point outside S. -/
def supportOn (S : Set X) : ObjectProperty (Coh X) :=
  fun N => ∀ x : {x : X // x ∉ S}, (stalkPullback X x.1).toFunctor.kernel N

instance supportOn_serre (S : Set X) : (supportOn X S).IsSerreClass := by
  let : ∀ x : {x : X // x ∉ S},
      (stalkPullback X x.1).toFunctor.kernel.IsSerreClass :=
    fun x => CategoryTheory.ObjectProperty.exactKernelSerre (stalkPullback X x.1)
  exact CategoryTheory.ObjectProperty.forallSerre _

/-- The full subcategory of the small coherent model with support contained in `S`. -/
abbrev CohSupportOn (S : Set X) := (supportOn X S).FullSubcategory
/-- This fixed full subcategory is exactly the geometric support category,
not an arbitrary exact category with a selected K-group isomorphism. -/
theorem supportOn_iff (S : Set X) (N : Coh X) :
    supportOn X S N ↔ support
      ((equivSmallModel.{u + 1} (FiniteTypeSheaves X)).inverse.obj N).obj ⊆ S := by
  constructor
  · intro h x hx
    by_contra hn
    exact hx ((smallStalk_kernel_iff X N x).mp (h ⟨x, hn⟩))
  · intro h x
    apply (smallStalk_kernel_iff X N x.1).mpr
    by_contra hn
    exact x.2 (h hn)

/-- An arbitrary family of distinct closed field immersions. These are
geometric data only; no K-theory statement is stored here. Each field is
the residue field of its image because its map is a closed immersion. -/
structure ClosedFieldFamily where
  /-- The index type of the distinct closed points in the family. -/
  Index : Type u
  /-- The field attached to each indexed closed point. -/
  field : Index → Type u
  fieldInstance : ∀ i, Field (field i)
  /-- The indexed closed points of `X`. -/
  point : Index → X
  point_injective : Function.Injective point
  point_closed : ∀ i, IsClosed ({point i} : Set X)
  /-- The closed immersion from each specified field spectrum into `X`. -/
  immersion : ∀ i, Spec (CommRingCat.of (field i)) ⟶ X
  closedImmersion : ∀ i, IsClosedImmersion (immersion i)
  immersion_apply : ∀ i y, immersion i y = point i

attribute [instance] ClosedFieldFamily.fieldInstance ClosedFieldFamily.closedImmersion

variable (D : ClosedFieldFamily X)

/-- The exact support subset is the range of the specified closed-point index. -/
def pointSet : Set X := Set.range D.point

/-- Coherence and Noetherianity make the support finite in this general
closed-point category. No fixed finite set or dimension bound is assumed. -/
theorem supportOn_finite (N : CohSupportOn X (pointSet X D)) :
    (support ((equivSmallModel.{u + 1} (FiniteTypeSheaves X)).inverse.obj N.obj).obj).Finite := by
  let N' := (equivSmallModel.{u + 1} (FiniteTypeSheaves X)).inverse.obj N.obj
  let Z := support N'.obj
  have hZ : IsClosed Z := finiteType_support_isClosed N'
  have hs := (supportOn_iff X _ N.obj).mp N.property
  obtain ⟨S, hS, hSc, hSi, hSZ⟩ :=
    NoetherianSpace.exists_finite_set_isClosed_irreducible hZ
  let g : S → X := fun s => (hSi s.1 s.2).genericPoint
  let : Finite S := hS.to_subtype
  apply (Set.finite_range g).subset
  intro x hx
  change x ∈ Z at hx
  obtain ⟨s, hsS, hxs⟩ := Set.mem_sUnion.mp (hSZ ▸ hx)
  let t : S := ⟨s, hsS⟩
  have hg : IsGenericPoint (g t) s :=
    (hSi s hsS).isGenericPoint_genericPoint (hSc s hsS)
  have hgZ : g t ∈ Z := by
    rw [hSZ]
    exact Set.mem_sUnion.mpr ⟨s, hsS, hg.mem⟩
  obtain ⟨i, hi⟩ := hs hgZ
  have hc : IsClosed ({g t} : Set X) := hi ▸ D.point_closed i
  have heq : x = g t := (hg.specializes hxs).mem_closed hc (Set.mem_singleton _)
  exact ⟨t, heq.symm⟩

theorem residue_lands (i : D.Index)
    (N : Coh (Spec (CommRingCat.of (D.field i)))) :
    supportOn X (pointSet X D)
      ((smallPushforward (D.immersion i)).toFunctor.obj N) := by
  intro x
  apply smallPushforward_stalkPullback_isZero
  apply coherentPushforward_stalkPullback_isZero
  intro y _ hs
  rw [D.immersion_apply] at hs
  have hx : x.1 = D.point i := hs.mem_closed (D.point_closed i) (Set.mem_singleton _)
  exact x.2 ⟨i, hx.symm⟩

/-- The original finite coherent pushforward with its proved closed support landing. -/
def residueToSupportExact (i : D.Index) : _root_.CategoryTheory.ExactCategory.ExactFunctor
    (_root_.CategoryTheory.ExactCategory.abelianExactStructure (Coh (Spec (CommRingCat.of
        (D.field i)))))
    (_root_.CategoryTheory.ExactCategory.abelianExactStructure (CohSupportOn X (pointSet X D)))
        where
  toFunctor := (supportOn X (pointSet X D)).lift
    (smallPushforward (D.immersion i)).toFunctor (residue_lands X D i)
  additive := {
    map_add := by
      intros
      apply ObjectProperty.hom_ext
      exact (smallPushforward (D.immersion i)).toFunctor.map_add }
  map_conflation S h := by
    have he := (smallPushforward (D.immersion i)).map_conflation S h
    exact { exact := Functor.reflects_exact_of_faithful (supportOn X (pointSet X D)).ι _ he.exact
            mono_f := (supportOn X (pointSet X D)).ι.mono_of_mono_map he.mono_f
            epi_g := (supportOn X (pointSet X D)).ι.epi_of_epi_map he.epi_g }

end AlgebraicGeometry.Scheme.Modules.Coherent.Support
