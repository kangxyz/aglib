/-
Copyright (c) 2026 kangxyz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.CategoryTheory.Limits.Monomorphisms
public import Aglib.AlgebraicGeometry.Limits.RelativeProducts
public import Aglib.AlgebraicGeometry.Descent.FinitePresentation.ClosedImmersion

/-!
# Eventual separatedness with monomorphic affine transitions

For a qcqs inverse system over a fixed quasi-separated base, with affine
monomorphic transition maps, separatedness of the original limit structure
map holds at a stage. The proof constructs the actual relative-product limit
and uses the cartesian squares of diagonals induced by monomorphisms. No
finite-presentation assumption, absolute approximation, or schematic-image
base-change assertion is needed.
-/

@[expose] public noncomputable section

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open CategoryTheory CategoryTheory.Limits

universe u

namespace AlgebraicGeometry.Scheme

/-- Eventual separatedness for a native over-category diagram whose transitions
are affine monomorphisms. In particular, this applies to closed transitions. -/
theorem exists_isSeparated_over_of_isLimit_of_mono
    {I : Type u} [Category.{u} I] [IsCofiltered I]
    {S : Scheme.{u}} [QuasiSeparatedSpace S]
    (D : I ⥤ Over S)
    [∀ {i j} (q : i ⟶ j), IsAffineHom (D.map q).left]
    [∀ {i j} (q : i ⟶ j), Mono (D.map q).left]
    [∀ i, CompactSpace (D.obj i).left] [∀ i, QuasiSeparatedSpace (D.obj i).left]
    (c : Cone D) (hc : IsLimit ((Over.forget S).mapCone c))
    [IsSeparated c.pt.hom] :
    ∃ i, IsSeparated (D.obj i).hom := by
  have : Nonempty I := IsCofiltered.nonempty
  let i : I := Classical.arbitrary I
  let E := RelativeProducts.diagram D
  let e := RelativeProducts.cone D c
  have he : IsLimit e := RelativeProducts.isLimitCone D c hc
  have {j k : I} (q : j ⟶ k) : IsAffineHom (E.map q) :=
    inferInstanceAs (IsAffineHom ((RelativeProducts.diagram D).map q))
  have (j : I) : CompactSpace (E.obj j) :=
    inferInstanceAs (CompactSpace ((RelativeProducts.diagram D).obj j))
  have (j : I) : QuasiSeparatedSpace (E.obj j) :=
    inferInstanceAs (QuasiSeparatedSpace ((RelativeProducts.diagram D).obj j))
  have {j k : I} (q : j ⟶ k) : Mono ((D ⋙ Over.forget S).map q) :=
    inferInstanceAs (Mono (D.map q).left)
  have hmono (i : I) : Mono (c.π.app i).left :=
    IsLimit.mono_π_app (D ⋙ Over.forget S) ((Over.forget S).mapCone c) hc i
  have hlim : IsPullback (c.π.app i).left (pullback.diagonal c.pt.hom)
      (pullback.diagonal (D.obj i).hom) (e.π.app i) :=
    isPullback_diagonal_of_mono c.pt.hom (D.obj i).hom (c.π.app i).left (c.π.app i).w
  have : IsClosedImmersion (pullback.fst (e.π.app i) (pullback.diagonal (D.obj i).hom)) := by
    rw [← hlim.flip.isoPullback_inv_fst]
    infer_instance
  obtain ⟨j, hj⟩ := exists_isClosedImmersion_pullback_fst_of_isLimit E e he i
    (pullback.diagonal (D.obj i).hom)
  have hstage : IsPullback (D.map j.hom).left (pullback.diagonal (D.obj j.left).hom)
      (pullback.diagonal (D.obj i).hom) (E.map j.hom) :=
    isPullback_diagonal_of_mono (D.obj j.left).hom (D.obj i).hom
      (D.map j.hom).left (D.map j.hom).w
  refine ⟨j.left, ?_⟩
  rw [AlgebraicGeometry.isSeparated_iff, ← hstage.flip.isoPullback_hom_fst]
  infer_instance

/-- The explicit-cone form of eventual separatedness for closed-transition
systems, retaining the original limit structural morphism. -/
theorem exists_isSeparated_of_isLimit
    {I : Type u} [Category.{u} I] [IsCofiltered I]
    (D : I ⥤ Scheme.{u})
    [∀ {i j} (q : i ⟶ j), IsClosedImmersion (D.map q)]
    [∀ i, CompactSpace (D.obj i)] [∀ i, QuasiSeparatedSpace (D.obj i)]
    (c : Cone D) (hc : IsLimit c)
    {S : Scheme.{u}} [QuasiSeparatedSpace S]
    (t : D ⟶ (Functor.const I).obj S)
    (p : c.pt ⟶ S) (hp : ∀ i, c.π.app i ≫ t.app i = p)
    [IsSeparated p] :
    ∃ i, IsSeparated (t.app i) := by
  let E := Over.lift D t
  let e := Over.liftCone D t c p hp
  have hlim : IsLimit ((Over.forget S).mapCone e) := hc
  have {i j : I} (q : i ⟶ j) : IsAffineHom (E.map q).left :=
    inferInstanceAs (IsAffineHom (D.map q))
  have {i j : I} (q : i ⟶ j) : Mono (E.map q).left :=
    inferInstanceAs (Mono (D.map q))
  have (i : I) : CompactSpace (E.obj i).left :=
    inferInstanceAs (CompactSpace (D.obj i))
  have (i : I) : QuasiSeparatedSpace (E.obj i).left :=
    inferInstanceAs (QuasiSeparatedSpace (D.obj i))
  have : IsSeparated e.pt.hom := inferInstanceAs (IsSeparated p)
  exact exists_isSeparated_over_of_isLimit_of_mono E e hlim

end AlgebraicGeometry.Scheme
