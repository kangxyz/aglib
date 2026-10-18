/-
Copyright (c) 2026 kangxyz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/

module

public import Aglib.AlgebraicGeometry.Morphisms.FiniteEtale.Descent.GlobalGluedCover
public import Aglib.AlgebraicGeometry.Morphisms.FiniteEtale.Descent.GlobalCoverFullness
public import Aglib.AlgebraicGeometry.Morphisms.FiniteEtale.Descent.GlobalFinitePureLocal
public import Aglib.AlgebraicGeometry.FundamentalGroup.Basic

/-!
# Finite purely inseparable invariance over arbitrary schemes

The functor is the actual pullback functor on actual finite étale covers.
Affine models are constructed from nilpotent-lifting descent data. The
equifibered diagram and its gluing/reconstruction are proved, and full
faithfulness is glued from the actual affine Hom-set bijections.
-/

@[expose] public section

noncomputable section
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open _root_.AlgebraicGeometry.Scheme.FiniteEtale (Fiber baseChange fiberBaseChangeEquiv
  fiberToFinite fiberToFiniteBaseChangeIso)

namespace AlgebraicGeometry.Scheme.FiniteEtale.PurelyInseparable.Global

universe u
variable (K L : Type u) [Field K] [Field L] [Algebra K L]
  [IsPurelyInseparable K L] [Module.Finite K L]
  {X : Scheme.{u}} (p : X ⟶ Spec (CommRingCat.of K))

/-- Finite purely inseparable field extension induces an equivalence on the
actual finite étale cover categories of EVERY scheme over the base field. -/
def finitePureCoverEquivalence :
    Scheme.FiniteEtale X ≌ Scheme.FiniteEtale (pullback p (Spec.algebraMap K L)) := by
  let f := pullback.fst p (Spec.algebraMap K L)
  let 𝒰 := X.directedAffineCover
  let : Surjective f := inferInstanceAs (Surjective (pullback.fst p (Spec.algebraMap K L)))
  let : Flat f := inferInstanceAs (Flat (pullback.fst p (Spec.algebraMap K L)))
  let : QuasiCompact f := inferInstanceAs (QuasiCompact (pullback.fst p (Spec.algebraMap K L)))
  let (i : 𝒰.I₀) : IsAffine (𝒰.X i) := i.2
  let (i : 𝒰.I₀) : (baseChange (pullback.fst (𝒰.f i) f)).IsEquivalence :=
    affineFieldRestriction_isEquivalence K L p (𝒰.f i)
  let : (baseChange f).Full := baseChange_full_of_local_full f 𝒰
  let : (baseChange f).Faithful := baseChange_faithful_of_flat_surjective f
  let : (baseChange f).EssSurj := baseChange_essSurj_of_local_equivalence f 𝒰
  let : (baseChange f).IsEquivalence := { }
  exact (baseChange f).asEquivalence

@[simp] theorem finitePureCoverEquivalence_functor :
    (finitePureCoverEquivalence K L p).functor =
      baseChange (pullback.fst p (Spec.algebraMap K L)) := rfl

theorem finitePureBaseChange_isEquivalence :
    (baseChange (pullback.fst p (Spec.algebraMap K L))).IsEquivalence :=
  (finitePureCoverEquivalence K L p).isEquivalence_functor

/-- Compatibility with the existing actual point fibre functor; the point
field can in particular be separably or algebraically closed. -/
def finitePureCoverFiberIso {Ω : Type u} [Field Ω]
    (s : Spec (CommRingCat.of Ω) ⟶ pullback p (Spec.algebraMap K L)) :
    fiberToFinite (s ≫ pullback.fst p (Spec.algebraMap K L)) ≅
      (finitePureCoverEquivalence K L p).functor ⋙ fiberToFinite s :=
  fiberToFiniteBaseChangeIso (pullback.fst p (Spec.algebraMap K L)) s

-- Keep this original typed fibre/point simp formula before carrier or functor normalization.
@[simp, nolint simpNF] theorem finitePureCoverFiberIso_apply {Ω : Type u} [Field Ω]
    (s : Spec (CommRingCat.of Ω) ⟶ pullback p (Spec.algebraMap K L))
    (Y : Scheme.FiniteEtale X) (q : Fiber (s ≫ pullback.fst p (Spec.algebraMap K L)) Y) :
    (finitePureCoverFiberIso K L p s).hom.app Y q =
      fiberBaseChangeEquiv (pullback.fst p (Spec.algebraMap K L)) s Y q :=
  Scheme.EtaleFundamentalGroups.finiteBaseChangeIso_hom_apply _ _ _ _

end AlgebraicGeometry.Scheme.FiniteEtale.PurelyInseparable.Global

/- Migration source: the R5Lab/Aglib mirror; exact module in the migration record.
R5 revision c82abf3a72ce1e1cedf4a4f1fe08bea994ad4df5.
SHA256 9404a4048164df659a623ac48dcc8700803bdf143bec38aa21bd4ebe3fa05ce3.
Definitions, hypotheses and universes are retained modulo native names. -/
