/-
Copyright (c) 2026 kangxyz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.RingTheory.FiniteLength.Support
public import Aglib.AlgebraicGeometry.Modules.Coherent.Support.StalkStrata
public import Aglib.AlgebraicGeometry.Modules.Pullback.FlatMorphism
public import Aglib.AlgebraicGeometry.Modules.Coherent.Affine.Comparison
public import Aglib.AlgebraicGeometry.Modules.Coherent.Pullback
public import Aglib.AlgebraicGeometry.Modules.QuasiCoherent.Affine.FiniteTypeComparison
public import Aglib.AlgebraicGeometry.Modules.Coherent.FinitePresentation
public import Aglib.AlgebraicGeometry.Modules.FinitePresentation.Locality
public import Aglib.AlgebraicGeometry.Modules.LocallyFree.Pullback
public import Aglib.AlgebraicGeometry.Modules.QuasiCoherent.FiniteType.FinitePresentation
public import Aglib.AlgebraicGeometry.Modules.Exact
public import Aglib.AlgebraicGeometry.Modules.Stalk.Basic
public import Aglib.AlgebraicGeometry.Modules.Support
public import Aglib.AlgebraicGeometry.Modules.FinitePresentation.Noetherian
public import Aglib.AlgebraicGeometry.Modules.QuasiCoherent.Affine.FiniteGenerators

/-!
# Local support and finite length of coherent pullback

Source-only extraction from `R5Lab.KTheory.Quillen.LocalPullbackSupport` at R5Lab revision
`e6d63abca2403f50b6b413101ad7f6a7f2e0e2c7`. Existing objects, maps,
hypotheses, universes, proof bodies and mathematical namespaces are retained.
The original source correspondence remains in the supplying application module.
-/


/-!
Native migration from `R5Lab.Aglib.AlgebraicGeometry.Modules.Support.LocalPullback` at R5 revision
`f8a3314ddecffcada2ec721d26d56a937bed9690`, SHA-256
`fcd3400da8db39da8fd0201a646ce63c7bed13a4ec1b81285f8c043cbae53aa3`.
Original objects, maps, universes and explicit hypotheses are retained.
Native providers replace duplicate implementations.
-/

@[expose] public section

open _root_.Module (finiteLength_of_support_maximal)

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open AlgebraicGeometry.Scheme.Modules.Coherent.Support
namespace AlgebraicGeometry.Scheme.Modules.Stalk

universe u
variable (X : Scheme.{u}) [IsNoetherian X] (p : ℕ)

omit [AlgebraicGeometry.IsNoetherian X] in
/-- A nonclosed prime of the actual local spectrum maps to a strictly lower-height
point of X. The embedding and the actual fromSpecStalk map are used explicitly. -/
theorem local_nonclosed_height_lt (x : HeightPoint X p)
    (q : Spec (X.presheaf.stalk x.1)) (hq : q ≠ IsLocalRing.closedPoint (X.presheaf.stalk x.1)) :
    ringKrullDim (X.presheaf.stalk (X.fromSpecStalk x.1 q)) < p := by
  let f := X.fromSpecStalk x.1
  have hs : f q ⤳ x.1 := (X.range_fromSpecStalk (x := x.1)).le ⟨q, rfl⟩
  have hn : f q ≠ x.1 := by
    intro he
    apply hq
    exact f.isEmbedding.injective (he.trans X.fromSpecStalk_closedPoint.symm)
  have hlt : x.1 < f q := lt_iff_le_not_ge.mpr
    ⟨hs, fun h => hn (Specializes.antisymm hs h).eq⟩
  have hx : Order.coheight x.1 = p := by
    have h := x.2
    rw [ringKrullDim_stalk_eq_coheight] at h
    exact WithBot.coe_injective h
  have hfin : Order.coheight (f q) < ⊤ :=
    lt_of_le_of_lt (Order.coheight_anti hs) (by rw [hx]; exact WithTop.coe_lt_top p)
  have hbad := Order.coheight_strictAnti hlt hfin
  rw [ringKrullDim_stalk_eq_coheight]
  exact WithBot.coe_lt_coe.mpr (hx ▸ hbad)

/-- The coherent pullback to the local spectrum at a height-`p` point
of an object supported in height at least `p`. -/
abbrev localCoherentPullback (M : CohAtLeast X p) (x : HeightPoint X p) :=
  (Scheme.Modules.Coherent.coherentPullback (X.fromSpecStalk x.1)).obj
      M.obj

/-- The support of the actual coherent pullback to the local spectrum is contained
in its actual closed point. This is a theorem about sheaf pullback and module stalks. -/
theorem local_pullback_support (M : CohAtLeast X p) (x : HeightPoint X p) :
    Scheme.Modules.support (localCoherentPullback X p M x).obj ⊆
      {IsLocalRing.closedPoint (X.presheaf.stalk x.1)} := by
  intro q hq
  by_contra hn
  have hz := M.property ⟨X.fromSpecStalk x.1 q, local_nonclosed_height_lt X p x q hn⟩
  let e := (Scheme.Modules.pullbackModuleStalkIso (X.fromSpecStalk
      x.1) q).app M.obj.obj
  have he : IsZero ((Scheme.Modules.moduleStalk (Spec
      (X.presheaf.stalk x.1)) q).obj
      (localCoherentPullback X p M x).obj) :=
    (Iso.isZero_iff e).mpr ((ModuleCat.extendScalars ((X.fromSpecStalk x.1).stalkMap
        q).hom).map_isZero hz)
  exact hq ((moduleStalk_isZero_iff _ _ q).mp he)

/-- The original global-section module of the local coherent pullback has finite
length. Its support comparison is the pinned actual affine support theorem. -/
theorem local_pullback_sections_finiteLength (M : CohAtLeast X p) (x : HeightPoint X p) :
    IsFiniteLength (X.presheaf.stalk x.1)
      (moduleSpecΓFunctor.obj (localCoherentPullback X p M x).obj) := by
  let R := X.presheaf.stalk x.1
  let N := localCoherentPullback X p M x
  have hN :=
      (Scheme.Modules.QuasiCoherent.affineLocallyFiniteType_spec_iff R
      N.obj).mp N.property
  let : N.obj.IsQuasicoherent := hN.1
  let : Module.Finite R (moduleSpecΓFunctor.obj N.obj) := hN.2
  apply finiteLength_of_support_maximal R (moduleSpecΓFunctor.obj N.obj)
  intro q hq
  have hq' : q ∈ Scheme.Modules.support N.obj := by
    rw [Scheme.Modules.support_eq_support_globalSections]
    exact hq
  have he := local_pullback_support X p M x hq'
  rw [Set.mem_singleton_iff] at he
  cases he
  change (IsLocalRing.maximalIdeal (X.presheaf.stalk x.1)).IsMaximal
  infer_instance

end AlgebraicGeometry.Scheme.Modules.Stalk
