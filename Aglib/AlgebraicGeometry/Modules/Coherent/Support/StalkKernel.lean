/-
Copyright (c) 2026 kangxyz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.Modules.Coherent.Support.FinitePushforward
public import Aglib.AlgebraicGeometry.Modules.Coherent.Support.StalkFiltration

/-!
Native migration from `R5Lab.Aglib.AlgebraicGeometry.Modules.Support.StalkKernel` at R5 revision
`f8a3314ddecffcada2ec721d26d56a937bed9690`, SHA-256
`75e9df1bbd873703c92bd3b14e84a1b6a61ce1979db7701ee3f3339b97236d0b`.
Original objects, maps, universes and explicit hypotheses are retained.
Native providers replace duplicate implementations.
-/

@[expose] public section

noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry TopologicalSpace
open AlgebraicGeometry.Scheme
open _root_.AlgebraicGeometry.Scheme.Modules (stalkFunctor)
open _root_.AlgebraicGeometry.Scheme.Modules.Coherent (coherentPullback)
open _root_.AlgebraicGeometry.Scheme.Modules.QuasiCoherent (FiniteTypeSheaves
    finiteTypeSheavesToModules finiteType_support_isClosed)
open AlgebraicGeometry.Scheme.Modules.Coherent.Support
    AlgebraicGeometry.Scheme.Modules.Coherent.Support
attribute [local instance] Abelian.hasFiniteBiproducts
attribute [local instance] Scheme.fromSpecStalk_flat
namespace AlgebraicGeometry.Scheme.Modules.Coherent.Support
universe u
variable (X : Scheme.{u}) [IsNoetherian X]

/-- The actual coherent local pullback is zero exactly when the original
stalk is zero. Both directions preserve the given point and actual maps. -/
theorem coherentPullback_zero_iff_stalk (N : FiniteTypeSheaves X) (x : X) :
    IsZero ((coherentPullback (X.fromSpecStalk x)).obj N) ↔
      IsZero ((stalkFunctor X x).obj N.obj) := by
  constructor
  · intro hz
    have hz' := (finiteTypeSheavesToModules _).map_isZero hz
    have hs := stalk_isZero_of_flat_pullback (X.fromSpecStalk x) N.obj hz'
      (IsLocalRing.closedPoint (X.presheaf.stalk x))
    simpa only [Scheme.fromSpecStalk_closedPoint] using hs
  · intro hz
    apply IsZero.of_full_of_faithful_of_isZero (finiteTypeSheavesToModules _) _
    apply pullback_isZero_of_support
    intro y hy
    have hs : X.fromSpecStalk x y ⤳ x :=
      (X.range_fromSpecStalk (x := x)).le ⟨y,rfl⟩
    exact hs.mem_closed (finiteType_support_isClosed N) hy hz

/-- Small-model transport changes neither this zero criterion nor its stalk. -/
theorem smallStalk_kernel_iff (N : Coh X) (x : X) :
    (stalkPullback X x).toFunctor.kernel N ↔
      IsZero ((stalkFunctor X x).obj
        ((equivSmallModel.{u + 1} (FiniteTypeSheaves X)).inverse.obj N).obj) := by
  change (_root_.CategoryTheory.SmallModel.functor.{u + 1}
    (coherentPullback (X.fromSpecStalk x))).kernel N ↔ _
  rw [_root_.CategoryTheory.SmallModel.kernel_iff]
  exact coherentPullback_zero_iff_stalk X _ x

variable [IsIntegral X]

omit [IsNoetherian X] in
/-- On an integral scheme the only point below height one is its actual generic point. -/
theorem eq_genericPoint_of_height_lt_one [IsNoetherian X] (x : X)
    (hx : ringKrullDim (X.presheaf.stalk x) < 1) : x = genericPoint X := by
  have hzero : Order.coheight x = 0 := by
    rw [ringKrullDim_stalk_eq_coheight] at hx
    have hx' : Order.coheight x < 1 := WithBot.coe_lt_coe.mp hx
    exact Order.lt_one_iff.mp hx'
  have hmax := Order.coheight_eq_zero.mp hzero
  have hback : x ⤳ genericPoint X := hmax (genericPoint_specializes x)
  exact (Specializes.antisymm hback (genericPoint_specializes x)).eq

end AlgebraicGeometry.Scheme.Modules.Coherent.Support
