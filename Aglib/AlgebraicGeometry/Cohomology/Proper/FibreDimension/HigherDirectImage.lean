/-
Copyright (c) 2026 kangxyz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.Cohomology.Proper.FibreDimension.Local
public import Aglib.AlgebraicGeometry.Cohomology.Proper.FibreFormalFunctions.Stalk
public import Aglib.AlgebraicGeometry.Cohomology.DirectImage.Restriction
public import Aglib.AlgebraicGeometry.Cohomology.Affine.PushforwardAcyclicity
public import Aglib.AlgebraicGeometry.Modules.QuasiCoherent.FiniteType.Pullback
public import Aglib.AlgebraicGeometry.Modules.Support
public import Aglib.AlgebraicGeometry.Morphisms.Proper.BirationalDVR

/-!
# Original higher images of proper birational surfaces

The original local-spectrum pullback and its closed fibre control the actual
higher-image stalk. No completeness of the target stalk is assumed.
-/

@[expose] public noncomputable section

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry TopologicalSpace
open AlgebraicGeometry.Scheme.Modules AlgebraicGeometry.Scheme.Modules.QuasiCoherent

universe u

namespace AlgebraicGeometry.Scheme.Cohomology

/-- The original fibre away from the generic target lies in a proper closed
subset of the original integral surface source. -/
theorem fiber_dimension_le_one_of_integral_surface
    {X Y : Scheme.{u}} [IsIntegral X] [IsIntegral Y]
    (f : Y ⟶ X) [IsDominant f] (hdY : topologicalKrullDim Y ≤ 2)
    (x : X) (hx : x ≠ genericPoint X) : topologicalKrullDim (f.fiber x) ≤ 1 := by
  let Z : Set Y := f ⁻¹' closure ({x} : Set X)
  have hclosed : IsClosed Z := isClosed_closure.preimage f.continuous
  have havoid : Disjoint Z (genericPoints Y) := by
    rw [genericPoints_eq_singleton, Set.disjoint_singleton_right]
    intro hy
    have hm : f (genericPoint Y) ∈ closure ({x} : Set X) := hy
    rw [map_genericPoint_of_isDominant Y f] at hm
    have hsp : x ⤳ genericPoint X := specializes_iff_mem_closure.mpr hm
    exact hx (hsp.antisymm (genericPoint_specializes x)).eq
  have hdim : topologicalKrullDim Z ≤ 1 :=
    topologicalKrullDim_closed_le_of_avoids_genericPoints Z hclosed havoid 1 hdY
  have hsub : f ⁻¹' ({x} : Set X) ⊆ Z := Set.preimage_mono subset_closure
  calc
    topologicalKrullDim (f.fiber x) = topologicalKrullDim (f ⁻¹' ({x} : Set X)) :=
      IsHomeomorph.topologicalKrullDim_eq _ (f.fiberHomeo x).isHomeomorph
    _ ≤ topologicalKrullDim Z :=
      (Topology.IsEmbedding.inclusion hsub).isInducing.topologicalKrullDim_le
    _ ≤ 1 := hdim

/-- Vanishing of the actual higher-image stalk above the dimension of its
original fibre, using the actual noncomplete local-spectrum base change. -/
theorem moduleHigherDirectImage_stalk_isZero_of_fiber_dimension
    {X Y : Scheme.{u}} [IsLocallyNoetherian X] (f : Y ⟶ X) [IsProper f]
    (M : Y.Modules) [M.IsQuasicoherent] (hM : affineLocallyFiniteType Y M)
    (x : X) (d q : ℕ) (hdim : topologicalKrullDim (f.fiber x) ≤ d) (hq : d < q) :
    IsZero ((moduleStalk X x).obj (((pushforward f).rightDerived q).obj M)) := by
  let : IsNoetherianRing (X.presheaf.stalk x) := inferInstance
  let a := Limits.pullback.fst f (X.fromSpecStalk x)
  let p := Limits.pullback.snd f (X.fromSpecStalk x)
  let N := (Scheme.Modules.pullback a).obj M
  let : IsLocallyNoetherian Y := LocallyOfFiniteType.isLocallyNoetherian f
  have hN : affineLocallyFiniteType _ N := affineLocallyFiniteType_pullback a hM
  have hd : topologicalKrullDim
      (idealThickeningSpace p (IsLocalRing.maximalIdeal (X.presheaf.stalk x))) ≤ d :=
    (IsHomeomorph.topologicalKrullDim_eq _
      (ProperFibreFormalFunctions.localFibreIso f x).hom.homeomorph.isHomeomorph).le.trans hdim
  have hz : Subsingleton (Sheaf.H.{u + 1} (moduleAddSheaf _ N) q) :=
    subsingleton_moduleCohomology_of_local_of_dim_firstThickening
      (A := X.presheaf.stalk x) p N hN d q hd hq
  let e := moduleHigherDirectImageStalkLinearEquiv f M x q
  let : Subsingleton ((moduleStalk X x).obj (((pushforward f).rightDerived q).obj M)) :=
    ⟨fun s t => e.injective (@Subsingleton.elim _ hz _ _)⟩
  exact ModuleCat.isZero_of_subsingleton _

theorem higherImage_stalk_isZero_on_isomorphism_open
    {X Y : Scheme.{u}} (f : Y ⟶ X) (M : Y.Modules) [M.IsQuasicoherent]
    (U : X.Opens) [IsIso (f ∣_ U)] (x : X) (hx : x ∈ U) (n : ℕ) :
    IsZero ((stalkFunctor X x).obj (((pushforward f).rightDerived (n + 1)).obj M)) := by
  let N := (Scheme.Modules.restrictFunctor (f ⁻¹ᵁ U).ι).obj M
  let : N.IsQuasicoherent := isQuasicoherent_restrictFunctor (f ⁻¹ᵁ U).ι M
  have hz : IsZero (((pushforward (f ∣_ U)).rightDerived (n + 1)).obj N) :=
    isZero_rightDerived_pushforward_succ (f ∣_ U) N n
  have hres : IsZero ((Scheme.Modules.restrictFunctor U.ι).obj
      (((pushforward f).rightDerived (n + 1)).obj M)) :=
    hz.of_iso ((higherDirectImageRestrictionIso f U (n + 1)).app M)
  have haway : supportedAway U.ι (((pushforward f).rightDerived (n + 1)).obj M) :=
    (supportedAway_iff U.ι _).mpr hres
  exact (supportedAway_iff_stalks U.ι _).mp haway ⟨x, hx⟩

/-- Proper birational integral surface maps have no actual coherent higher
images above degree one. The source dimension is retained explicitly. -/
theorem isZero_higherDirectImage_of_proper_birational_surface
    {X Y : Scheme.{u}} [IsIntegral X] [IsIntegral Y] [IsLocallyNoetherian X]
    (f : Y ⟶ X) [IsProper f] [IsDominant f]
    (hff : IsIso (CommRingCat.ofHom (functionFieldMap f)))
    (hdY : topologicalKrullDim Y ≤ 2)
    (M : Y.Modules) [M.IsQuasicoherent] (hM : affineLocallyFiniteType Y M)
    (q : ℕ) (hq : 1 < q) : IsZero (((pushforward f).rightDerived q).obj M) := by
  classical
  apply (isZero_iff_stalks _).mpr
  intro x
  by_cases hx : x = genericPoint X
  · subst x
    obtain ⟨U, hxU, hU⟩ :=
      exists_isIso_restrict_of_isProper_birational_at_valuationRing f hff (genericPoint X)
    let : IsIso (f ∣_ U) := hU
    obtain ⟨n, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : q ≠ 0)
    exact higherImage_stalk_isZero_on_isomorphism_open f M U _ hxU n
  · have hz := moduleHigherDirectImage_stalk_isZero_of_fiber_dimension f M hM x 1 q
      (fiber_dimension_le_one_of_integral_surface f hdY x hx) hq
    exact ((forget₂ (ModuleCat (X.presheaf.stalk x)) AddCommGrpCat.{u}).map_isZero hz).of_iso
      ((moduleStalkForgetIso X x).app (((pushforward f).rightDerived q).obj M)).symm

end AlgebraicGeometry.Scheme.Cohomology
