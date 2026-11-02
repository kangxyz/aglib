/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.Surfaces.Resolution.RationalDoublePoint.HeightMultiset
public import Aglib.AlgebraicGeometry.Surfaces.Resolution.RationalDoublePoint.FiniteHeight
public import Aglib.AlgebraicGeometry.Surfaces.Resolution.PointBlowupChain.NormalStages
public import Aglib.AlgebraicGeometry.FunctionField.StalkInjection
public import Aglib.AlgebraicGeometry.Stalk.LocalBaseResidue

/-!
# Finite original point-blowup resolution from genuine singular heights

The native multiset induction constructs the actual chain, proves normality of
its actual stages, and preserves every open on which the original scheme was
regular. Initial empty levels are derived separately from the original cones
and an earlier complete base.
-/

@[expose] public noncomputable section
set_option autoImplicit false

open CategoryTheory TopologicalSpace IsLocalRing Localization.Away
open AlgebraicGeometry.Scheme.Blowup
open AlgebraicGeometry.Scheme.Blowup.ClosedPointPrefix
open AlgebraicGeometry.Scheme.RationalSingularities

universe u

namespace AlgebraicGeometry.Scheme.RationalDoublePoint

/-- Serialize genuine finite singular heights into a finite chain of the actual
point blowups. This intermediate theorem preserves every original regular open. -/
theorem exists_regular_pointBlowupChain_of_empty_singularPrefixes
    (R : Type u) [CommRing R] [IsDomain R] [IsLocalRing R] [IsNoetherianRing R]
    (hR : IsNagataRing.{u, 0} R) (hdR : ringKrullDim R = 2)
    (hRat : NormalModificationH1Vanishing R)
    {X : Scheme.{u}} [IsIntegral X]
    (f : X ⟶ Spec (.of R)) [IsProper f] [IsDominant f]
    (hX : NormalStalks X)
    (hff : IsIso (CommRingCat.ofHom (functionFieldMap f)))
    (hlevels : ∀ x : X, ¬ IsRegularLocalRing (X.presheaf.stalk x) →
      ∃ n, IsEmpty (SingularPrefix X x n)) :
    ∃ (Y : Scheme.{u}) (g : Y ⟶ X) (c : PointBlowupChain g),
      RegularStalks Y ∧ c.NormalStages ∧
      ∀ U : X.Opens, (∀ x : X, x ∈ U → IsRegularLocalRing (X.presheaf.stalk x)) →
        IsIso (g ∣_ U) := by
  classical
  have hmain : ∀ m : Multiset ℕ,
      ∀ (Z : Scheme.{u}) [IsIntegral Z]
        (p : Z ⟶ Spec (.of R)) [IsProper p] [IsDominant p]
        (hZ : NormalStalks Z)
        (hfield : IsIso (CommRingCat.ofHom (functionFieldMap p)))
        (hfinite : {z : Z | ¬ IsRegularLocalRing (Z.presheaf.stalk z)}.Finite)
        (hlev : ∀ z : Z, ¬ IsRegularLocalRing (Z.presheaf.stalk z) →
          ∃ n, IsEmpty (SingularPrefix Z z n)),
        heightMultiset
          (eligible := fun W w => ¬ IsRegularLocalRing (W.presheaf.stalk w))
          (X := Z) hfinite hlev = m →
        ∃ (T : Scheme.{u}) (g : T ⟶ Z) (c : PointBlowupChain g),
          RegularStalks T ∧ c.NormalStages ∧
          ∀ U : Z.Opens, (∀ z : Z, z ∈ U → IsRegularLocalRing (Z.presheaf.stalk z)) →
            IsIso (g ∣_ U) := by
    intro m
    induction m using (Multiset.wellFounded_isDershowitzMannaLT (α := ℕ)).induction with
    | h m ih =>
      intro Z _ p _ _ hZ hfield hfinite hlev hm
      by_cases hreg : RegularStalks Z
      · refine ⟨Z, 𝟙 Z, PointBlowupChain.refl Z, hreg, True.intro, ?_⟩
        intro U _
        exact inferInstanceAs (IsIso ((𝟙 Z) ∣_ U))
      · have hbad : ∃ x : Z, ¬ IsRegularLocalRing (Z.presheaf.stalk x) := by
          simpa only [RegularStalks, not_forall] using hreg
        obtain ⟨x, hx⟩ := hbad
        let : IsLocallyNoetherian Z := LocallyOfFiniteType.isLocallyNoetherian p
        obtain ⟨_, _, _, hN, hd, hclosed, _, _, _, hrat⟩ :=
          singular_stalk_properties_of_rational_model R hR hdR hRat p hZ hfield x hx
        let B := blowupDatum (Z.fromSpecResidueField x).ker
        have hB : NormalStalks B.Y :=
          normalStalks_pointBlowup_of_rational_stalk Z hZ x hclosed hN hd hrat
        have step : PointBlowupChain B.map := by
          have hs : PointBlowupChain (𝟙 B.Y ≫ B.map) :=
            PointBlowupChain.cons x hclosed hd (𝟙 B.Y) (PointBlowupChain.refl B.Y)
          exact Eq.mp (congrArg (fun g : B.Y ⟶ Z => PointBlowupChain g)
            (Category.id_comp B.map)) hs
        let : IsIntegral B.Y := step.isIntegral inferInstance
        let : IsProper B.map := step.isProper inferInstance
        let : IsDominant B.map := step.isDominant inferInstance
        let : IsIso (CommRingCat.ofHom (functionFieldMap B.map)) :=
          step.functionFieldMap_isIso inferInstance
        let : IsIso (CommRingCat.ofHom (functionFieldMap p)) := hfield
        have hcomp : IsIso (CommRingCat.ofHom (functionFieldMap (B.map ≫ p))) := by
          rw [functionFieldMap_comp, CommRingCat.ofHom_comp]
          infer_instance
        obtain ⟨hfinB, hnew, hlt⟩ :=
          exists_pointBlowup_heightMultiset_lt R hR hdR hRat p hZ hfield hfinite x hx hlev
        have hltm : Multiset.IsDershowitzMannaLT
            (heightMultiset
              (eligible := fun W w => ¬ IsRegularLocalRing (W.presheaf.stalk w))
              (X := B.Y) hfinB hnew) m := by
          rw [← hm]
          exact hlt
        obtain ⟨T, g, tail, hT, hnormal, hopen⟩ :=
          ih _ hltm B.Y (B.map ≫ p) hB hcomp hfinB hnew rfl
        refine ⟨T, g ≫ B.map, PointBlowupChain.cons x hclosed hd g tail,
          hT, ⟨hB, hnormal⟩, ?_⟩
        intro U hU
        let : IsClosedImmersion (Z.fromSpecResidueField x) :=
          isClosed_singleton_iff_isClosedImmersion.mp hclosed
        have hdisjoint :
            Disjoint (U : Set Z) ((Z.fromSpecResidueField x).ker.support : Set Z) := by
          rw [Scheme.Hom.support_ker, Scheme.range_fromSpecResidueField, hclosed.closure_eq]
          apply Set.disjoint_left.mpr
          intro z hz hz'
          have he : z = x := Set.mem_singleton_iff.mp hz'
          subst z
          exact hx (hU x hz)
        let : IsIso (B.map ∣_ U) := B.restrict_isIso_of_disjoint U hdisjoint
        have hV : ∀ y : B.Y, y ∈ B.map ⁻¹ᵁ U →
            IsRegularLocalRing (B.Y.presheaf.stalk y) := by
          intro y hy
          have hyx : B.map y ≠ x := by
            intro he
            have hxU : x ∈ U := he ▸ hy
            exact hx (hU x hxU)
          let : IsIso (B.map.stalkMap y) := pointBlowup_stalkMap_isIso_of_ne x hclosed y hyx
          let : IsRegularLocalRing (Z.presheaf.stalk (B.map y)) := hU (B.map y) hy
          exact IsRegularLocalRing.of_ringEquiv
            (asIso (B.map.stalkMap y)).commRingCatIsoToRingEquiv
        let : IsIso (g ∣_ B.map ⁻¹ᵁ U) := hopen (B.map ⁻¹ᵁ U) hV
        have hi : IsIso ((g ∣_ B.map ⁻¹ᵁ U) ≫ (B.map ∣_ U)) := inferInstance
        exact Eq.mpr (congrArg
          (fun k : ((g ≫ B.map) ⁻¹ᵁ U).toScheme ⟶ U.toScheme => IsIso k)
          (morphismRestrict_comp g B.map U)) hi
  let : CompactSpace X := QuasiCompact.compactSpace_of_compactSpace f
  let : IsNoetherian X := { __ := LocallyOfFiniteType.isLocallyNoetherian f }
  have hdim := Cohomology.actualModel_dimension_of_nagata f hR hdR.le hff
  have hJ : IsJ2Ring.{u, 0} R := IsNagataRing.isJ2Ring_of_semilocal_dimLE_two R hR hdR.le
  have hfinite := finite_singularSet_of_finiteType_of_isJ2Ring R f hJ hX hdim
  exact hmain _ X f hX hff hfinite hlevels rfl

/-- Actual initial full cones over an earlier complete base admit a finite
original point-blowup resolution preserving every original regular open.
No empty-level, marking, future-cone or later-completeness hypothesis is input. -/
theorem exists_regular_pointBlowupChain_of_initial_cones_of_complete_base
    (R : Type u) [CommRing R] [IsDomain R] [IsLocalRing R] [IsNoetherianRing R]
    (hR : IsNagataRing.{u, 0} R) (hdR : ringKrullDim R = 2)
    (hRat : NormalModificationH1Vanishing R)
    {X : Scheme.{u}} [IsIntegral X]
    (f : X ⟶ Spec (.of R)) [IsProper f] [IsDominant f]
    (hX : NormalStalks X)
    (hff : IsIso (CommRingCat.ofHom (functionFieldMap f)))
    (hcones : ∀ x : X, ¬ IsRegularLocalRing (X.presheaf.stalk x) →
      ∃ (t : maximalIdeal (X.presheaf.stalk x))
        (g : Fin 2 → maximalIdeal (X.presheaf.stalk x))
        (q : MvPolynomial (Fin 3) (ResidueField (X.presheaf.stalk x))),
        Ideal.span (Set.range fun i =>
          (CaseOne.orderedGenerators t g i : X.presheaf.stalk x)) =
            maximalIdeal (X.presheaf.stalk x) ∧
        q ≠ 0 ∧ q.IsHomogeneous 2 ∧
        RingHom.ker (CaseOne.canonicalConeMap t g) = Ideal.span {q})
    (A : Type u) [CommRing A] [IsDomain A] [IsLocalRing A]
    [IsAdicComplete (maximalIdeal A) A] (hdA : ringKrullDim A = 2)
    (a : A →+* R) [IsLocalHom a]
    (hinj : Function.Injective a) (hres : (ResidueField.map a).Finite) :
    ∃ (Y : Scheme.{u}) (g : Y ⟶ X) (c : PointBlowupChain g),
      RegularStalks Y ∧ c.NormalStages ∧
      ∀ U : X.Opens, (∀ x : X, x ∈ U → IsRegularLocalRing (X.presheaf.stalk x)) →
        IsIso (g ∣_ U) := by
  apply exists_regular_pointBlowupChain_of_empty_singularPrefixes R hR hdR hRat f hX hff
  intro x hx
  obtain ⟨t, g, q, hgen, hq0, hq, hker⟩ := hcones x hx
  obtain ⟨_, _, _, _, _, _, _, hbase, hresf, _⟩ :=
    singular_stalk_properties_of_rational_model R hR hdR hRat f hX hff x hx
  let : IsLocalHom (f.stalkScalar x) := f.stalkScalar_isLocalHom_of_closedPoint x hbase
  have hinjScalar : Function.Injective (f.stalkScalar x) := by
    have h := (f.stalkMap_injective_of_isDominant x).comp (f.closedBaseStalkEquiv x hbase).injective
    change Function.Injective
      ((f.stalkMap x).hom.comp (f.closedBaseStalkEquiv x hbase).toRingHom) at h
    rw [f.closedBaseStalkEquiv_stalkMap x hbase] at h
    exact h
  have hresScalar : (ResidueField.map (f.stalkScalar x)).Finite :=
    (f.stalkScalar_residueMap_finite_iff x hbase).mpr hresf
  let ax : A →+* X.presheaf.stalk x := (f.stalkScalar x).comp a
  let : IsLocalHom ax := inferInstanceAs (IsLocalHom ((f.stalkScalar x).comp a))
  have hinjAx : Function.Injective ax := hinjScalar.comp hinj
  have hresAx : (ResidueField.map ax).Finite := by
    change (ResidueField.map ((f.stalkScalar x).comp a)).Finite
    rw [ResidueField.map_comp]
    exact hresScalar.comp hres
  exact exists_empty_singularPrefix_level_of_initial_cone_of_complete_base
    R hR hdR hRat f hX hff x hx t g hgen q hq0 hq hker A hdA ax hinjAx hresAx

end AlgebraicGeometry.Scheme.RationalDoublePoint
