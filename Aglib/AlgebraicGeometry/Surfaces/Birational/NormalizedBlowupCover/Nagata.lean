/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.Surfaces.Birational.NormalizedBlowupCover.Finite
public import Aglib.AlgebraicGeometry.Normalization.FiniteFunctionField
public import Aglib.AlgebraicGeometry.Blowup.AffineLiftingCover

/-!
# The original normalized blowup cover in an arbitrary finite extension

These results concern the existing Cover and FiniteBase objects. The specified
action on the same original function field identifies their generic map with
the common finite-function-field normalization construction. Nagata finiteness
on actual base charts replaces the separable finite-etale argument.

The base-chart Nagata property follows from the original affine structural map,
birationality of the actual normalized blowdown, and the public GF2 theorem.
The original normalization map, map into the literal pullback, both projections,
generic triangle, dominance, and original function-field maps are unchanged.
-/

@[expose] public noncomputable section

open CategoryTheory AlgebraicGeometry Opposite TopologicalSpace
open AlgebraicGeometry.Scheme.Blowup
open scoped nonZeroDivisors

universe u

namespace AlgebraicGeometry.Scheme.Birational.NormalizedBlowupCover

namespace Cover.Nagata

variable {S T X : Scheme.{u}} [IsIntegral S] [IsIntegral T] [IsIntegral X]
  (a : X ⟶ S) [IsDominant a]
  (ha : IsIso (CommRingCat.ofHom (Scheme.functionFieldMap a)))
  (s : T ⟶ S) [IsDominant s]

/-- The original scalar action: inverse blowdown field map, then the original
field map of s, on the unchanged original function field of T. -/
@[instance_reducible] def fieldAlgebra : Algebra X.functionField T.functionField :=
  ((Scheme.functionFieldMap s).comp (Cover.baseFieldIso a ha).inv.hom).toAlgebra

/-- The actual finite field map stays finite after the original field isomorphism. -/
theorem fieldAlgebra_finite (hfin : (Scheme.functionFieldMap s).Finite) :
    letI := fieldAlgebra a ha s
    Module.Finite X.functionField T.functionField := by
  let := fieldAlgebra a ha s
  change ((Scheme.functionFieldMap s).comp (Cover.baseFieldIso a ha).inv.hom).Finite
  exact hfin.comp (RingHom.Finite.of_surjective _
    (ConcreteCategory.bijective_of_isIso (Cover.baseFieldIso a ha).inv).2)

/-- Equality with the common adapter is on the original generic map, with its
specified scalar action and its unchanged original field spectrum. -/
theorem genericMap_eq :
    letI := fieldAlgebra a ha s
    Cover.genericMap a ha s = Scheme.FiniteFunctionField.genericMap X T.functionField := by
  let := fieldAlgebra a ha s
  unfold Cover.genericMap Scheme.FiniteFunctionField.genericMap
    Scheme.FiniteFunctionField.genericCover
  rw [Cover.genericCover_eq_specMap]
  rfl

private theorem fromNormalization_finite_congr {D Z : Scheme.{u}}
    (f g : D ⟶ Z) [QuasiCompact f] [QuasiSeparated f]
    [QuasiCompact g] [QuasiSeparated g] (h : f = g) :
    IsFinite f.fromNormalization ↔ IsFinite g.fromNormalization := by
  cases h
  rfl

private theorem normalization_normalStalks_congr {D Z : Scheme.{u}}
    (f g : D ⟶ Z) [QuasiCompact f] [QuasiSeparated f]
    [QuasiCompact g] [QuasiSeparated g] (h : f = g) :
    NormalStalks f.normalization ↔ NormalStalks g.normalization := by
  cases h
  rfl

/-- The same original relative-normalization map is finite under actual
affine-chart Nagata hypotheses and an arbitrary finite field extension. -/
theorem pi_isFinite (hfin : (Scheme.functionFieldMap s).Finite)
    (hNagata : ∀ U : X.affineOpens, Nonempty U.1 → IsNagataRing.{u, 0} Γ(X, U.1)) :
    IsFinite (Cover.pi a ha s) := by
  let := fieldAlgebra a ha s
  let : Module.Finite X.functionField T.functionField := fieldAlgebra_finite a ha s hfin
  change IsFinite (Cover.genericMap a ha s).fromNormalization
  exact (fromNormalization_finite_congr _ _ (genericMap_eq a ha s)).mpr
    (Scheme.FiniteFunctionField.fromNormalization_isFinite X T.functionField hNagata)

/-- All stalks of the same original relative normalization are normal domains.
No separability or normality hypothesis on X is used. -/
theorem normalization_normalStalks (hfin : (Scheme.functionFieldMap s).Finite) :
    NormalStalks (Cover.normalization a ha s) := by
  let := fieldAlgebra a ha s
  let : Module.Finite X.functionField T.functionField := fieldAlgebra_finite a ha s hfin
  change NormalStalks (Cover.genericMap a ha s).normalization
  exact (normalization_normalStalks_congr _ _ (genericMap_eq a ha s)).mpr
    (Scheme.FiniteFunctionField.normalization_normalStalks X T.functionField)

end Cover.Nagata

section OriginalCharts

variable {A : CommRingCat.{u}} {W : Scheme.{u}} (f : W ⟶ Spec A)

local instance [IsDomain A] : Nonempty (⊤ : (Spec A).Opens) :=
  ⟨⟨genericPoint (Spec A), trivial⟩⟩

private theorem originalChart_finiteType [LocallyOfFiniteType f]
    (U : W.Opens) (hU : IsAffineOpen U) : (affineBaseMap f U).FiniteType :=
  (f.finiteType_appLE (isAffineOpen_top _) hU le_top).comp
    (RingHom.FiniteType.of_surjective (Scheme.ΓSpecIso A).inv.hom
      (ConcreteCategory.bijective_of_isIso (Scheme.ΓSpecIso A).inv).2)

private theorem originalChart_injective [IsDomain A] [IsIntegral W]
    [IsDominant f] [QuasiCompact f] (U : W.Opens) [Nonempty U] :
    Function.Injective (affineBaseMap f U) := by
  let : IsSchemeTheoreticallyDominant f := IsSchemeTheoreticallyDominant.of_isDominant f
  exact (AlgebraicGeometry.map_injective_of_isIntegral W (homOfLE (le_top : U ≤ ⊤))).comp
    ((f.app_injective ⊤).comp
      (ConcreteCategory.bijective_of_isIso (Scheme.ΓSpecIso A).inv).1)

private theorem originalChart_germ [IsDomain A] [IsIntegral W] [IsDominant f]
    (U : W.Opens) [Nonempty U] :
    CommRingCat.ofHom (affineBaseMap f U) ≫ W.germToFunctionField U =
      (Scheme.ΓSpecIso A).inv ≫ (Spec A).germToFunctionField ⊤ ≫
        CommRingCat.ofHom (Scheme.functionFieldMap f) := by
  let : Nonempty (⊤ : W.Opens) := ⟨⟨genericPoint W, trivial⟩⟩
  have hg : genericPoint W ∈ U :=
    ((genericPoint_spec W).mem_open_set_iff U.isOpen).mpr (by simpa using ‹Nonempty U›)
  have hres : W.presheaf.map (homOfLE (le_top : U ≤ ⊤)).op ≫
      W.germToFunctionField U = W.germToFunctionField ⊤ :=
    W.presheaf.germ_res (homOfLE (le_top : U ≤ ⊤)) (genericPoint W) hg
  rw [Scheme.functionFieldMap_germ]
  change (Scheme.ΓSpecIso A).inv ≫ f.appTop ≫
      W.presheaf.map (homOfLE (le_top : U ≤ ⊤)).op ≫ W.germToFunctionField U =
    (Scheme.ΓSpecIso A).inv ≫ f.appTop ≫ W.germToFunctionField ⊤
  rw [hres]

private theorem originalChart_germ_apply [IsDomain A] [IsIntegral W] [IsDominant f]
    (U : W.Opens) [Nonempty U] (r : A) :
    W.germToFunctionField U (affineBaseMap f U r) =
      Scheme.functionFieldMap f (algebraMap A (Spec A).functionField r) :=
  congrArg (fun k : A ⟶ W.functionField ↦ k r) (originalChart_germ f U)

private theorem originalChart_isAlgebraic [IsDomain A] [IsIntegral W] [IsDominant f]
    (hff : IsIso (CommRingCat.ofHom (Scheme.functionFieldMap f)))
    (U : W.Opens) [Nonempty U] :
    letI := (affineBaseMap f U).toAlgebra
    Algebra.IsAlgebraic A Γ(W, U) := by
  let := (affineBaseMap f U).toAlgebra
  let := hff
  refine ⟨fun z ↦ ?_⟩
  obtain ⟨q, hq⟩ := (ConcreteCategory.bijective_of_isIso
    (CommRingCat.ofHom (Scheme.functionFieldMap f))).2 (W.germToFunctionField U z)
  obtain ⟨c, d, hd', hcd⟩ := IsFractionRing.div_surjective A q
  have hd0 : d ≠ 0 := mem_nonZeroDivisors_iff_ne_zero.mp hd'
  have hdF : Scheme.functionFieldMap f (algebraMap A (Spec A).functionField d) ≠ 0 := by
    apply (map_ne_zero (Scheme.functionFieldMap f)).mpr
    exact (map_ne_zero_iff _ (IsFractionRing.injective A (Spec A).functionField)).mpr hd0
  have hrat : Scheme.functionFieldMap f (algebraMap A (Spec A).functionField c) /
      Scheme.functionFieldMap f (algebraMap A (Spec A).functionField d) =
        W.germToFunctionField U z := by
    rw [← map_div₀, hcd]
    exact hq
  have hrel : affineBaseMap f U d * z = affineBaseMap f U c := by
    apply W.germToFunctionField_injective U
    rw [map_mul, originalChart_germ_apply, originalChart_germ_apply]
    exact (mul_comm _ _).trans ((div_eq_iff hdF).mp hrat).symm
  refine ⟨Polynomial.C d * Polynomial.X - Polynomial.C c, ?_, ?_⟩
  · intro hp
    apply hd0
    have hc := congrArg (fun p : Polynomial A ↦ p.coeff 1) hp
    simpa using hc
  · change Polynomial.aeval z (Polynomial.C d * Polynomial.X - Polynomial.C c) = 0
    simp only [map_sub, map_mul, Polynomial.aeval_C, Polynomial.aeval_X,
      RingHom.algebraMap_toAlgebra, sub_eq_zero]
    exact hrel

private theorem originalChart_isNagata [IsDomain A] [IsIntegral W]
    [IsDominant f] [QuasiCompact f] [LocallyOfFiniteType f]
    (hA : IsNagataRing.{u, 0} A) (hd : ringKrullDim A ≤ 2)
    (hff : IsIso (CommRingCat.ofHom (Scheme.functionFieldMap f)))
    (U : W.Opens) (hU : IsAffineOpen U) [Nonempty U] : IsNagataRing.{u, 0} Γ(W, U) := by
  let := (affineBaseMap f U).toAlgebra
  let : Algebra.FiniteType A Γ(W, U) := originalChart_finiteType f U hU
  let : Algebra.IsAlgebraic A Γ(W, U) := originalChart_isAlgebraic f hff U
  exact hA.of_finiteType_isAlgebraic_of_dimLE_two hd (originalChart_injective f U)

end OriginalCharts

namespace Base

variable (A : Type u) [CommRing A] [IsDomain A] (J : Ideal A) (hJ : J ≠ ⊥)

/-- Every actual nonempty affine chart of the actual normalized blowup is
Nagata by GF2 applied to its original structural scalar map. -/
theorem affineChart_isNagata (hd : ringKrullDim A ≤ 2) (hA : IsNagataRing.{u, 0} A)
    (U : (normalization A J hJ).Opens) (hU : IsAffineOpen U) [Nonempty U] :
    IsNagataRing.{u, 0} Γ(normalization A J hJ, U) := by
  let : IsNoetherianRing A := hA.isNoetherianRing
  let : IsProper (a A J hJ) := a_isProper A J hJ hd hA
  exact originalChart_isNagata (a A J hJ) hA hd (a_fieldMap_isIso A J hJ) U hU

end Base

namespace FiniteBase.Nagata

variable (A B : Type u) [CommRing A] [IsDomain A] [CommRing B] [IsDomain B]
  (J : Ideal A) (hJ : J ≠ ⊥)
  (s : Spec (.of B) ⟶ Spec (.of A)) [IsDominant s]

/-- Normality concerns the existing Y in the same original finite field extension. -/
theorem Y_normalStalks (hfin : (Scheme.functionFieldMap s).Finite) :
    NormalStalks (FiniteBase.Y A B J hJ s) :=
  Cover.Nagata.normalization_normalStalks
    (Base.a A J hJ) (Base.a_fieldMap_isIso A J hJ) s hfin

/-- The existing dominant pi is finite, with actual chart Nagata properties
derived from the original surface base. No separability is required. -/
theorem pi_isFinite (hd : ringKrullDim A ≤ 2) (hA : IsNagataRing.{u, 0} A)
    (hfin : (Scheme.functionFieldMap s).Finite) : IsFinite (FiniteBase.pi A B J hJ s) := by
  apply Cover.Nagata.pi_isFinite (Base.a A J hJ) (Base.a_fieldMap_isIso A J hJ) s hfin
  intro U hne
  let := hne
  exact Base.affineChart_isNagata A J hJ hd hA U.1 U.2

/-- Local Noetherianity follows from the same original finite pi. -/
theorem Y_isLocallyNoetherian (hd : ringKrullDim A ≤ 2) (hA : IsNagataRing.{u, 0} A)
    (hfin : (Scheme.functionFieldMap s).Finite) :
    IsLocallyNoetherian (FiniteBase.Y A B J hJ s) := by
  let : IsNoetherianRing A := hA.isNoetherianRing
  let : IsLocallyNoetherian (Base.normalization A J hJ) :=
    Base.normalization_isLocallyNoetherian A J hJ hd hA
  let : IsFinite (FiniteBase.pi A B J hJ s) := pi_isFinite A B J hJ s hd hA hfin
  exact LocallyOfFiniteType.isLocallyNoetherian (FiniteBase.pi A B J hJ s)

/-- Properness of the existing B-map uses its original pullback square and
the same finite pi. The original B-map and its function-field isomorphism remain unchanged. -/
theorem b_isProper [IsFinite s] (hd : ringKrullDim A ≤ 2) (hA : IsNagataRing.{u, 0} A)
    (hfin : (Scheme.functionFieldMap s).Finite) : IsProper (FiniteBase.b A B J hJ s) := by
  let : IsNoetherianRing A := hA.isNoetherianRing
  let : IsProper (Base.a A J hJ) := Base.a_isProper A J hJ hd hA
  let : IsFinite (Cover.pi (Base.a A J hJ) (Base.a_fieldMap_isIso A J hJ) s) :=
    pi_isFinite A B J hJ s hd hA hfin
  exact Cover.b_isProper (Base.a A J hJ) (Base.a_fieldMap_isIso A J hJ) s

end FiniteBase.Nagata

end AlgebraicGeometry.Scheme.Birational.NormalizedBlowupCover
