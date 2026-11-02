/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.EtaleCohomology.Curves.KummerGenericRepresentative
public import Aglib.AlgebraicGeometry.EtaleCohomology.Kummer.GenericRepresentativePullback
public import Aglib.AlgebraicGeometry.RationalPoint.BaseChangeOrder

/-! # Original Kummer residues in rational base-change squares

The actual function-field square transports the positive generic representative.
The actual stalk map at a cartesian rational section preserves order, hence the
original residue. The final theorem obtains its representative from the proved
curve construction, rather than assuming a cohomological comparison. All four
Ext universes remain independent. No global-unit roots, genus, properness,
finite boundary enumeration, or target-field algebraic closure is assumed.
-/

@[expose] public noncomputable section

open CategoryTheory AlgebraicGeometry TopologicalSpace
open AlgebraicGeometry.Scheme.EtaleCohomology
open GroupCohomology.Kummer.Coefficients
open GroupCohomology.Kummer.CoefficientBaseChange
open GroupCohomology.Kummer.Torsor

universe u wU wV wKU wKV

namespace AlgebraicGeometry.Scheme.EtaleCohomology.Curves.KummerResidueNaturality

variable {X Y U V : Scheme.{u}}
  [IsIntegral X] [IsIntegral Y] [IsIntegral U] [IsIntegral V]
  (j : U ⟶ X) (j' : V ⟶ Y) [IsOpenImmersion j] [IsOpenImmersion j']
  (a : V ⟶ U) (b : Y ⟶ X) [IsDominant a] [IsDominant b]
  (hsq : a ≫ j = j' ≫ b)

local instance : IsDominant j := Scheme.isDominant_of_isOpenImmersion j
local instance : IsDominant j' := Scheme.isDominant_of_isOpenImmersion j'

include hsq in
/-- The original open square induces its literal contravariant function-field square. -/
theorem functionFieldMap_openSquare :
    (Scheme.functionFieldMap a).comp (Scheme.functionFieldMap j) =
      (Scheme.functionFieldMap j').comp (Scheme.functionFieldMap b) := by
  have hcongr {f g : V ⟶ X} [IsDominant f] [IsDominant g] (h : f = g) :
      Scheme.functionFieldMap f = Scheme.functionFieldMap g := by
    subst g
    rfl
  exact (Scheme.functionFieldMap_comp a j).symm.trans
    ((hcongr hsq).trans (Scheme.functionFieldMap_comp j' b))

variable {k K : Type u} [Field k] [Field K]
  [IsNoetherian X] [IsNoetherian Y]
  [hDX : ∀ x : ClosedPoint X, IsDiscreteValuationRing (X.presheaf.stalk x.val)]
  [hDY : ∀ y : ClosedPoint Y, IsDiscreteValuationRing (Y.presheaf.stalk y.val)]
  (r : RationalPoint k X) (s : RationalPoint K Y)
  (q : Spec (.of K) ⟶ Spec (.of k))
  (H : IsPullback q s.sectionMap r.sectionMap b)

include hsq H in
/-- Original boundary orders agree at cartesian rational sections, with the
same function-field unit transported through the actual open square. -/
theorem boundaryOrder_functionFieldUnitMap (f : U.functionFieldˣ) :
    KummerResidue.boundaryOrder j' ⟨s.point, s.point_isClosed⟩
        (Additive.ofMul (Scheme.functionFieldUnitMap a f)) =
      KummerResidue.boundaryOrder j ⟨r.point, r.point_isClosed⟩ (Additive.ofMul f) := by
  let g : X.functionField := (Scheme.FunctionField.fieldEquiv j).symm (f : U.functionField)
  have hjg : Scheme.functionFieldMap j g = (f : U.functionField) :=
    (Scheme.FunctionField.fieldEquiv j).apply_symm_apply _
  have hmap := DFunLike.congr_fun (functionFieldMap_openSquare j j' a b hsq) g
  have hfg : Scheme.functionFieldMap a (f : U.functionField) =
      Scheme.functionFieldMap j' (Scheme.functionFieldMap b g) :=
    (congrArg (Scheme.functionFieldMap a) hjg).symm.trans hmap
  have he : (Scheme.FunctionField.fieldEquiv j').symm
      (Scheme.functionFieldMap a (f : U.functionField)) = Scheme.functionFieldMap b g := by
    apply (Scheme.FunctionField.fieldEquiv j').injective
    exact ((Scheme.FunctionField.fieldEquiv j').apply_symm_apply _).trans hfg
  have hp := RationalPoint.point_map_of_isPullback r s q b H
  let : IsDiscreteValuationRing s.localRing := hDY ⟨s.point, s.point_isClosed⟩
  let : IsDiscreteValuationRing (X.presheaf.stalk (b s.point)) := by
    rw [hp]
    exact hDX ⟨r.point, r.point_isClosed⟩
  change Y.ord ((Scheme.FunctionField.fieldEquiv j').symm
    (Scheme.functionFieldMap a (f : U.functionField))) s.point = X.ord g r.point
  exact (congrArg (fun z : Y.functionField => Y.ord z s.point) he).trans
    ((RationalPoint.order_functionFieldMap_of_isPullback r s q b H g).trans
      (congrArg (fun z : X => X.ord g z) hp))

variable [HasExt.{wU} (AbelianSheaf.{u, u + 1} U)]
  [HasExt.{wV} (AbelianSheaf.{u, u + 1} V)]
  [HasExt.{wKU} (AbelianSheaf.{u, u + 1} (Spec U.functionField))]
  [HasExt.{wKV} (AbelianSheaf.{u, u + 1} (Spec V.functionField))]
  (n : ℕ) (hn : 0 < n) (hinv : IsUnit (n : Γ(U, ⊤)))

include hsq H in
/-- An actual positive generic representative proves original residue naturality. -/
theorem residue_h1Map_of_generic_representative (c : H1Etale U (mu U n))
    (f : U.functionFieldˣ)
    (hf : h1Map (U.fromSpecStalk (genericPoint U)) n hn hinv c =
      rootClass GroupCohomology.Kummer.RootCover.etalePowerSurjectivity
        (Spec U.functionField) n hn
        (levelInvertible (U.fromSpecStalk (genericPoint U)) n hinv)
        ((Kummer.ringGlobalUnitsEquiv U.functionField (Additive.ofMul f)).toMul)) :
    KummerResidue.residue j' n hn (levelInvertible a n hinv)
        ⟨s.point, s.point_isClosed⟩ (h1Map a n hn hinv c) =
      KummerResidue.residue j n hn hinv ⟨r.point, r.point_isClosed⟩ c := by
  have ht := GroupCohomology.Kummer.Torsor.genericPullback_rootRepresentative
    a n hn hinv c f hf
  have hsource := (congrArg (KummerResidue.fieldResidue j n hn
    (levelInvertible (U.fromSpecStalk (genericPoint U)) n hinv)
      ⟨r.point, r.point_isClosed⟩) hf).trans
        (KummerResidue.fieldResidue_rootClass j n hn
          (levelInvertible (U.fromSpecStalk (genericPoint U)) n hinv)
          ⟨r.point, r.point_isClosed⟩ (Additive.ofMul f))
  have htarget := (congrArg (KummerResidue.fieldResidue j' n hn
    (levelInvertible (V.fromSpecStalk (genericPoint V)) n (levelInvertible a n hinv))
      ⟨s.point, s.point_isClosed⟩) ht).trans
        (KummerResidue.fieldResidue_rootClass j' n hn
          (levelInvertible (V.fromSpecStalk (genericPoint V)) n (levelInvertible a n hinv))
          ⟨s.point, s.point_isClosed⟩ (Additive.ofMul (Scheme.functionFieldUnitMap a f)))
  exact htarget.trans ((congrArg (fun z : ℤ => (z : ZMod n))
    (boundaryOrder_functionFieldUnitMap j j' a b hsq r s q H f)).trans hsource.symm)

include hsq H in
/-- Original residues commute with pullback at corresponding rational points;
the positive generic representative is constructed internally on the curve. -/
theorem residue_h1Map [IsNoetherian U]
    [∀ x : ClosedPoint U, IsDiscreteValuationRing (U.presheaf.stalk x.val)]
    (hdim : topologicalKrullDim U ≤ 1) (c : H1Etale U (mu U n)) :
    KummerResidue.residue j' n hn (levelInvertible a n hinv)
        ⟨s.point, s.point_isClosed⟩ (h1Map a n hn hinv c) =
      KummerResidue.residue j n hn hinv ⟨r.point, r.point_isClosed⟩ c := by
  obtain ⟨f, _, _, hf⟩ :=
    KummerGenericRepresentative.exists_positive_generic_representative U hdim n hn hinv c
  exact residue_h1Map_of_generic_representative j j' a b hsq r s q H n hn hinv c f hf

end AlgebraicGeometry.Scheme.EtaleCohomology.Curves.KummerResidueNaturality
