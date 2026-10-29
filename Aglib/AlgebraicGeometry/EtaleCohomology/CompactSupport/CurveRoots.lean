/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.EtaleCohomology.CompactSupport.FiniteComplement
public import Aglib.AlgebraicGeometry.EtaleCohomology.Kummer.CoefficientBaseChange
public import Aglib.AlgebraicGeometry.EtaleCohomology.Curves.PrimeToCharacteristicVanishing
public import Aglib.AlgebraicGeometry.Morphisms.Proper.GlobalSections
public import Aglib.AlgebraicGeometry.Geometrically.Integral.SmoothCurve
public import Aglib.AlgebraicGeometry.Morphisms.Smooth.Dimension
public import Aglib.AlgebraicGeometry.Curves.Basic

/-!
# Compactly supported cohomology of roots of unity on an affine curve

Let `j : U ⟶ X` be an open immersion whose closed complement `D` is a finite set of closed
points with separably closed residue fields, and let `n > 0` be invertible on `X`. The map
`H^r_c(U, μ_n) → H^r(X, μ_n)` is induced by `j_! μ_{n,U} ⟶ μ_{n,X}`, the adjoint of the inverse
of the canonical isomorphism `j^* μ_{n,X} ≅ μ_{n,U}` of the Kummer root sheaves
(`Kummer.CoefficientBaseChange.rootsPullbackIso`). It is bijective for `r ≥ 2`, by the
open-closed sequence `0 → j_! j^* μ_n → μ_n → i_* i^* μ_n → 0` and the vanishing of the
positive cohomology of the finite closed part (Milne, *Lectures on Étale Cohomology* v2.21,
proof of Prop. 14.5, p. 92; SGA 4, Exp. XVIII, (1.1.3.1)).

For a smooth proper geometrically connected curve `X` over a separably closed field `k`
(`Scheme.OverField.Curve.Properties`; in particular over an algebraically closed field),
`n` invertible in `k`, a finite nonempty set `D` of closed points and `U = X − D`:

* `H^2_c(U, μ_n) → H^2(X, μ_n)` is an isomorphism (SGA 4, Exp. XVIII, (1.1.3.1));
* `H^r_c(U, μ_n) = 0` for `r ≥ 3`, by `Curves.roots_subsingleton_H_of_curve`;
* `H^0_c(U, μ_n) = 0`, because the global sections of `X` form a field, so that a global
  root of unity is determined by its value on the nonempty finite support.

The identification `H^2(X, μ_n) ≅ ℤ/n` is not asserted here.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite
open GroupCohomology.Kummer.Coefficients GroupCohomology.Kummer.CoefficientBaseChange

universe w u

namespace AlgebraicGeometry.Scheme.EtaleCohomology.CompactSupport

attribute [local instance] hasSheafifyLarge

open Curves.FiniteClosedSupport

section Sections

variable {X : Scheme.{u}} [HasExt.{w} (AbelianSheaf.{u, u + 1} X)]

/-- A morphism of abelian sheaves whose global-section map is injective is injective on
degree-zero cohomology. -/
private theorem sheafHMap_zero_injective {F G : AbelianSheaf.{u, u + 1} X} (f : F ⟶ G)
    (hf : Function.Injective (f.hom.app (op (etaleTerminal X)))) :
    Function.Injective (Sheaf.H.map f 0) := by
  intro x y hxy
  have hT := etaleTerminalIsTerminal X
  apply (Sheaf.H.equiv₀ F hT).injective
  apply hf
  rw [Sheaf.H.equiv₀_naturality hT f x, Sheaf.H.equiv₀_naturality hT f y, hxy]

omit [HasExt.{w} (AbelianSheaf.{u, u + 1} X)] in
/-- The literal root pullback is injective on global sections when the ring map of global
sections along the base change of `i` is injective. -/
private theorem rootsUnit_app_injective {Z : Scheme.{u}} (i : Z ⟶ X) (n : ℕ)
    (hφ : Function.Injective (pullback.fst (etaleTerminal X).hom i).appTop.hom) :
    Function.Injective ((rootsUnit i n).hom.app (op (etaleTerminal X))) := by
  intro a b hab
  have ha := rootsUnit_sections i n (op (etaleTerminal X)) a
  have hb := rootsUnit_sections i n (op (etaleTerminal X)) b
  rw [hab, hb] at ha
  have h := Units.map_injective
    (f := (pullback.fst (etaleTerminal X).hom i).appTop.hom.toMonoidHom) hφ ha
  apply (rootsSections X n (op (etaleTerminal X))).injective
  apply Additive.toMul.injective
  exact Subtype.ext h.symm

omit [HasExt.{w} (AbelianSheaf.{u, u + 1} X)] in
/-- The original unit `μ_{n,X} ⟶ i_* i^* μ_{n,X}` is injective on global sections under the
same condition. -/
private theorem rootsAdjunctionUnit_app_injective {Z : Scheme.{u}} (i : Z ⟶ X) (n : ℕ)
    (hn : 0 < n) (hinv : IsUnit (n : Γ(X, ⊤)))
    (hφ : Function.Injective (pullback.fst (etaleTerminal X).hom i).appTop.hom) :
    Function.Injective
      (((inverseImageAdjunction i).unit.app (mu X n)).hom.app (op (etaleTerminal X))) := by
  have h := rootsUnit_app_injective i n hφ
  rw [← rootsPullbackIso_unit i n hn hinv] at h
  intro a b hab
  apply h
  simp only [ObjectProperty.FullSubcategory.comp_hom, NatTrans.comp_app,
    ConcreteCategory.comp_apply, hab]

end Sections

section Roots

variable {U X : Scheme.{u}} (j : U ⟶ X) [IsOpenImmersion j] (n : ℕ) (hn : 0 < n)
  (hinv : IsUnit (n : Γ(X, ⊤)))

/-- The map `j_! μ_{n,U} ⟶ μ_{n,X}`: extension by zero of the inverse of the canonical root
isomorphism `j^* μ_{n,X} ≅ μ_{n,U}`, followed by the original counit. -/
def rootsExtensionMap : (etaleLowerShriek j).obj (mu U n) ⟶ mu X n :=
  (etaleLowerShriek j).map (rootsPullbackIso j n hn hinv).inv ≫
    (etaleLowerShriekAdjunction j).counit.app (mu X n)

variable [HasExt.{w} (AbelianSheaf.{u, u + 1} X)]

/-- The map `H^r_c(U, μ_n) → H^r(X, μ_n)` induced by `rootsExtensionMap`. -/
def rootsMap (r : ℕ) : H j (mu U n) r →+ Sheaf.H.{w} (mu X n) r :=
  Sheaf.H.map (rootsExtensionMap j n hn hinv) r

/-- The roots map is the coefficient isomorphism followed by the original counit map. -/
theorem rootsMap_eq_comp (r : ℕ) :
    rootsMap j n hn hinv r =
      (counitMap j (mu X n) r).comp (H.map j (rootsPullbackIso j n hn hinv).inv r) := by
  refine AddMonoidHom.ext fun x => ?_
  exact Sheaf.H.map_comp_apply _ _ x

variable (D : Set X) (hD : Set.range j = Dᶜ) (hfin : D.Finite)
  (hclosed : ∀ x ∈ D, IsClosed ({x} : Set X))

include hD hfin hclosed

/-- `H^0_c(U, μ_n) → H^0(X, μ_n)` is injective. -/
theorem rootsMap_zero_injective : Function.Injective (rootsMap j n hn hinv 0) := by
  rw [rootsMap_eq_comp]
  exact (counitMap_zero_injective_of_finite D hfin hclosed j hD (mu X n)).comp
    (H.map_bijective_of_isIso j _ 0).injective

include hn hinv in
/-- `H^0_c(U, μ_n)` vanishes when global roots of unity are detected on the finite support,
which holds when the ring map of global sections along the support is injective. -/
theorem subsingleton_H_roots_zero_of_injective
    (hφ : Function.Injective (pullback.fst (etaleTerminal X).hom (inclusion X D)).appTop.hom) :
    Subsingleton (H j (mu U n) 0) := by
  let : IsClosedImmersion (inclusion X D) := inclusion_isClosedImmersion X D hfin hclosed
  have hunitMap : Function.Injective
      (Sheaf.H.map ((inverseImageAdjunction (inclusion X D)).unit.app (mu X n)) 0) :=
    sheafHMap_zero_injective _
      (rootsAdjunctionUnit_app_injective (inclusion X D) n hn hinv hφ)
  have hzero : Subsingleton (H j ((inverseImage j).obj (mu X n)) 0) := by
    refine ⟨fun x y => counitMap_zero_injective_of_finite D hfin hclosed j hD (mu X n) ?_⟩
    have hx := (exact_counitMap_unitMap j (inclusion X D)
      (range_eq_compl_range_inclusion D j hD) (mu X n) 0 (counitMap j (mu X n) 0 x)).mpr
        ⟨x, rfl⟩
    have hy := (exact_counitMap_unitMap j (inclusion X D)
      (range_eq_compl_range_inclusion D j hD) (mu X n) 0 (counitMap j (mu X n) 0 y)).mpr
        ⟨y, rfl⟩
    exact hunitMap (hx.trans hy.symm)
  exact (H.map_bijective_of_isIso j (rootsPullbackIso j n hn hinv).inv 0).injective.subsingleton

variable (hsep : ∀ x : D, IsSepClosed (X.residueField x.val))

include hsep

/-- `H^r_c(U, μ_n) → H^r(X, μ_n)` is bijective for `r ≥ 2`. -/
theorem rootsMap_bijective_of_sepClosed (r : ℕ) (hr : 2 ≤ r) :
    Function.Bijective (rootsMap j n hn hinv r) := by
  rw [rootsMap_eq_comp]
  exact (counitMap_bijective_of_finite_of_sepClosed D hfin hclosed hsep j hD (mu X n) r hr).comp
    (H.map_bijective_of_isIso j _ r)

/-- The isomorphism `H^r_c(U, μ_n) ≃+ H^r(X, μ_n)` for `r ≥ 2`. -/
def rootsAddEquiv (r : ℕ) (hr : 2 ≤ r) : H j (mu U n) r ≃+ Sheaf.H.{w} (mu X n) r :=
  AddEquiv.ofBijective (rootsMap j n hn hinv r)
    (rootsMap_bijective_of_sepClosed j n hn hinv D hD hfin hclosed hsep r hr)

theorem rootsAddEquiv_apply (r : ℕ) (hr : 2 ≤ r) (x : H j (mu U n) r) :
    rootsAddEquiv j n hn hinv D hD hfin hclosed hsep r hr x = rootsMap j n hn hinv r x :=
  rfl

end Roots

section Curve

open Scheme.OverField

variable {k : Type u} [Field k] (X : FScheme k) (hX : Curve.Properties X)

include hX in
/-- A smooth proper geometrically connected curve over a field is integral. -/
private theorem curve_isIntegral : IsIntegral X.left := by
  let := hX.smooth
  let := hX.connected
  let : GeometricallyIntegral X.hom :=
    Scheme.geometricallyIntegral_of_smoothOfRelativeDimension_one_of_geometricallyConnected
      X.hom
  exact GeometricallyIntegral.isIntegral_of_subsingleton X.hom

include hX in
/-- A smooth proper geometrically connected curve over a field has dimension at most one. -/
private theorem curve_topologicalKrullDim_le_one : topologicalKrullDim X.left ≤ 1 := by
  let := curve_isIntegral X hX
  rw [smoothFieldDimension k X.left X.hom 1 hX.smooth inferInstance]
  exact le_of_eq Nat.cast_one

/-- A level invertible in the base field is invertible in the global sections. -/
theorem isUnit_natCast_globalSections {n : ℕ} (hunit : IsUnit (n : k)) :
    IsUnit (n : Γ(X.left, ⊤)) := by
  have h : IsUnit (n : Γ(Spec (.of k), ⊤)) := by
    simpa using hunit.map (Scheme.ΓSpecIso (CommRingCat.of k)).inv.hom
  exact levelInvertible X.hom n h

variable [IsSepClosed k]

include hX in
/-- Closed points of a curve over a separably closed field have separably closed residue
fields. -/
private theorem curve_closedPoint_isSepClosed (x : X.left)
    (hx : IsClosed ({x} : Set X.left)) :
    IsSepClosed (X.left.residueField x) := by
  let := hX.proper
  let := residueAlgebra X.left X.hom x
  let : Module.Finite k (X.left.residueField x) := residue_finite X.left X.hom ⟨x, hx⟩
  exact Algebra.IsAlgebraic.isSepClosed (F := k) (E := X.left.residueField x)

variable (D : Set X.left) (hfin : D.Finite) (hclosed : ∀ x ∈ D, IsClosed ({x} : Set X.left))
  {U : Scheme.{u}} (j : U ⟶ X.left) [IsOpenImmersion j] (hD : Set.range j = Dᶜ)
  (n : ℕ) [HasExt.{w} (AbelianSheaf.{u, u + 1} X.left)]

include hX hfin hclosed hD

/-- For a curve over a separably closed field, `H^r_c(U, μ_n) → H^r(X, μ_n)` is an isomorphism
for `r ≥ 2`. For `r = 2` this is the isomorphism `H^2_c(U, μ_n) ≅ H^2(X, μ_n)` in the proof of
Milne, *Lectures on Étale Cohomology* v2.21, Prop. 14.5, p. 92 (SGA 4, Exp. XVIII, (1.1.3.1));
the identification with `ℤ/n` is not asserted. The level data `hn` and `hinv` are needed to
form the canonical root isomorphism that defines the map; both follow from `IsUnit (n : k)`. -/
theorem rootsMap_bijective_of_curve (hn : 0 < n) (hinv : IsUnit (n : Γ(X.left, ⊤))) (r : ℕ)
    (hr : 2 ≤ r) : Function.Bijective (rootsMap j n hn hinv r) :=
  rootsMap_bijective_of_sepClosed j n hn hinv D hD hfin hclosed
    (fun x => curve_closedPoint_isSepClosed X hX x.val (hclosed x.val x.property)) r hr

/-- For a curve over a separably closed field and `n` invertible in `k`, `H^r_c(U, μ_n) = 0`
for `r ≥ 3`. -/
theorem subsingleton_H_roots_of_curve (hunit : IsUnit (n : k)) (r : ℕ) (hr : 3 ≤ r) :
    Subsingleton (H j (mu U n) r) := by
  let := hX.proper
  have hn : 0 < n := Nat.pos_of_ne_zero (by rintro rfl; simp at hunit)
  have hinv := isUnit_natCast_globalSections X hunit
  let : CompactSpace X.left := QuasiCompact.compactSpace_of_compactSpace X.hom
  have : Subsingleton (Sheaf.H.{w} (mu X.left n) r) :=
    Curves.roots_subsingleton_H_of_curve k X.left X.hom (curve_topologicalKrullDim_le_one X hX)
      n hn hunit hinv r (by omega)
  exact (rootsMap_bijective_of_curve X hX D hfin hclosed j hD n hn hinv r
    (by omega)).injective.subsingleton

omit [IsSepClosed k] in
/-- For a curve over a field, `n` invertible in `k` and a nonempty finite set of closed points,
`H^0_c(U, μ_n) = 0`. -/
theorem subsingleton_H_roots_zero_of_curve (hDne : D.Nonempty) (hunit : IsUnit (n : k)) :
    Subsingleton (H j (mu U n) 0) := by
  let := hX.proper
  have hn : 0 < n := Nat.pos_of_ne_zero (by rintro rfl; simp at hunit)
  have hinv := isUnit_natCast_globalSections X hunit
  let := curve_isIntegral X hX
  let : Field Γ(X.left, ⊤) := (globalSections_isField X).toField
  obtain ⟨x, hx⟩ := hDne
  have : IsIso (etaleTerminal X.left).hom := by
    change IsIso (𝟙 X.left)
    infer_instance
  let p : pointScheme X.left D :=
    Sigma.ι (fun x : D => Spec (X.left.residueField x.val)) ⟨x, hx⟩
      (IsLocalRing.closedPoint (X.left.residueField x))
  let q : ↥(pullback (etaleTerminal X.left).hom (inclusion X.left D)) :=
    inv (pullback.snd (etaleTerminal X.left).hom (inclusion X.left D)) p
  let : Nonempty (⊤ : (pullback (etaleTerminal X.left).hom (inclusion X.left D)).Opens) :=
    ⟨⟨q, trivial⟩⟩
  have hφ : Function.Injective
      (pullback.fst (etaleTerminal X.left).hom (inclusion X.left D)).appTop.hom :=
    RingHom.injective (R := Γ(X.left, ⊤)) _
  exact subsingleton_H_roots_zero_of_injective j n hn hinv D hD hfin hclosed hφ

end Curve

end AlgebraicGeometry.Scheme.EtaleCohomology.CompactSupport
