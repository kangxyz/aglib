/-
Copyright (c) 2026 kangxyz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Mathlib.AlgebraicGeometry.Morphisms.Finite
public import Mathlib.AlgebraicGeometry.Morphisms.Proper
public import Mathlib.CategoryTheory.Monoidal.Cartesian.Over
public import Mathlib.FieldTheory.Finite.Basic
public import Aglib.AlgebraicGeometry.SchemeOverField

/-!
# Finite rational-point sets over finite fields

Finite rational-point set of a quasi-compact locally finite-type scheme over finite field k.

Source: `R5Lab.Aglib.AlgebraicGeometry.RationalPoints.FiniteField`, frozen R5
`f8a3314ddecffcada2ec721d26d56a937bed9690`, SHA-256
`402ccce9aaa83d53b29b2845b967411ddd072d8e1eba6e25b8680c06f31ba3d4`. Selected lines: [[35, 112]].
The actual objects, canonical maps, universes and stated premises are retained.
-/

@[expose] public section

noncomputable section
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open AlgebraicGeometry.Scheme.OverField (FScheme)
open MonoidalCategory CartesianMonoidalCategory MonObj
open scoped CategoryTheory.MonObj TensorProduct
namespace AlgebraicGeometry.Scheme.RationalPoint
universe u
attribute [local instance] Over.cartesianMonoidalCategory
variable (k : Type u) [Field k] [Fintype k]

-- Preserve the source's displayed Fintype premise; this exception is declaration-local.
set_option linter.unusedFintypeInType false in
/-- A finite-type algebra has only finitely many maps to a finite field:
a map is determined by its values on finitely many algebra generators. -/
theorem finite_algebraHom (A : Type u) [CommRing A] [Algebra k A]
    [Algebra.FiniteType k A] : Finite (A →ₐ[k] k) := by
  classical
  obtain ⟨s, hs⟩ := (Algebra.FiniteType.out : (⊤ : Subalgebra k A).FG)
  exact Finite.of_injective (fun f : A →ₐ[k] k => fun x : s => f x.val) (by
    intro f g h
    exact AlgHom.ext_of_adjoin_eq_top hs (fun x hx => congrFun h ⟨x, hx⟩))

-- Preserve the source's displayed Fintype premise; this exception is declaration-local.
set_option linter.unusedFintypeInType false in
/-- Affine finite-type rational-point finiteness, by actual coordinate maps. -/
theorem finite_affineRationalPoints (X : FScheme k) [IsAffine X.left]
    [LocallyOfFiniteType X.hom] : Finite (𝟙_ (FScheme k) ⟶ X) := by
  let a : k →+* Γ(X.left, ⊤) :=
    ((Scheme.ΓSpecIso (CommRingCat.of k)).inv ≫ X.hom.appTop).hom
  let : Algebra k Γ(X.left, ⊤) := a.toAlgebra
  have ha : a.FiniteType :=
    (HasRingHomProperty.appTop @LocallyOfFiniteType X.hom inferInstance).comp
      (RingHom.FiniteType.of_surjective _
        (ConcreteCategory.bijective_of_isIso (Scheme.ΓSpecIso (CommRingCat.of k)).inv).2)
  let : Algebra.FiniteType k Γ(X.left, ⊤) := ha
  let : Finite (Γ(X.left, ⊤) →ₐ[k] k) := finite_algebraHom k Γ(X.left, ⊤)
  let coordinates : (𝟙_ (FScheme k) ⟶ X) → (Γ(X.left, ⊤) →ₐ[k] k) := fun p =>
    { toRingHom := (p.left.appTop ≫ (Scheme.ΓSpecIso (CommRingCat.of k)).hom).hom
      commutes' := fun x => by
        have hp : p.left ≫ X.hom = 𝟙 _ := Over.w p
        have he : ((Scheme.ΓSpecIso (CommRingCat.of k)).inv ≫ X.hom.appTop) ≫
            (p.left.appTop ≫ (Scheme.ΓSpecIso (CommRingCat.of k)).hom) =
              𝟙 (CommRingCat.of k) := by
          rw [Category.assoc, ← Category.assoc X.hom.appTop p.left.appTop,
            ← Scheme.Hom.comp_appTop, hp]
          rw [Scheme.Hom.id_appTop]
          change (Scheme.ΓSpecIso (CommRingCat.of k)).inv ≫ 𝟙 _ ≫
            (Scheme.ΓSpecIso (CommRingCat.of k)).hom = _
          simp only [Category.id_comp, Iso.inv_hom_id]
        exact congrArg (fun h : CommRingCat.of k ⟶ CommRingCat.of k => h.hom x) he }
  exact Finite.of_injective coordinates (by
    intro p q h
    apply Over.OverMorphism.ext
    apply ext_of_isAffine (Y := X.left)
    apply (cancel_mono (Scheme.ΓSpecIso (CommRingCat.of k)).hom).mp
    exact CommRingCat.hom_ext (congrArg AlgHom.toRingHom h))

-- Preserve the source's displayed Fintype premise; this exception is declaration-local.
set_option linter.unusedFintypeInType false in
/-- Rational points over a finite field are finite on every quasi-compact
finite-type scheme. The proof uses a finite affine cover, not a curve-specific
finiteness input and not the eventual arithmetic quotient. -/
theorem finite_rationalPoints (X : FScheme k) [LocallyOfFiniteType X.hom]
    [QuasiCompact X.hom] : Finite (𝟙_ (FScheme k) ⟶ X) := by
  classical
  let : CompactSpace X.left := QuasiCompact.compactSpace_of_compactSpace X.hom
  let : Subsingleton (𝟙_ (FScheme k)).left :=
    inferInstanceAs (Subsingleton (Spec (CommRingCat.of k)))
  let C : X.left.OpenCover := X.left.affineCover.finiteSubcover
  let U (i : C.I₀) : FScheme k := Over.mk (C.f i ≫ X.hom)
  let (i : C.I₀) : IsAffine (U i).left :=
    inferInstanceAs (IsAffine (X.left.affineCover.finiteSubcover.X i))
  let (i : C.I₀) : LocallyOfFiniteType (U i).hom :=
    inferInstanceAs (LocallyOfFiniteType (C.f i ≫ X.hom))
  let (i : C.I₀) : Finite (𝟙_ (FScheme k) ⟶ U i) := finite_affineRationalPoints k (U i)
  let project : (Σ i : C.I₀, (𝟙_ (FScheme k) ⟶ U i)) → (𝟙_ (FScheme k) ⟶ X) :=
    fun p => p.2 ≫ Over.homMk (C.f p.1) rfl
  exact Finite.of_surjective project (by
    intro p
    let i := C.idx (p.left (IsLocalRing.closedPoint k))
    have h : Set.range p.left ⊆ Set.range (C.f i) := by
      rintro _ ⟨x, rfl⟩
      have hx : x = IsLocalRing.closedPoint k := Subsingleton.elim _ _
      rw [hx]
      exact C.covers _
    let q : 𝟙_ (FScheme k) ⟶ U i :=
      Over.homMk (IsOpenImmersion.lift (C.f i) p.left h) (by
        change IsOpenImmersion.lift (C.f i) p.left h ≫ (C.f i ≫ X.hom) = 𝟙 _
        rw [← Category.assoc, IsOpenImmersion.lift_fac]
        exact Over.w p)
    refine ⟨⟨i, q⟩, ?_⟩
    apply Over.OverMorphism.ext
    exact IsOpenImmersion.lift_fac (C.f i) p.left h)


end AlgebraicGeometry.Scheme.RationalPoint
end
