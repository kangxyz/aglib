/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.AffineScheme.AlgebraMapTriangles
public import Aglib.AlgebraicGeometry.Stalk.Scalar
public import Aglib.RingTheory.Smooth.ArtinianLifting
public import Mathlib.AlgebraicGeometry.Morphisms.Smooth
public import Mathlib.AlgebraicGeometry.Noetherian
public import Mathlib.AlgebraicGeometry.Stalk

/-!
# Smoothness from lifting of points along square-zero thickenings

Let `k` be a commutative ring and `π : X ⟶ Spec k` a morphism. The predicate
`Scheme.Hom.LiftsAlongNoetherianSquareZero π` says: for every surjection `g : A' → A` of
`k`-algebras with `A'` Noetherian and `(ker g) ^ 2 = 0`, every point `a : Spec A ⟶ X` over
`Spec k` extends to a point `a' : Spec A' ⟶ X` over `Spec k` with `Spec g ≫ a' = a`. It is stated
through ordinary morphisms of schemes, so any representation of a functor by `X` on (locally)
Noetherian test schemes over `Spec k` can supply it.

* `Scheme.Hom.LiftsAlongNoetherianSquareZero.exists_lift_stalk`: the predicate gives, for every
  point `x`, the lifting of surjective `k`-algebra maps `𝒪_{X,x} → A` along square-zero
  surjections `A' → A` of Artinian local `k`-algebras, through Mathlib's correspondence between
  local maps out of `𝒪_{X,x}` and morphisms from the spectrum of a local ring sending the closed
  point to `x`.
* `Scheme.Hom.formallySmooth_stalkMap_of_liftsAlongNoetherianSquareZero`: if `k` is Noetherian
  and `π` is locally of finite type, every stalk map of `π` is formally smooth. The stalk is the
  localization of the finite type `k`-algebra of sections over an affine open neighbourhood, so
  the Artinian-test criterion
  `Algebra.FormallySmooth.of_lift_artinianLocal_squareZero_of_isLocalization` applies at every
  point; no condition on the residue field is needed.
* `Scheme.Hom.smooth_of_liftsAlongNoetherianSquareZero`: under the same hypotheses `π` is smooth
  (Mathlib's `Scheme.Hom.smoothLocus_eq_top_iff`).

Source: Kleiman, *The Picard scheme*, arXiv:math/0504020v1, proof of Prop. 5.19, p. 47, where the
infinitesimal criterion for smoothness (quoted from SGA 1) is applied to Artin local test rings.
Here the base is any Noetherian ring, in particular any field.
-/

@[expose] public section

noncomputable section

open CategoryTheory IsLocalRing

universe u

namespace AlgebraicGeometry.Scheme

variable {k : Type u} [CommRing k] {X : Scheme.{u}}

/-- **Points lift along Noetherian square-zero thickenings.** For every surjection `g : A' → A`
of `k`-algebras with `A'` Noetherian and `(ker g) ^ 2 = 0`, every point `a : Spec A ⟶ X` over
`Spec k` extends to a point `a' : Spec A' ⟶ X` over `Spec k` with `Spec g ≫ a' = a`. -/
def Hom.LiftsAlongNoetherianSquareZero (π : X ⟶ Spec (.of k)) : Prop :=
  ∀ (A' A : Type u) [CommRing A'] [CommRing A] [Algebra k A'] [Algebra k A] [IsNoetherianRing A']
    (g : A' →ₐ[k] A), Function.Surjective g → RingHom.ker g ^ 2 = ⊥ →
    ∀ a : Spec (.of A) ⟶ X, a ≫ π = Spec.algebraMap k A →
      ∃ a' : Spec (.of A') ⟶ X, a' ≫ π = Spec.algebraMap k A' ∧
        Spec.map (CommRingCat.ofHom g.toRingHom) ≫ a' = a

/-- **Lifting at a stalk.** If points of `X` lift along Noetherian square-zero thickenings, then
for every point `x`, with `𝒪_{X,x}` a `k`-algebra through the structural scalar map, every
surjective `k`-algebra map `𝒪_{X,x} → A` lifts along every surjection `A' → A` of `k`-algebras
with `A'` Artinian local and square-zero kernel. -/
theorem Hom.LiftsAlongNoetherianSquareZero.exists_lift_stalk {π : X ⟶ Spec (.of k)}
    (H : π.LiftsAlongNoetherianSquareZero) (x : X) :
    letI := (π.stalkScalar x).toAlgebra
    ∀ (A' A : Type u) [CommRing A'] [CommRing A] [IsLocalRing A'] [IsArtinianRing A']
      [Algebra k A'] [Algebra k A] (g : A' →ₐ[k] A), Function.Surjective g →
      RingHom.ker g ^ 2 = ⊥ → ∀ φ : X.presheaf.stalk x →ₐ[k] A, Function.Surjective φ →
        ∃ ψ : X.presheaf.stalk x →ₐ[k] A', g.comp ψ = φ := by
  let := (π.stalkScalar x).toAlgebra
  intro A' A _ _ _ _ _ _ g hg hK φ hφ
  -- `A` is nontrivial, hence local, and `g` and `φ` are local homomorphisms.
  have : Nontrivial A := by
    refine ⟨⟨0, 1, fun h => ?_⟩⟩
    have h1 : (1 : A') ∈ RingHom.ker g := by
      rw [RingHom.mem_ker, map_one]
      exact h.symm
    have h2 : (1 : A') ∈ RingHom.ker g ^ 2 := by
      rw [← one_mul (1 : A'), pow_two]
      exact Ideal.mul_mem_mul h1 h1
    rw [hK, Ideal.mem_bot] at h2
    exact one_ne_zero h2
  have : IsLocalRing A := IsLocalRing.of_surjective' g.toRingHom hg
  have hgl : IsLocalHom (CommRingCat.ofHom g.toRingHom).hom := IsLocalHom.of_surjective _ hg
  have hφl : IsLocalHom (CommRingCat.ofHom φ.toRingHom).hom := IsLocalHom.of_surjective _ hφ
  -- The point `a = Spec φ ≫ (Spec 𝒪_{X,x} → X)` over `Spec k`, and its lift `a'`.
  have hscalar : X.fromSpecStalk x ≫ π = Spec.map (CommRingCat.ofHom (π.stalkScalar x)) := by
    rw [← SpecMap_stalkMap_fromSpecStalk, Spec.fromSpecStalk_eq, ← Spec.map_comp]
    congr 1
    ext r
    rw [Hom.stalkScalar_eq_local]
    rfl
  let a : Spec (.of A) ⟶ X := Spec.map (CommRingCat.ofHom φ.toRingHom) ≫ X.fromSpecStalk x
  have ha : a ≫ π = Spec.algebraMap k A := by
    rw [Category.assoc, hscalar]
    exact Spec.map_algHom_algebraMap φ
  obtain ⟨a', ha', hga'⟩ := H A' A g hg hK a ha
  -- The closed point of `Spec A'` maps to `x`.
  have hx : a' (closedPoint (CommRingCat.of A')) = x := by
    have h1 : (Spec.map (CommRingCat.ofHom g.toRingHom)) (closedPoint (CommRingCat.of A)) =
        closedPoint (CommRingCat.of A') := Spec_closedPoint
    have h2 : (Spec.map (CommRingCat.ofHom φ.toRingHom)) (closedPoint (CommRingCat.of A)) =
        closedPoint (X.presheaf.stalk x) := Spec_closedPoint
    calc a' (closedPoint (CommRingCat.of A'))
        = a' ((Spec.map (CommRingCat.ofHom g.toRingHom)) (closedPoint (CommRingCat.of A))) := by
          rw [h1]
      _ = (Spec.map (CommRingCat.ofHom g.toRingHom) ≫ a') (closedPoint (CommRingCat.of A)) :=
          (Scheme.Hom.comp_apply _ _ _).symm
      _ = a (closedPoint (CommRingCat.of A)) := by rw [hga']
      _ = X.fromSpecStalk x
            ((Spec.map (CommRingCat.ofHom φ.toRingHom)) (closedPoint (CommRingCat.of A))) :=
          Scheme.Hom.comp_apply _ _ _
      _ = x := by rw [h2, fromSpecStalk_closedPoint]
  -- `a'` factors through a local map `φ' : 𝒪_{X,x} → A'` (Mathlib's `stalkClosedPointTo`).
  have key : ∀ {y : X}, a' (closedPoint (CommRingCat.of A')) = y →
      ∃ φ' : X.presheaf.stalk y ⟶ CommRingCat.of A', IsLocalHom φ'.hom ∧
        Spec.map φ' ≫ X.fromSpecStalk y = a' := by
    rintro y rfl
    exact ⟨stalkClosedPointTo a', inferInstance, Spec_stalkClosedPointTo_fromSpecStalk a'⟩
  obtain ⟨φ', hφ'l, hφ'⟩ := key hx
  -- `φ'` is a `k`-algebra map, since `a'` lies over `Spec k`.
  have hk : CommRingCat.ofHom (π.stalkScalar x) ≫ φ' =
      CommRingCat.ofHom (algebraMap k A') := by
    apply Spec.map_injective
    rw [Spec.map_comp, ← hscalar, ← Category.assoc, hφ']
    exact ha'
  let ψ : X.presheaf.stalk x →ₐ[k] A' :=
    { φ'.hom with commutes' := fun c => congrArg (fun f => f.hom c) hk }
  refine ⟨ψ, ?_⟩
  -- `g ∘ ψ = φ`: both are local maps out of the stalk with the same spectrum morphism.
  have hl₁ : IsLocalHom (φ' ≫ CommRingCat.ofHom g.toRingHom).hom :=
    inferInstanceAs (IsLocalHom ((CommRingCat.ofHom g.toRingHom).hom.comp φ'.hom))
  have heq : Spec.map (φ' ≫ CommRingCat.ofHom g.toRingHom) ≫ X.fromSpecStalk x =
      Spec.map (CommRingCat.ofHom φ.toRingHom) ≫ X.fromSpecStalk x := by
    rw [Spec.map_comp_assoc, hφ', hga']
  have := (SpecToEquivOfLocalRing X (CommRingCat.of A)).symm.injective
    (a₁ := ⟨x, φ' ≫ CommRingCat.ofHom g.toRingHom, hl₁⟩)
    (a₂ := ⟨x, CommRingCat.ofHom φ.toRingHom, hφl⟩) heq
  have h' : φ' ≫ CommRingCat.ofHom g.toRingHom = CommRingCat.ofHom φ.toRingHom :=
    congrArg Subtype.val (eq_of_heq (Sigma.mk.inj_iff.mp this).2)
  exact AlgHom.ext fun c => congrArg (fun f => f.hom c) h'

/-- Formal smoothness of the structural scalar map `k → 𝒪_{X,x}` gives formal smoothness of the
stalk map `𝒪_{Spec k, π x} → 𝒪_{X,x}`, since `k → 𝒪_{Spec k, π x}` is a localization. -/
theorem Hom.formallySmooth_stalkMap_of_formallySmooth_stalkScalar (π : X ⟶ Spec (.of k))
    (x : X) (h : (π.stalkScalar x).FormallySmooth) : (π.stalkMap x).hom.FormallySmooth := by
  have hgerm : ((Spec (.of k)).presheaf.germ ⊤ (π x) trivial).hom.FormallyUnramified := by
    let := (Spec (.of k)).presheaf.algebra_section_stalk (U := ⊤) ⟨π x, trivial⟩
    let hU := isAffineOpen_top (Spec (.of k))
    have := hU.isLocalization_stalk ⟨π x, trivial⟩
    exact RingHom.formallyUnramified_algebraMap.mpr
      (Algebra.FormallyUnramified.of_isLocalization
        (hU.primeIdealOf ⟨π x, trivial⟩).asIdeal.primeCompl)
  have hΓ : (Scheme.ΓSpecIso (.of k)).inv.hom.FormallyUnramified :=
    RingHom.FormallyUnramified.of_surjective
      (Scheme.ΓSpecIso (.of k)).symm.commRingCatIsoToRingEquiv.surjective
  have hβ := hΓ.comp hgerm
  let : Algebra k ((Spec (.of k)).presheaf.stalk (π x)) :=
    (((Spec (.of k)).presheaf.germ ⊤ (π x) trivial).hom.comp
      (Scheme.ΓSpecIso (.of k)).inv.hom).toAlgebra
  let : Algebra ((Spec (.of k)).presheaf.stalk (π x)) (X.presheaf.stalk x) :=
    (π.stalkMap x).hom.toAlgebra
  let : Algebra k (X.presheaf.stalk x) := (π.stalkScalar x).toAlgebra
  have : IsScalarTower k ((Spec (.of k)).presheaf.stalk (π x)) (X.presheaf.stalk x) :=
    IsScalarTower.of_algebraMap_eq' (Hom.stalkScalar_eq_local π x)
  have : Algebra.FormallyUnramified k ((Spec (.of k)).presheaf.stalk (π x)) := hβ
  have : Algebra.FormallySmooth k (X.presheaf.stalk x) := h
  exact RingHom.formallySmooth_algebraMap.mpr
    (Algebra.FormallySmooth.of_restrictScalars (R := k)
      (A := (Spec (.of k)).presheaf.stalk (π x)) (B := X.presheaf.stalk x))

/-- **Formally smooth stalks from lifting** (Kleiman, *The Picard scheme*,
arXiv:math/0504020v1, proof of Prop. 5.19, p. 47). Let `k` be a Noetherian ring and
`π : X ⟶ Spec k` locally of finite type. If points of `X` lift along Noetherian square-zero
thickenings, then every stalk map of `π` is formally smooth. -/
theorem Hom.formallySmooth_stalkMap_of_liftsAlongNoetherianSquareZero [IsNoetherianRing k]
    {π : X ⟶ Spec (.of k)} [LocallyOfFiniteType π] (H : π.LiftsAlongNoetherianSquareZero)
    (x : X) : (π.stalkMap x).hom.FormallySmooth := by
  apply Hom.formallySmooth_stalkMap_of_formallySmooth_stalkScalar
  let := (π.stalkScalar x).toAlgebra
  obtain ⟨_, ⟨V, hV, rfl⟩, hxV, -⟩ :=
    X.isBasis_affineOpens.exists_subset_of_mem_open (Set.mem_univ x) isOpen_univ
  have e : V ≤ π ⁻¹ᵁ ⊤ := fun _ _ => trivial
  let : Algebra k Γ(X, V) :=
    ((π.appLE ⊤ V e).hom.comp (Scheme.ΓSpecIso (.of k)).inv.hom).toAlgebra
  have : Algebra.FiniteType k Γ(X, V) := by
    have h1 := π.finiteType_appLE (isAffineOpen_top (Spec (.of k))) hV e
    have h2 : (Scheme.ΓSpecIso (.of k)).inv.hom.FiniteType :=
      RingHom.FiniteType.of_surjective _
        (Scheme.ΓSpecIso (.of k)).symm.commRingCatIsoToRingEquiv.surjective
    exact h1.comp h2
  let : Algebra Γ(X, V) (X.presheaf.stalk x) := X.presheaf.algebra_section_stalk ⟨x, hxV⟩
  have hgerm : π.appLE ⊤ V e ≫ X.presheaf.germ V x hxV =
      π.appTop ≫ X.presheaf.germ ⊤ x trivial := by
    rw [Scheme.Hom.appLE, Category.assoc, TopCat.Presheaf.germ_res]
    rfl
  have : IsScalarTower k Γ(X, V) (X.presheaf.stalk x) := by
    apply IsScalarTower.of_algebraMap_eq'
    change π.stalkScalar x = (X.presheaf.germ V x hxV).hom.comp
      ((π.appLE ⊤ V e).hom.comp (Scheme.ΓSpecIso (.of k)).inv.hom)
    rw [← RingHom.comp_assoc, ← CommRingCat.hom_comp, hgerm]
    rfl
  have := hV.isLocalization_stalk ⟨x, hxV⟩
  exact Algebra.FormallySmooth.of_lift_artinianLocal_squareZero_of_isLocalization
    (hV.primeIdealOf ⟨x, hxV⟩).asIdeal (H.exists_lift_stalk x)

/-- **Smoothness from lifting** (Kleiman, *The Picard scheme*, arXiv:math/0504020v1, proof of
Prop. 5.19, p. 47). Let `k` be a Noetherian ring, for instance a field, and `π : X ⟶ Spec k`
locally of finite type. If points of `X` lift along Noetherian square-zero thickenings, then `π`
is smooth. -/
theorem Hom.smooth_of_liftsAlongNoetherianSquareZero [IsNoetherianRing k]
    {π : X ⟶ Spec (.of k)} [LocallyOfFiniteType π] (H : π.LiftsAlongNoetherianSquareZero) :
    Smooth π := by
  rw [← Scheme.Hom.smoothLocus_eq_top_iff, ← top_le_iff]
  rintro x -
  exact Scheme.Hom.mem_smoothLocus.mpr
    (π.formallySmooth_stalkMap_of_liftsAlongNoetherianSquareZero H x)

end AlgebraicGeometry.Scheme
