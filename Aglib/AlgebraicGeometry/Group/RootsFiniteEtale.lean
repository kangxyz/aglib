/-
Copyright (c) 2026 kangxyz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/

module

public import Aglib.AlgebraicGeometry.Group.MultiplicativeGroup
public import Mathlib.AlgebraicGeometry.Morphisms.Finite
public import Mathlib.AlgebraicGeometry.Morphisms.Etale
public import Mathlib.RingTheory.Etale.StandardEtale
public import Mathlib.Tactic.Ring
/-!
# Polynomial realization and finite étaleness of roots of unity

The input is the actual `MultiplicativeGroup.rootsScheme X n`, constructed as
an equalizer of the literal nth-power and constant-one morphisms. For every
positive n this module identifies it, in `Over X`, with the pullback of
`Spec (Γ(X, ⊤)[T]/(T^n - 1))` along the canonical map `X.toSpecΓ`.

The comparison is proved on every test scheme over X, by the Γ/Spec
adjunction, the polynomial quotient universal property, and Yoneda. Thus it
preserves the actual structure morphism; no affineness or noetherian
hypothesis on X is used. Finiteness follows from monicity. If n is a unit in
Γ(X, ⊤), the pair `(T^n - 1, 1)` is standard étale: the Bézout identity is
`(T^n - 1)' * (n⁻¹ T) + (T^n - 1) * (-1) = 1`. The resulting standard-étale
algebra is explicitly identified with the polynomial quotient. Scheme
étaleness then follows by base change.

Mathematical correspondence: Stacks Project, tag 040M (the roots-of-unity
functor), and tag 03PL (étale Kummer, the monic polynomial and invertible
derivative argument). These are source locators, not theorem assumptions.
All conclusions in this file are proved from mathlib and the constructed
multiplicative-group input, with no retained standard-theorem premise.
The level n = 1 is included; n = 0 is excluded.

Mathematical source: `K2-018#lem:k2018-geometric-exact-order`, at source
revision `e73d98b1b5c1e5abcdebf7d058e436d792b87982`.
Frozen input basis: `7f86e4a1763cc4ec35e9b0a8acd659750355a0de`;
`MultiplicativeGroup.lean` SHA-256:
`00d2f93b8d66e0059bf60def78b7ace6d0420906d1aa114a62daca46972179ea`.
This is the weight-one roots scheme, not a replacement for the arithmetic
weight-two coefficient in the final Kummer application.
-/

@[expose] public section

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Opposite Polynomial
namespace AlgebraicGeometry.Scheme.Group.RootsFiniteEtale
universe u
variable (R : Type u) [CommRing R]
/-- The literal monic polynomial defining nth roots of unity. -/
def rootPolynomial (n : ℕ) : R[X] := X ^ n - 1
/-- The actual quotient algebra `R[T]/(T^n - 1)`. -/
abbrev RootAlgebra (n : ℕ) := AdjoinRoot (rootPolynomial R n)
theorem rootPolynomial_monic (n : ℕ) (hn : 0 < n) : (rootPolynomial R n).Monic :=
  monic_X_pow_sub_one hn.ne'
instance rootAlgebra_finite (n : ℕ) [NeZero n] : Module.Finite R (RootAlgebra R n) :=
  (rootPolynomial_monic R n (Nat.pos_of_ne_zero (NeZero.ne n))).finite_adjoinRoot

/-- An explicit standard-étale presentation when n is invertible. -/
def standardPair (n : ℕ) (hn : 0 < n) (hunit : IsUnit (n : R)) : StandardEtalePair R where
  f := rootPolynomial R n
  monic_f := rootPolynomial_monic R n hn
  g := 1
  cond := by
    obtain ⟨a, ha⟩ := hunit
    refine ⟨C (↑(a⁻¹) : R) * X, -1, 0, ?_⟩
    rcases n with _ | m
    · omega
    have ha' : (m + 1 : R) * (↑(a⁻¹) : R) = 1 := by
      simpa only [ha, Nat.cast_add, Nat.cast_one] using a.mul_inv
    simp only [rootPolynomial, derivative_sub, derivative_X_pow_succ, derivative_one,
      sub_zero, pow_zero]
    calc
      C (m + 1 : R) * X ^ m * (C (↑(a⁻¹) : R) * X) + (X ^ (m + 1) - 1) * -1 =
          C ((m + 1 : R) * (↑(a⁻¹) : R)) * X ^ (m + 1) - (X ^ (m + 1) - 1) := by
        rw [map_mul, pow_succ]
        ring
      _ = 1 := by rw [ha', map_one]; ring

/-- Localization at 1 adds nothing: the standard-étale algebra is the root quotient. -/
def standardPairEquiv (n : ℕ) (hn : 0 < n) (hunit : IsUnit (n : R)) :
    (standardPair R n hn hunit).Ring ≃ₐ[R] RootAlgebra R n := by
  let P := standardPair R n hn hunit
  change P.Ring ≃ₐ[R] AdjoinRoot P.f
  have hP : P.HasMap (AdjoinRoot.root P.f) :=
    ⟨AdjoinRoot.eval₂_root P.f, by simp [P, standardPair]⟩
  refine AlgEquiv.ofAlgHom
    (P.lift (AdjoinRoot.root P.f) hP)
    (AdjoinRoot.liftAlgHom P.f (Algebra.ofId R P.Ring) P.X P.hasMap_X.1) ?_ ?_
  · apply AdjoinRoot.algHom_ext
    change P.lift _ hP ((AdjoinRoot.liftAlgHom P.f (Algebra.ofId R P.Ring)
      P.X P.hasMap_X.1) (AdjoinRoot.root P.f)) = AdjoinRoot.root P.f
    rw [AdjoinRoot.liftAlgHom_root, P.lift_X]
  · apply P.hom_ext
    change (AdjoinRoot.liftAlgHom P.f (Algebra.ofId R P.Ring) P.X P.hasMap_X.1)
      (P.lift _ hP P.X) = P.X
    rw [P.lift_X, AdjoinRoot.liftAlgHom_root]

theorem rootAlgebra_etale (n : ℕ) (hn : 0 < n) (hunit : IsUnit (n : R)) :
    Algebra.Etale R (RootAlgebra R n) :=
  Algebra.Etale.of_equiv (standardPairEquiv R n hn hunit)


theorem root_pow (n : ℕ) : (AdjoinRoot.root (rootPolynomial R n)) ^ n = 1 := by
  have h := AdjoinRoot.eval₂_root (rootPolynomial R n)
  simpa [rootPolynomial, sub_eq_zero] using h

variable {R} in
/-- The quotient's ring maps with prescribed constants are precisely roots of unity. -/
def rootRingHomEquiv (S : Type u) [CommRing S] (i : R →+* S) (n : ℕ) [NeZero n] :
    {f : RootAlgebra R n →+* S // f.comp (algebraMap R _) = i} ≃ rootsOfUnity n S where
  toFun f := rootsOfUnity.mkOfPowEq (f.val (AdjoinRoot.root (rootPolynomial R n)))
    (by rw [← map_pow, root_pow, map_one])
  invFun a := ⟨AdjoinRoot.lift i (a.val : S) (by
      simpa [rootPolynomial, sub_eq_zero] using (mem_rootsOfUnity' n a.val).mp a.property),
    AdjoinRoot.lift_comp_of _⟩
  left_inv f := by
    apply Subtype.ext
    apply AdjoinRoot.ringHom_ext
    · dsimp
      rw [AdjoinRoot.lift_comp_of]
      exact f.property.symm
    · simp
  right_inv a := by
    apply rootsOfUnity.coe_injective
    simp

variable {R}

def schemeHomRingEquiv (U : Scheme.{u}) (A : Type u) [CommRing A] :
    (U ⟶ Spec (.of A)) ≃ (A →+* Γ(U, ⊤)) :=
  ((ΓSpec.adjunction.homEquiv U (op (.of A))).symm.trans
    (MultiplicativeGroup.opRingHomEquiv (.of A) Γ(U, ⊤)))

theorem schemeHomRingEquiv_comp {U V : Scheme.{u}} (A : Type u) [CommRing A]
    (f : U ⟶ V) (g : V ⟶ Spec (.of A)) :
    schemeHomRingEquiv U A (f ≫ g) = f.appTop.hom.comp (schemeHomRingEquiv V A g) := by
  change (((ΓSpec.adjunction.homEquiv U (op (.of A))).symm (f ≫ g)).unop.hom) = _
  rw [Adjunction.homEquiv_naturality_left_symm]
  rfl

theorem schemeHomRingEquiv_spec {U : Scheme.{u}} {A B : Type u} [CommRing A] [CommRing B]
    (g : U ⟶ Spec (.of B)) (i : A →+* B) :
    schemeHomRingEquiv U A (g ≫ Spec.map (CommRingCat.ofHom i)) =
      (schemeHomRingEquiv U B g).comp i := by
  change (((ΓSpec.adjunction.homEquiv U (op (.of A))).symm
    (g ≫ Scheme.Spec.map (CommRingCat.ofHom i).op)).unop.hom) = _
  rw [Adjunction.homEquiv_naturality_right_symm]
  rfl

theorem schemeHomRingEquiv_toSpecΓ (U : Scheme.{u}) :
    schemeHomRingEquiv U Γ(U, ⊤) U.toSpecΓ = RingHom.id _ := by
  change ((Scheme.ΓSpecIso Γ(U, ⊤)).inv ≫ U.toSpecΓ.appTop).hom = _
  rw [Scheme.toSpecΓ_appTop, Iso.inv_hom_id]
  rfl

/-- The explicit polynomial family, obtained by base change from global sections. -/
def polynomialScheme (X : Scheme.{u}) (n : ℕ) : Over X :=
  Over.mk (pullback.fst X.toSpecΓ
    (Spec.map (CommRingCat.ofHom (algebraMap Γ(X, ⊤) (RootAlgebra Γ(X, ⊤) n)))))

def polynomialHomEquiv (X : Scheme.{u}) (n : ℕ) (U : Over X) :
    (U ⟶ polynomialScheme X n) ≃
      {g : U.left ⟶ Spec (.of (RootAlgebra Γ(X, ⊤) n)) //
        g ≫ Spec.map (CommRingCat.ofHom (algebraMap Γ(X, ⊤) _)) = U.hom ≫ X.toSpecΓ} where
  toFun f := ⟨f.left ≫ pullback.snd _ _, by
    rw [Category.assoc, ← pullback.condition, ← Category.assoc]
    exact congrArg (fun k => k ≫ X.toSpecΓ) f.w⟩
  invFun g := Over.homMk (pullback.lift U.hom g.val g.property.symm) (by simp [polynomialScheme])
  left_inv f := by
    apply Over.OverMorphism.ext
    apply pullback.hom_ext
    · simpa [polynomialScheme] using f.w.symm
    · simp
  right_inv g := by apply Subtype.ext; simp

def polynomialHomRingEquiv (X : Scheme.{u}) (n : ℕ) (U : Over X) :
    (U ⟶ polynomialScheme X n) ≃
      {f : RootAlgebra Γ(X, ⊤) n →+* Γ(U.left, ⊤) //
        f.comp (algebraMap Γ(X, ⊤) _) = U.hom.appTop.hom} :=
  (polynomialHomEquiv X n U).trans
    ((schemeHomRingEquiv U.left (RootAlgebra Γ(X, ⊤) n)).subtypeEquiv (fun g => by
      rw [← (schemeHomRingEquiv U.left Γ(X, ⊤)).injective.eq_iff,
        schemeHomRingEquiv_spec, schemeHomRingEquiv_comp, schemeHomRingEquiv_toSpecΓ,
        RingHom.comp_id]))

def polynomialHomRootsEquiv (X : Scheme.{u}) (n : ℕ) [NeZero n] (U : Over X) :
    (U ⟶ polynomialScheme X n) ≃ rootsOfUnity n Γ(U.left, ⊤) :=
  (polynomialHomRingEquiv X n U).trans (rootRingHomEquiv _ U.hom.appTop.hom n)

theorem polynomialHomRootsEquiv_val (X : Scheme.{u}) (n : ℕ) [NeZero n] (U : Over X)
    (f : U ⟶ polynomialScheme X n) :
    ((polynomialHomRootsEquiv X n U f).val : Γ(U.left, ⊤)) =
      schemeHomRingEquiv U.left (RootAlgebra Γ(X, ⊤) n)
        (f.left ≫ pullback.snd _ _) (AdjoinRoot.root (rootPolynomial Γ(X, ⊤) n)) := by
  rfl

/-- The explicit polynomial family represents the same roots functor on every test scheme. -/
def polynomialRepresentable (X : Scheme.{u}) (n : ℕ) [NeZero n] :
    (MultiplicativeGroup.rootsFunctor X n ⋙ CategoryTheory.forget _).RepresentableBy
      (polynomialScheme X n) where
  homEquiv := polynomialHomRootsEquiv X n _
  homEquiv_comp f g := by
    apply rootsOfUnity.coe_injective
    change ((polynomialHomRootsEquiv X n _ (f ≫ g)).val : Γ(_, ⊤)) =
      f.left.appTop.hom ((polynomialHomRootsEquiv X n _ g).val : Γ(_, ⊤))
    rw [polynomialHomRootsEquiv_val]
    change schemeHomRingEquiv _ _ ((f.left ≫ g.left) ≫ pullback.snd _ _) _ =
      f.left.appTop.hom ((polynomialHomRootsEquiv X n _ g).val : Γ(_, ⊤))
    rw [polynomialHomRootsEquiv_val, Category.assoc, schemeHomRingEquiv_comp]
    rfl

/-- Polynomial realization of the already constructed equalizer, over the original base. -/
def rootsPolynomialIso (X : Scheme.{u}) (n : ℕ) [NeZero n] :
    MultiplicativeGroup.rootsScheme X n ≅ polynomialScheme X n :=
  (MultiplicativeGroup.rootsRepresentable X n).uniqueUpToIso (polynomialRepresentable X n)

instance polynomialScheme_finite (X : Scheme.{u}) (n : ℕ) [NeZero n] :
    IsFinite (polynomialScheme X n).hom := by
  have : IsFinite (Spec.map (CommRingCat.ofHom
      (algebraMap Γ(X, ⊤) (RootAlgebra Γ(X, ⊤) n)))) := by
    rw [IsFinite.SpecMap_iff]
    change (algebraMap Γ(X, ⊤) (RootAlgebra Γ(X, ⊤) n)).Finite
    rw [RingHom.finite_algebraMap]
    infer_instance
  exact inferInstanceAs (IsFinite (pullback.fst _ _))

theorem polynomialScheme_etale (X : Scheme.{u}) (n : ℕ) (hn : 0 < n)
    (hunit : IsUnit (n : Γ(X, ⊤))) : Etale (polynomialScheme X n).hom := by
  have : Algebra.Etale Γ(X, ⊤) (RootAlgebra Γ(X, ⊤) n) := rootAlgebra_etale _ n hn hunit
  have : Etale (Spec.map (CommRingCat.ofHom
      (algebraMap Γ(X, ⊤) (RootAlgebra Γ(X, ⊤) n)))) := by
    rw [HasRingHomProperty.Spec_iff (P := @Etale)]
    change (algebraMap Γ(X, ⊤) (RootAlgebra Γ(X, ⊤) n)).Etale
    rw [RingHom.etale_algebraMap]
    infer_instance
  exact inferInstanceAs (Etale (pullback.fst _ _))

/-- The actual power-map kernel is finite at every positive level. -/
theorem rootsScheme_finite (X : Scheme.{u}) (n : ℕ) (hn : 0 < n) :
    IsFinite (MultiplicativeGroup.rootsScheme X n).hom := by
  let : NeZero n := ⟨hn.ne'⟩
  let e := rootsPolynomialIso X n
  have : IsIso e.hom.left := (Over.forget X).map_isIso e.hom
  rw [← e.hom.w]
  infer_instance

/-- The actual power-map kernel is étale when its positive level is invertible. -/
theorem rootsScheme_etale (X : Scheme.{u}) (n : ℕ) (hn : 0 < n)
    (hunit : IsUnit (n : Γ(X, ⊤))) : Etale (MultiplicativeGroup.rootsScheme X n).hom := by
  let : NeZero n := ⟨hn.ne'⟩
  let e := rootsPolynomialIso X n
  have : IsIso e.hom.left := (Over.forget X).map_isIso e.hom
  have : Etale (polynomialScheme X n).hom := polynomialScheme_etale X n hn hunit
  rw [← e.hom.w]
  infer_instance

end AlgebraicGeometry.Scheme.Group.RootsFiniteEtale
