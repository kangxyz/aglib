/-
Copyright (c) 2026 kangxyz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/

module

public import Aglib.AlgebraicGeometry.Morphisms.FiniteEtale.Descent.AffineSheafAlgebraDatum
public import Aglib.RingTheory.Descent.Basic

/-! The local identity section is constant on the equivalence relation over
the constructed invariant algebra. -/

@[expose] public section

noncomputable section
set_option autoImplicit false
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open CategoryTheory AlgebraicGeometry TensorProduct
open AlgebraicGeometry.Scheme.FiniteEtale

namespace AlgebraicGeometry.Scheme.FiniteEtale.SheafDescent.AffineSheafAlgebraDatum

universe u
variable {R S : Type u} [CommRing R] [CommRing S] [Algebra R S] [Algebra.Etale R S]
variable [Module.Flat R S]
variable (F : Scheme.EtaleCohomology.SetSheaf (Spec (.of R))) (B : Type u)
variable [CommRing B] [Algebra R B] [Algebra S B] [IsScalarTower R S B]
variable [Module.Finite S B] [Algebra.Etale S B]
variable (e : Scheme.EtaleCohomology.finiteRepresentedSetSheaf (AffineDescent.specCover S B) ≅
  (Scheme.EtaleCohomology.setEtaleRestriction (chart R S)).obj F)

local instance etaleTensor' : Algebra.Etale S (S ⊗[R] B) := by
  have : Algebra.Etale R B := Algebra.Etale.comp R S B
  infer_instance

/-- If two affine test maps agree on the literal invariant algebra, the local
identity section has the same pullback along both. -/
theorem identitySection_invariant {C : Type u} [CommRing C]
    [Algebra R C] [Algebra S C] [IsScalarTower R S C] [Algebra.Etale S C]
    (φ : B →ₐ[R] C) (ψ : B →ₐ[S] C)
    (h : ∀ a : (datum F B e).invariants, φ a = ψ a) :
    map (S := S) F φ (identitySection F B e) =
      map (S := S) F (ψ.restrictScalars R) (identitySection F B e) := by
  let D := datum F B e
  let l : S ⊗[R] B →ₐ[S] C := AlgHom.liftEquiv R S B C φ
  have hl : l.comp D.coaction = ψ := by
    ext b
    obtain ⟨z, rfl⟩ := D.baseChange_surjective b
    change l (D.coaction (D.baseChange z)) = ψ (D.baseChange z)
    rw [D.coaction_baseChange]
    induction z using TensorProduct.inductionOn with
    | tmul s a =>
      rw [_root_.Algebra.Descent.Datum.tensorInclusion_tmul,
        _root_.Algebra.Descent.Datum.baseChange_tmul, map_smul]
      change s • φ a = s • ψ a
      rw [h a]
    | add x y hx hy => simp only [map_add, hx, hy]
  have hδ : map (S := S) F (D.coaction.restrictScalars R) (identitySection F B e) =
      map (S := S) F (Algebra.TensorProduct.includeRight : B →ₐ[R] S ⊗[R] B)
        (identitySection F B e) :=
    (representationEquiv_eq F B e (coaction F B e)).symm.trans
      (representationEquiv_coaction F B e)
  have hlη : (l.restrictScalars R).comp
      (Algebra.TensorProduct.includeRight : B →ₐ[R] S ⊗[R] B) = φ := by
    ext b
    simp [l]
  calc
    map (S := S) F φ (identitySection F B e) =
        map (S := S) F (l.restrictScalars R)
          (map (S := S) F (Algebra.TensorProduct.includeRight : B →ₐ[R] S ⊗[R] B)
            (identitySection F B e)) := by rw [← map_comp, hlη]
    _ = map (S := S) F (l.restrictScalars R)
        (map (S := S) F (D.coaction.restrictScalars R) (identitySection F B e)) := by rw [hδ]
    _ = map (S := S) F (ψ.restrictScalars R) (identitySection F B e) := by
      rw [← map_comp]
      change map (S := S) F ((l.comp D.coaction).restrictScalars R) _ = _
      rw [hl]

end AlgebraicGeometry.Scheme.FiniteEtale.SheafDescent.AffineSheafAlgebraDatum

/- Migration source: the R5Lab/Aglib mirror; exact module in the migration record.
R5 revision c82abf3a72ce1e1cedf4a4f1fe08bea994ad4df5.
SHA256 af6f50f5f7605940e88882076037e2dcf9efeb32b16f440866979282ce40eab3.
Definitions, hypotheses and universes are retained modulo native names. -/
