/-
Copyright (c) 2026 kangxyz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.EtaleCohomology.ArtinSchreier.Complex
public import Aglib.AlgebraicGeometry.EtaleCohomology.ArtinSchreier.KernelCover
public import Mathlib.Algebra.Homology.ShortComplex.ShortExact

/-!
# The actual Artin--Schreier short exact sequence

The native kernel's sections are locally original prime-field constants on
the canonical basic-open partition. This proves exactness for the actual
constant-prime-field inclusion and literal power-minus-identity map, with no
Noetherian or nonempty hypothesis.
-/

@[expose] public noncomputable section

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open CategoryTheory CategoryTheory.Limits Opposite

namespace AlgebraicGeometry.Scheme.EtaleCohomology

universe u

/-- Every actual native-kernel section is locally an original prime-field constant. -/
theorem primeFieldToArtinSchreierKernel_isLocallySurjective (X : Scheme.{u})
    (p : ℕ) (hp : p.Prime) (hX : (p : Γ(X, ⊤)) = 0) :
    Presheaf.IsLocallySurjective (Scheme.smallEtaleTopology X)
      (primeFieldToArtinSchreierKernel X p hp hX).hom := by
  let : Fact p.Prime := ⟨hp⟩
  constructor
  intro U s
  let b : Γ(U.left, ⊤) := artinSchreierKernelSection X p hp hX (op U) s
  have hb : b ^ p - b = 0 := artinSchreierKernelSection_equation X p hp hX (op U) s
  have hU : (p : Γ(U.left, ⊤)) = 0 := primeCast_eq_zero_on_test X p hX (op U)
  let O : ZMod p → U.left.Opens := Scheme.ArtinSchreier.rootOpen p hU b hb
  let V : ZMod p → X.Etale := fun i => Scheme.Etale.mk ((O i).ι ≫ U.hom)
  let q : ∀ i, V i ⟶ U := fun i => MorphismProperty.Over.homMk (O i).ι rfl
  have hc : Sieve.ofArrows V q ∈ Scheme.smallEtaleTopology X U := by
    rw [Scheme.ofArrows_mem_smallEtaleTopology_iff]
    ext x
    simp only [Set.mem_iUnion, Set.mem_range, Set.mem_univ, iff_true]
    obtain ⟨i, hi⟩ := Scheme.ArtinSchreier.exists_mem_rootOpen p hU b hb x
    exact ⟨i, ⟨⟨x, hi⟩, rfl⟩⟩
  apply (Scheme.smallEtaleTopology X).superset_covering ?_ hc
  rw [Sieve.ofArrows, Sieve.generate_le_iff, Presieve.ofArrows_le_iff]
  intro i
  let c : (primeFieldSheaf X p).obj.obj (op (V i)) :=
    (toSheafify (Scheme.smallEtaleTopology X)
      ((Functor.const X.Etaleᵒᵖ).obj (primeFieldCoefficient p))).app
        (op (V i)) (ULift.up i)
  refine ⟨c, ?_⟩
  have hi : Function.Injective
      ((kernel.ι (artinSchreierMap X p hp hX)).hom.app (op (V i))) := by
    exact (AddCommGrpCat.mono_iff_injective _).mp inferInstance
  apply hi
  have hlift := congrArg
    (fun t : primeFieldSheaf X p ⟶ additiveStructureSheaf X =>
      t.hom.app (op (V i)) c)
    (primeFieldToArtinSchreierKernel_ι X p hp hX)
  change (kernel.ι (artinSchreierMap X p hp hX)).hom.app (op (V i))
      ((primeFieldToArtinSchreierKernel X p hp hX).hom.app (op (V i)) c) =
    (primeFieldToStructure X p hX).hom.app (op (V i)) c at hlift
  rw [hlift]
  have hconstant := congrArg
    (fun t => t.app (op (V i)) (ULift.up i))
    (toSheafify_primeFieldToStructure X p hX)
  change (primeFieldToStructure X p hX).hom.app (op (V i)) c =
    (primeFieldPresheafMap X p hX).app (op (V i)) (ULift.up i) at hconstant
  rw [hconstant]
  have hn := ConcreteCategory.congr_hom
    ((kernel.ι (artinSchreierMap X p hp hX)).hom.naturality (q i).op) s
  change (kernel.ι (artinSchreierMap X p hp hX)).hom.app (op (V i))
      ((kernel (artinSchreierMap X p hp hX)).obj.map (q i).op s) =
    (additiveStructurePresheaf X).map (q i).op
      ((kernel.ι (artinSchreierMap X p hp hX)).hom.app (op U) s) at hn
  rw [hn]
  apply ULift.ext
  change Algebra.ArtinSchreier.residueScalarHom p
      (primeCast_eq_zero_on_test X p hX (op (V i))) i = (O i).ι.appTop.hom b
  rw [Algebra.ArtinSchreier.residueScalarHom_apply]
  exact (Scheme.ArtinSchreier.rootOpen_appTop_root p hU b hb i).symm

/-- The actual map onto the native AS kernel is an epimorphism of abelian sheaves. -/
theorem primeFieldToArtinSchreierKernel_epi (X : Scheme.{u}) (p : ℕ) (hp : p.Prime)
    (hX : (p : Γ(X, ⊤)) = 0) : Epi (primeFieldToArtinSchreierKernel X p hp hX) := by
  let := primeFieldToArtinSchreierKernel_isLocallySurjective X p hp hX
  exact inferInstance

/-- The original constant prime-field sheaf is the native kernel of the original AS map. -/
def primeFieldArtinSchreierKernelIso (X : Scheme.{u}) (p : ℕ) (hp : p.Prime)
    (hX : (p : Γ(X, ⊤)) = 0) :
    primeFieldSheaf X p ≅ kernel (artinSchreierMap X p hp hX) := by
  let := primeFieldToArtinSchreierKernel_mono X p hp hX
  let := primeFieldToArtinSchreierKernel_epi X p hp hX
  have := isIso_of_mono_of_epi (primeFieldToArtinSchreierKernel X p hp hX)
  exact asIso (primeFieldToArtinSchreierKernel X p hp hX)

/-- The kernel isomorphism uses the literal factor of the original coefficient inclusion. -/
theorem primeFieldArtinSchreierKernelIso_hom (X : Scheme.{u}) (p : ℕ) (hp : p.Prime)
    (hX : (p : Γ(X, ⊤)) = 0) :
    (primeFieldArtinSchreierKernelIso X p hp hX).hom =
      primeFieldToArtinSchreierKernel X p hp hX := rfl

/-- Exactness at the actual additive etale structure sheaf. -/
theorem artinSchreierComplex_exact (X : Scheme.{u}) (p : ℕ) (hp : p.Prime)
    (hX : (p : Γ(X, ⊤)) = 0) : (artinSchreierComplex X p hp hX).Exact := by
  rw [ShortComplex.exact_iff_epi_kernel_lift]
  exact primeFieldToArtinSchreierKernel_epi X p hp hX

/-- The original prime-field inclusion and AS map form a short exact sequence. -/
theorem artinSchreierComplex_shortExact (X : Scheme.{u}) (p : ℕ) (hp : p.Prime)
    (hX : (p : Γ(X, ⊤)) = 0) : (artinSchreierComplex X p hp hX).ShortExact := by
  exact ShortComplex.ShortExact.mk' (artinSchreierComplex_exact X p hp hX)
    (primeFieldToStructure_mono X p hp hX) (artinSchreierMap_epi X p hp hX)

end AlgebraicGeometry.Scheme.EtaleCohomology
