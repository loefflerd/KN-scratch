import Theorems.MTT.Thm_MTT_Cohomology_cuspPrimitive_analytic_relations
import Definitions.MTT.Def_MTT_Cohomology_Integration
import Mathlib.RingTheory.Flat.Basic
set_option autoImplicit false
noncomputable section
open scoped BigOperators TensorProduct
open MTT.Cohomology

namespace MTT.Cohomology

lemma cuspPeriodPolynomial_mem_Sym {N k : ℕ} (hk : 2 ≤ k) (f : CuspForm (MTT.GammaOne N) (k : ℤ))
    (r : ℚ) : cuspPeriodPolynomial f r ∈ Sym ℂ (k - 2) := by
  unfold cuspPeriodPolynomial
  refine Submodule.sum_mem _ fun j hj => ?_
  rw [MvPolynomial.mem_homogeneousSubmodule]
  apply MvPolynomial.isHomogeneous_monomial
  rw [Finsupp.degree_eq_sum, Fin.sum_univ_two]
  have := Finset.mem_range.mp hj
  simp [binaryExponent]
  omega

lemma cuspPrimitive_mem_Sym {N k : ℕ} (hk : 2 ≤ k) (f : CuspForm (MTT.GammaOne N) (k : ℤ))
    (x : Cusp) : cuspPrimitive f x ∈ Sym ℂ (k - 2) := by
  rcases x with _ | r
  · exact Submodule.zero_mem _
  · exact cuspPeriodPolynomial_mem_Sym hk f r

end MTT.Cohomology

theorem solution
    {N k : ℕ} (hN : 0 < N) (hk : 2 ≤ k) :
    ∃ I : CuspForm (MTT.GammaOne N) (k : ℤ) →ₗ[ℂ] Hc N (k-2) ℂ,
      ∀ f, (I f).val = integrationCochain f := by
  obtain ⟨hequiv, hadd, hsmul⟩ := MTT.Cohomology.cuspPrimitive_analytic_relations hN hk
  have hmem : ∀ f : CuspForm (MTT.GammaOne N) (k : ℤ),
      integrationCochain f ∈ compactSupport (CongruenceSubgroup.Gamma1 N) (k - 2) ℂ := by
    intro f
    refine ⟨?_, ?_, ?_⟩
    · intro x y
      exact Submodule.sub_mem _ (cuspPrimitive_mem_Sym hk f y) (cuspPrimitive_mem_Sym hk f x)
    · intro x y z
      simp only [integrationCochain]
      abel
    · intro γ x y
      simp only [integrationCochain]
      rw [hequiv f γ y, hequiv f γ x, map_sub]
      abel
  refine ⟨{ toFun := fun f => ⟨integrationCochain f, hmem f⟩
            map_add' := ?_
            map_smul' := ?_ }, fun f => rfl⟩
  · intro f g
    apply Subtype.ext
    funext D
    simp only [integrationCochain, Submodule.coe_add, Pi.add_apply, hadd]
    abel
  · intro c f
    apply Subtype.ext
    funext D
    simp only [integrationCochain, Submodule.coe_smul, Pi.smul_apply, hsmul, smul_sub,
      RingHom.id_apply]
