module

public import Definitions.FLT.Def_EllipticCurve_TateModule
public import Definitions.FLT.Def_P2M_Util

section privateSection

namespace P2MW.S_TateModule_exists_linearMap_apply_eq_of_addMonoidHom

set_option autoImplicit false

theorem solution
    (p : ℕ) [Fact p.Prime] {M M' : Type} [AddCommGroup M] [AddCommGroup M'] (f : M →+ M') :
    ∃ e : TateModule p M →ₗ[ℤ_[p]] TateModule p M',
      (∀ (x : TateModule p M) (n : ℕ), ((e x : TateModule p M') : ℕ → M') n = f ((x : ℕ → M) n)) ∧
      (Function.Injective f → Function.Injective e) := by
  refine ⟨{ toFun := fun x => ⟨fun n => f ((x : ℕ → M) n), fun n => ⟨?_, ?_⟩⟩, map_add' := ?_, map_smul' := ?_ },
    ?_, ?_⟩
  · rw [← map_zsmul, TateModule.torsion, map_zero]
  · rw [← map_zsmul, TateModule.compat]
  · intro x y
    exact Subtype.ext (funext fun n => by
      show f (((x + y : TateModule p M) : ℕ → M) n) = f ((x : ℕ → M) n) + f ((y : ℕ → M) n)
      rw [AddSubgroup.coe_add, Pi.add_apply, map_add])
  · intro a x
    exact Subtype.ext (funext fun n => by
      show f (((a • x : TateModule p M) : ℕ → M) n) = ((a.appr n : ℕ) : ℤ) • f ((x : ℕ → M) n)
      rw [TateModule.smul_apply, map_zsmul])
  · intro x n
    rfl
  · intro hf x y hxy
    refine Subtype.ext (funext fun n => hf ?_)
    have := congrArg (fun z : TateModule p M' => (z : ℕ → M') n) hxy
    exact this
end S_TateModule_exists_linearMap_apply_eq_of_addMonoidHom
end P2MW

end privateSection

public section publicSection

set_option autoImplicit false

theorem TateModule.exists_linearMap_apply_eq_of_addMonoidHom
    (p : ℕ) [Fact p.Prime] {M M' : Type} [AddCommGroup M] [AddCommGroup M'] (f : M →+ M') :
    ∃ e : TateModule p M →ₗ[ℤ_[p]] TateModule p M',
      (∀ (x : TateModule p M) (n : ℕ), ((e x : TateModule p M') : ℕ → M') n = f ((x : ℕ → M) n)) ∧
      (Function.Injective f → Function.Injective e) := _root_.P2MW.S_TateModule_exists_linearMap_apply_eq_of_addMonoidHom.solution p f

end publicSection
