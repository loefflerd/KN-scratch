import Definitions.MTT.Def_MTT_Measures

noncomputable section
open scoped BigOperators

theorem MTT.periods_exist
    {N k : ℕ} (hN : 0 < N) (hk : 2 ≤ k)
    (ι : MTT.Qbar →+* ℂ) (f : MTT.Eigenform N k ι) :
    Nonempty (MTT.Periods k ι f.form) := by sorry
