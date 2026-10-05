module

public import Definitions.FLT.Def_HahnSeries_RamificationBound

public section publicSection

theorem HahnSeries.HasRamBound.add {K : Type*} [Field K] {e : ℕ} {x y : HahnSeries ℚ K} (hx : HasRamBound e x)
    (hy : HasRamBound e y) : HasRamBound e (x + y) := by
  intro g hg
  rcases support_add_subset x y hg with h | h
  · exact hx h
  · exact hy h

end publicSection
