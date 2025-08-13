import Mathlib.Tactic.Push

namespace Yablo

/-- Predicate `Y(n)` is yablo-paradoxial predicate -/
def yabloian (Y : ℕ → Prop) := ∀ n, Y n ↔ ∀ m > n, ¬Y m

/-- There is no yabloian predicate. -/
theorem not_exists_yabloian_predicate : ¬∃ Y, yabloian Y := by
  rintro ⟨Y, hY⟩;
  by_cases h : ∃ n, Y n;
  . obtain ⟨n, hn⟩ := h;
    have := hY n |>.mp hn (n + 1) (by omega);
    have := hY (n + 1) |>.not.mp this;
    push_neg at this;
    obtain ⟨m, _, _⟩ := this;
    apply hY n |>.mp hn m (by omega);
    assumption;
  . push_neg at h;
    have := hY 0 |>.not.mp (h 0);
    push_neg at this;
    obtain ⟨m, _, _⟩ := this;
    apply h m;
    assumption;

end Yablo
