import Mathlib.Tactic.Push
import Mathlib.Tactic.ByContra
import Mathlib.Tactic.Use

namespace Yablo

/-- Predicate `Y(n)` is yablo-paradoxial predicate -/
def yabloian (Y : ℕ → Prop) := ∀ n, Y n ↔ ∀ m > n, ¬Y m

/-- There is no yabloian predicate. -/
theorem not_exists_yabloian_predicate : ¬∃ Y, yabloian Y := by
  rintro ⟨Y, hY⟩;
  have h₁ : ∀ n, ¬Y n := by
    by_contra! hC;
    obtain ⟨n, hn⟩ := hC;
    apply hY n |>.mp hn (n + 1) (by omega);
    apply hY _ |>.mpr;
    intro m hm;
    apply hY n |>.mp hn;
    omega;
  obtain ⟨m, _, _⟩ : ∃ x, 0 < x ∧ Y x := by
    simpa using hY 0 |>.not.mp $ h₁ 0;
  apply h₁ m;
  assumption;

end Yablo
