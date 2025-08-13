# Yablo's paradox in Lean 4

Tiny proof (26 lines) of "there is no Yablo-paradoxical predicate in Lean 4".

```lean
def yabloian (Y : ℕ → Prop) := ∀ n, Y n ↔ ∀ m > n, ¬Y m

theorem not_exists_yabloian_predicate : ¬∃ Y, yabloian Y
```
