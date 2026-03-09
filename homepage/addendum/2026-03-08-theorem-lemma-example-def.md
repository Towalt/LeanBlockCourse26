---
title: "theorem vs lemma"
parent: Addendum
nav_order: 2
---

# `theorem`, `lemma`, `example`, and `def`
{: .no_toc }

*March 8, 2026 · `P02–P03`*

---

In the course files you will encounter four declaration keywords: `def`, `theorem`, `lemma`, and `example`. Lean treats some of these identically, but they signal different intent.

## `def` vs `theorem`

Both introduce a named declaration, but they differ in **transparency**:

- **`def`** creates a *transparent* definition. The body can be unfolded by `simp`, `dsimp`, `rfl`, and the kernel. Use this for data and computable functions.
- **`theorem`** creates an *opaque* definition. The body is not unfolded. Use this for propositions and proofs.

Because of proof irrelevance (all proofs of the same proposition are definitionally equal), opacity does not matter for `Prop`-valued declarations — but the convention is still `theorem` for proofs and `def` for data.

```lean
def double (n : Nat) : Nat := 2 * n         -- transparent: simp can unfold
theorem double_pos (n : Nat) (h : 0 < n) : 0 < double n := by simp [double]
```

## `theorem` vs `lemma`

They are **synonyms**. Lean does not distinguish them at all:

```lean
theorem foo : True := trivial
lemma bar : True := trivial
-- These produce identical declarations.
```

Mathlib conventionally uses `lemma` for intermediate results and `theorem` for "named" results, but this is a social convention, not a language distinction. In this course we use `theorem` throughout.

## `example`

An `example` is an **unnamed theorem**. It type-checks and elaborates like a `theorem`, but no name is added to the environment. You cannot reference it later.

```lean
example (P : Prop) (p : P) : P := p   -- proves P → P, but gives it no name
```

We use `example` for exercises and one-off demonstrations. After proving a result as `example`, we point to its Mathlib equivalent via `#check` so you know the real name to use going forward.

## Summary

| Keyword | Named | Transparent | Use for |
|---------|:-----:|:-----------:|---------|
| `def` | yes | yes | Data, computable functions |
| `theorem` | yes | no | Proofs, propositions |
| `lemma` | yes | no | Synonym for `theorem` |
| `example` | no | no | Exercises, demonstrations |
