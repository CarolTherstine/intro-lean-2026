# WORDNET — Semantic Lexical Network

> **References**
> - [Kementzey BSc Thesis](https://lean-forward.github.io/pubs/kementzey_bsc_thesis)
> - [Mathlib4 — SimpleGraph](https://github.com/leanprover-community/mathlib4/tree/fbe77601aba49915466829996621694648a19266/Mathlib/Combinatorics/SimpleGraph)

---

## Overview

WordNet is a **directed acyclic graph (DAG)** organized into groups by **Part-Of-Speech (POS)**. The relations treated here are the **"is-a"** relations:

1. **Hyponymy** — `Penguin` is a hyponym of `Bird` (more specific).
2. **Hypernymy** — `Bird` is a hypernym of `Penguin` (more general).

```
                         {entity}
                            ▲
                            │ hypernymy
                         {animal}
                            ▲
                            │
                        {vertebrate}
                            ▲
                            │
                          {bird}
                        ▲        ▲
           hypernymy    │        │  hypernymy
                       │        │
                  {penguin}   {eagle}
```

Relations hold between **Synsets** — sets of conceptual synonyms.

---

## Formal Properties (Theorems)

Let `S` be the set of synsets and `→` the hypernym/hyponym relation.

### Theorem 1 — Irreflexivity (hypo/hyper)

```
∀ i ∈ S, ¬ (i → i)
```

### Theorem 2 — Transitivity (hypo/hyper)

```
∀ i, j, k ∈ S, (i → j) ∧ (j → k) → (i → k)
```

### Theorem 3 — Asymmetry (hypo/hyper)

```
∀ i, j ∈ S, (i → j) → ¬ (j → i)
```

### Theorem 4 — Unique Root

Define the reflexive-transitive closure `→*`:

```
(i →* j)  iff  i = j  or  there exists n ≥ 1 and elements c₀, c₁, …, cₙ such that
              c₀ = i,  cₙ = j,  and  cₖ → cₖ₊₁  for every k < n.
```

A root is an element that reaches every synset:

```
Root(r)  :=  ∀ a ∈ S, r →* a
```

There exists a unique root:

```
∃! r ∈ S, Root(r)
```

i.e.:

```
∃ (r) (∀ (a) (r →* a)) ∧ ∀ (r') (∀ (a) (r' →* a)) → (r' = r)
```

### Theorem 5 — Inheritance Monotonicity

```
∀ (a, b, p) (a →* b) → inh(a, p) → inh(b, p)
```

Equivalently, unfolding `inh`:

```
∀ (a, b, c, p) (a →* b) → (c →* a) → has(c, p) → inh(b, p)
```
