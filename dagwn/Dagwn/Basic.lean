--IS-A relationship
structure Edge where
  target_id : Nat
  relation_name : String

structure Vertex where
  id : Nat
  concept : String
  out_edges : List Edge

structure Graph where
  vertices : List Vertex

--================================================================
--                HELPER FUNCTIONS
--================================================================
def get_vertex (g : Graph) (id : Nat) :=
  g.vertices.find? (fun v => v.id == id)

def reaches (g : Graph) (length x y : Nat) : Bool :=
  match length with
  | 0 => x == y
  | length + 1 =>
    x == y ||
    (match get_vertex g x with
     | none   => false
     | some v => v.out_edges.any (fun e => reaches g length e.target_id y))
termination_by length

def has_edge_to (edges : List Edge) (target : Nat) : Bool :=
  edges.any (fun e => e.target_id == target)

def has_edge_to_in_g (g : Graph) (x : Nat) : Bool :=
  g.vertices.any (fun v => v.out_edges.any (fun e => e.target_id == x))

--inductive Walk : Vertex → Vertex → Type u
--  | nil {u : Vertex} : Walk u u
--  | cons {u v w : Vertex} (h :  u v) (p : Walk v w) : Walk u w
--  deriving DecidableEq
--
--def length {u v : V} : G.Walk u v → ℕ
--  | nil => 0
--  | cons _ q => q.length.succ
--
--def IsAcyclic : Prop := ∀ ⦃v : Vertex⦄ (c : G.Walk v v), ¬c.IsCycle

--================================================================
--                SPECIFIC FUNCTIONS
--================================================================
--lower/child
--is x a parent to y
--is y an hyponym of x
def DirectHyponym (g : Graph) (x y : Nat) : Bool :=
  match get_vertex g x with
  | none   => false
  | some v => has_edge_to v.out_edges y

--upper/parent
--is x a child to y
--is y an hypernym of x
def DirectHypernym (g : Graph) (x y : Nat) : Bool :=
  DirectHyponym g y x

def IndirectHyponym (g : Graph) (x y : Nat) : Bool :=
  match get_vertex g x, get_vertex g y with
  | some _, some _ => reaches g (g.vertices.length + 1) x y
  | _, _           => false

def IndirectHypernym (g : Graph) (x y : Nat) : Bool :=
  IndirectHyponym g y x

--================================================================
--                THEOREM FUNCTIONS
--================================================================
--guarantee that for all vertices in g none is the hypernym to itself
-- therefore no vertices points to itself

--Theorem 1 : Irreflexivity
-- ∀ x (¬ (x → x))
def Irreflexivity_bool (g : Graph) : Bool
  := g.vertices.all (fun x => !DirectHypernym g x.id x.id)

def Irreflexivity (g : Graph) : Prop :=
  ∀ x ∈ g.vertices, ¬ DirectHypernym g x.id x.id


theorem Irreflexivity_bool_iff (g : Graph) :
    Irreflexivity_bool g ↔ Irreflexivity g := by
  constructor
  · intro h x hx
    rw [Irreflexivity_bool, List.all_eq_true] at h
    simpa using h x hx
  · intro h
    rw [Irreflexivity_bool, List.all_eq_true]
    intro x hx
    simpa using h x hx

theorem Irreflexivity_bool_iff2 (g : Graph) :
    Irreflexivity_bool g ↔ Irreflexivity g := by
  rw [Irreflexivity_bool, List.all_eq_true]
  constructor
  · intro h x hx
    simpa using h x hx
  · intro h x hx
    simpa using h x hx

--Theorem 2 : Transitivity
-- ∀ (x, y , z ) (x → y ∧ y → z) → x indirect → z
def Transitivity_bool (g : Graph) : Bool :=
  g.vertices.all (fun x =>
    g.vertices.all (fun y =>
      g.vertices.all (fun z =>
          !(DirectHyponym g x.id y.id && DirectHyponym g y.id z.id) ||
          IndirectHyponym g x.id z.id)))

def Transitivity (g : Graph) : Prop :=
  ∀ x ∈ g.vertices, ∀ y ∈ g.vertices, ∀ z ∈ g.vertices,
    DirectHyponym g x.id y.id → DirectHyponym g y.id z.id  → IndirectHyponym g x.id z.id


theorem Transitivy_bool_iff (g : Graph) :
  Transitivity_bool g ↔ Transitivity g := by
  simp only [Transitivity_bool, List.all_eq_true]
  constructor
  · intro h x hx y hy z hz hxy hyz
    specialize h x hx

    by_cases h1 : DirectHyponym g x.id y.id
    · by_cases h2 : DirectHyponym g y.id z.id
      · simp [h1, h2] at h
        exact h
      · simp [h2] at h
    · simp [h1] at h
  · intro h x hx y hy z hz
    by_cases h1 : DirectHyponym g x.id y.id
    · by_cases h2 : DirectHyponym g y.id z.id
      · simp [h1, h2]
        exact h x hx y hy z hz h1 h2
      · simp [h2]
    · simp [h1]

--Theorem 2 : Transitivity
-- ∀ (x, y , z ) (x → y ∧ y → z) → x indirect → z


--Theorem 3 : Assymetry
--∀ (i, j) (i → j) → ¬ (j → i)
def Asymmetry_bool (g : Graph) : Bool :=
  g.vertices.all (fun x =>
    match get_vertex g x.id with
    | none => true
    | some v =>
      v.out_edges.all (fun y =>
        match get_vertex g y.target_id with
        | none => true
        | some _ => !IndirectHypernym g x.id y.target_id
      ))

def Asymmetry (g  : Graph) : Prop :=
  ∀ x ∈ g.vertices, ∀ y ∈ g.vertices, DirectHyponym g x.id y.id → ¬ DirectHyponym g y.id x.id

theorem Asymmetry_bool_iff (g : Graph) :
  Asymmetry_bool g ↔ Asymmetry g :=by
  constructor
  . intro h

--Theorem 4 : Unique Root
--Root(r)  :=  ∀ a ∈ S, r →* a
--∃! r ∈ S, Root(r)
def UniqueRoot_bool (g : Graph) (r : Nat) : Bool :=
  !has_edge_to_in_g g r &&
  g.vertices.all (fun v => IndirectHyponym g r v.id)

--exactly 1 unique
def HasOneUniqueRoot_bool (g : Graph) : Bool :=
  (g.vertices.filter (fun v => UniqueRoot_bool g v.id)).length == 1

--Guarantees that g has no cycle (i.e no vertice can reach itself)
def Acyclicity (g : Graph) : Bool :=
  g.vertices.all (fun x =>
      match get_vertex g x.id with
      | none => true
      | some v =>
          ¬ reaches g (g.vertices.length + 1) v.id v.id
  )

--def HasCycle (g : Graph) : Bool :=
--definir o q eh ciclo
--e provar q as propriedades provam q n tem ciclo

--================================================================
--                WORDNET SPECIFIC
--================================================================
structure SynsetGraph where
  g              : Graph
  irr            : Irreflexivity_bool g = true
  ass            : Asymmetry_bool g = true
  trsnt          : Transitivity_bool g = true
  universal_root : HasOneUniqueRoot_bool g = true

namespace SynsetGraph

theorem irreflexive (s : SynsetGraph) : Irreflexivity_bool s.g = true := s.irr
theorem asymmetric  (s : SynsetGraph) : Asymmetry_bool s.g = true := s.ass
theorem transitive  (s : SynsetGraph) : Transitivity_bool s.g = true := s.trsnt
theorem unique_root (s : SynsetGraph) : HasOneUniqueRoot_bool s.g = true := s.universal_root
theorem synset_cycle (s: SynsetGraph) : Acyclicity s.g = true := by
  have h1 := s.irr
  have h2 := s.ass
  have h3 := s.trsnt


theorem strict_partial_order_proves_acyclicity (s: SynsetGraph) : Acyclicity s.g = true := sorry

--parsing do arquivo wn em uma instancia de synset graph
--funcao q carrega e faz a translate do dto
--usar json



end SynsetGraph

--================================================================
--                SANITY CHECKS
--================================================================

-- ─── helper ──────────────────────────────────────────────────────
def check (g : Graph) : Bool :=
  Irreflexivity_bool g &&
  Asymmetry_bool g &&
  Transitivity_bool g &&
  HasOneUniqueRoot_bool g

--================================================================
--  GRAPHS: one per property, so each test isolates one failure
--================================================================

/-- Well-formed tree: animal → {dog, cat}. Passes every check. -/
def tree : Graph :=
  { vertices :=
    [ { id := 0, concept := "animal", out_edges :=
        [ { target_id := 1, relation_name := "is-a" }
        , { target_id := 2, relation_name := "is-a" } ] }
    , { id := 1, concept := "dog", out_edges := [] }
    , { id := 2, concept := "cat", out_edges := [] } ] }

/-- Self-loop 0 → 0: fails irreflexivity, asymmetry, unique-root. -/
def selfLoop : Graph :=
  { vertices :=
    [ { id := 0, concept := "a", out_edges := [{ target_id := 0, relation_name := "r" }] } ] }

/-- 2-cycle 0 ⇄ 1: fails asymmetry (and unique-root: no in-degree-0 vertex). -/
def twoCycle : Graph :=
  { vertices :=
    [ { id := 0, concept := "a", out_edges := [{ target_id := 1, relation_name := "r" }] }
    , { id := 1, concept := "b", out_edges := [{ target_id := 0, relation_name := "r" }] } ] }

/-- Two disjoint chains: fails unique-root (two in-degree-0 vertices: 0 and 2). -/
def forest2 : Graph :=
  { vertices :=
    [ { id := 0, concept := "a", out_edges := [{ target_id := 1, relation_name := "r" }] }
    , { id := 1, concept := "b", out_edges := [] }
    , { id := 2, concept := "c", out_edges := [{ target_id := 3, relation_name := "r" }] }
    , { id := 3, concept := "d", out_edges := [] } ] }

/-- Chain 0 → 1 → 2 with NO shortcut 0 → 2. Passes every check. -/
def goodChain : Graph :=
  { vertices :=
    [ { id := 0, concept := "a", out_edges := [{ target_id := 1, relation_name := "r" }] }
    , { id := 1, concept := "b", out_edges := [{ target_id := 2, relation_name := "r" }] }
    , { id := 2, concept := "c", out_edges := [] } ] }

/-- Chain 0 → 1 → 2 AND shortcut 0 → 2. Fails transitivity (shortcut present). -/
def hasShortcut : Graph :=
  { vertices :=
    [ { id := 0, concept := "a", out_edges :=
        [ { target_id := 1, relation_name := "r" }
        , { target_id := 2, relation_name := "r" } ] }
    , { id := 1, concept := "b", out_edges := [{ target_id := 2, relation_name := "r" }] }
    , { id := 2, concept := "c", out_edges := [] } ] }

--================================================================
--  PER-PROPERTY TESTS  (positive and negative case for each)
--================================================================

-- ─── Irreflexivity: no x → x ─────────────────────────────────────
#eval Irreflexivity_bool tree        -- true
#eval Irreflexivity_bool goodChain   -- true
#eval Irreflexivity_bool selfLoop    -- false  (0 → 0)

-- ─── Asymmetry: no x ⇝ y with y ⇝ x (for x ≠ y) ─────────────────
#eval Asymmetry_bool tree            -- true
#eval Asymmetry_bool goodChain       -- true
#eval Asymmetry_bool twoCycle        -- false  (0 ⇝ 1 and 1 ⇝ 0)
#eval Asymmetry_bool selfLoop        -- false  (0 ⇝ 0)

-- ─── Transitivity (= no shortcuts): x→y→z ⟹ NOT x→z ─────────────
#eval Transitivity_bool tree         -- true   (no 2-hop paths at all)
#eval Transitivity_bool goodChain    -- true   (0→1→2, and no 0→2)
#eval Transitivity_bool hasShortcut  -- false  (0→1→2 AND 0→2)
#eval Transitivity_bool twoCycle     -- true   (0→1→0 is a cycle, not a shortcut)

-- ─── Unique root: exactly one in-degree-0 vertex that reaches all ─
#eval HasOneUniqueRoot_bool tree     -- true   (root: animal)
#eval HasOneUniqueRoot_bool goodChain -- true  (root: 0)
#eval HasOneUniqueRoot_bool forest2  -- false  (two roots: 0 and 2)
#eval HasOneUniqueRoot_bool twoCycle -- false  (no in-degree-0 vertex)
#eval HasOneUniqueRoot_bool selfLoop -- false  (no in-degree-0 vertex)

-- ─── check: all four at once ────────────────────────────────────
#eval check tree         -- true
#eval check goodChain    -- true
#eval check selfLoop     -- false
#eval check twoCycle     -- false
#eval check forest2      -- false
#eval check hasShortcut  -- false
