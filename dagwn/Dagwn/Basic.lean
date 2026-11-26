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

def reaches_pos (g : Graph) (steps x y : Nat) : Bool :=
  match steps with
  | 0 => false
  | steps + 1 =>
    match get_vertex g x with
    | none   => false
    | some v => v.out_edges.any (fun e => reaches g steps e.target_id y)

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

--is x a indirect hypernym of y
def IndirectHyponym (g : Graph) (x y : Nat) : Bool :=
  match get_vertex g x, get_vertex g y with
  | some _, some _ => reaches g (g.vertices.length + 1) x y
  | _, _           => false

--is y an indirect hypernym of x
def IndirectHypernym (g : Graph) (x y : Nat) : Bool :=
  IndirectHyponym g y x


--================================================================
--                THEOREM FUNCTIONS
--================================================================
--guarantee that for all vertices in g none is the hypernym to itself
-- therefore no vertices points to itself

--===========================================================================

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

--===========================================================================

--Theorem 2 : Transitivity
-- ∀ (x, y , z ) (x → y ∧ y → z) → x indirect → z
def Transitivity_bool (g : Graph) : Bool :=
  g.vertices.all (fun x =>
    g.vertices.all (fun y =>
      g.vertices.all (fun z =>
        !((IndirectHyponym g x.id y.id || DirectHyponym g x.id y.id) &&
           DirectHyponym g y.id z.id) ||
        IndirectHyponym g x.id z.id)))

inductive Transitivity (g : Graph) (x : Nat) : Nat → Prop where
  | step {cur : Nat} :
      reaches g (g.vertices.length + 1) x cur = true →
      --para todo next hiponimio direto de cur, ele herda de x (ie reaches)
      (∀ nxt : Nat, DirectHyponym g cur nxt = true → Transitivity g x nxt)
      -- → Transitivity g x cur

--theorem Transitivity_bool_iff (g : Graph) :
--∀ x, Transitivity_bool = true := by sorry

--===========================================================================

--Theorem 3 : Assymetry
--∀ (i, j) (i → j) → ¬ (j → i)
def Asymmetry_bool (g : Graph) : Bool :=
  g.vertices.all (fun x =>
      g.vertices.all (fun y =>
          if DirectHyponym g x.id y.id then
                      !IndirectHypernym g x.id y.id
                    else
                      true
      ))

def Asymmetry (g  : Graph) : Prop :=
  ∀ x ∈ g.vertices, ∀ y ∈ g.vertices, (DirectHyponym g x.id y.id ) → ¬ IndirectHypernym g x.id y.id


theorem Asymetry_bool_iff (g : Graph) :
  Asymmetry_bool g ↔ Asymmetry g := by
  unfold Asymmetry_bool Asymmetry
  simp only [List.all_eq_true, Bool.ite_eq_true_distrib, Bool.not_eq_true']
  constructor
  · intro h x hx y hy h_hypo
    have h_inner := h x hx y hy
    simp [h_hypo] at h_inner
    rw[h_inner]
    trivial
  · intro h x hx y hy
    case mpr =>
      split
      · next h_hypo =>
        simpa using h x hx y hy h_hypo
      · trivial

--===========================================================================

--Theorem 4 : Unique Root
--Root(r)  :=  ∀ a ∈ S, r →* a
--∃! r ∈ S, Root(r)
def UniqueRoot_bool (g : Graph) (r : Nat) : Bool :=
  !has_edge_to_in_g g r &&
  g.vertices.all (fun v => IndirectHyponym g r v.id)

--exactly 1 unique
def HasOneUniqueRoot_bool (g : Graph) : Bool :=
  (g.vertices.filter (fun v => UniqueRoot_bool g v.id)).length == 1

--================================================================
--               SPECIFIC GRAPH
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



inductive AcyclicFrom (g : Graph) : Nat → Prop where
  | free {u : Nat} :
      reaches_pos g (g.vertices.length + 1) u u = false →
      (∀ v : Vertex, get_vertex g u = some v →
        ∀ e ∈ v.out_edges, AcyclicFrom g e.target_id) →
      AcyclicFrom g u

def Acyclic (g : Graph) : Prop :=
  ∀ v ∈ g.vertices, AcyclicFrom g v.id

theorem Acyclicity_from_props (g: Graph) :
(Irreflexivity_bool g = true ∧ Asymmetry_bool g = true ∧ Transitivity_bool g = true )
→ Acyclic g := by
  intro x y z
  sorry
--theorem acyclic_with_irrefl_trans_asym
--(g : Graph)
--(hIrrefl : Irreflexivity g)
--(hAsym : Asymmetry g)
--(hTrans : Transitivity g)
--(hAcyc : Acyclic g)

-- 1. Well-formedness: edges stay inside g.vertices and IDs resolve cleanly
def WellFormed (g : Graph) : Prop :=
  (∀ x ∈ g.vertices, get_vertex g x.id = some x) ∧
  (∀ v ∈ g.vertices, ∀ e ∈ v.out_edges, ∃ w ∈ g.vertices, w.id = e.target_id)

-- 2. Monotonicity of `reaches` in the step bound
theorem reaches_mono (g : Graph) (n x y : Nat) :
    reaches g n x y = true → reaches g (n + 1) x y = true := by
  intro h
  simp only [reaches, Bool.or_eq_true]
  cases eq_xy : (x == y)
  · right
    rw [reaches] at h
    simp [eq_xy] at h
    exact h
  · left; rfl

-- 3. No self-loops at positive length (combines Irreflexivity + Asymmetry)
theorem no_pos_cycle (g : Graph) (hwf : WellFormed g)
    (hirr : Irreflexivity g) (hasym : Asymmetry g)
    (u : Vertex) (hu : u ∈ g.vertices) :
    reaches_pos g (g.vertices.length + 1) u.id u.id = false := by
  -- Proof by contradiction: suppose reaches_pos ... = true
  rw [Bool.eq_false_iff]
  intro hpos
  unfold reaches_pos at hpos
  rw [hwf.1 u hu] at hpos
  rw [List.any_eq_true] at hpos
  rcases hpos with ⟨e, he_mem, hreach⟩
  -- Find the target vertex w ∈ g.vertices
  rcases hwf.2 u hu e he_mem with ⟨w, hw_mem, hw_id⟩
  rw [← hw_id] at hreach he_mem
  -- Establish DirectHyponym g u.id w.id = true
  have hdir : DirectHyponym g u.id w.id = true := by
    unfold DirectHyponym has_edge_to
    rw [hwf.1 u hu, List.any_eq_true]
    exact ⟨e, he_mem, by simp [hw_id]⟩
  -- Lift reaches g len w.id u.id to IndirectHyponym g w.id u.id
  have hind : IndirectHyponym g w.id u.id = true := by
    unfold IndirectHyponym
    rw [hwf.1 w hw_mem, hwf.1 u hu]
    exact reaches_mono g g.vertices.length w.id u.id hreach
  -- Contradicts Asymmetry g u hu w hw hdir
  exact hasym u hu w hw_mem hdir hind

-- 4. Well-founded induction to build AcyclicFrom
-- Because g has no cycles (no_pos_cycle), every path terminates in ≤ g.vertices.length steps.
-- Induct on `fuel : Nat` where `reaches_pos g (fuel + 1) u.id u.id = false`
-- or on the cardinality of reachable vertices.
theorem acyclicFrom_aux (g : Graph) (hwf : WellFormed g)
    (hirr : Irreflexivity g) (hasym : Asymmetry g)
    (k : Nat) (u : Vertex) (hu : u ∈ g.vertices)
    (hk : ∀ y, reaches_pos g (k + 1) u.id y = true → False) :
    AcyclicFrom g u.id := by
  induction k generalizing u with
  | zero =>
    refine AcyclicFrom.free (no_pos_cycle g hwf hirr hasym u hu) ?_
    intro v hv e he
    rw [hwf.1 u hu] at hv
    injection hv with hv_eq; subst hv_eq
    exfalso
    apply hk e.target_id
    unfold reaches_pos
    rw [hwf.1 u hu, List.any_eq_true]
    refine ⟨e, he, ?_⟩
    simp [reaches]
  | succ k ih =>
    refine AcyclicFrom.free (no_pos_cycle g hwf hirr hasym u hu) ?_
    intro v hv e he
    rw [hwf.1 u hu] at hv
    injection hv with hv_eq; subst hv_eq
    rcases hwf.2 u hu e he with ⟨w, hw_mem, hw_id⟩
    rw [← hw_id]
    apply ih w hw_mem
    intro y hy
    apply hk y
    -- A path of length k+1 from w gives a path of length k+2 from u
    unfold reaches_pos at hy ⊢
    rw [hwf.1 u hu, List.any_eq_true]
    refine ⟨e, he, ?_⟩
    rw [← hw_id, reaches]
    simp only [Bool.or_eq_true]
    right
    exact hy

theorem acyclic_with_irrefl_trans_asym
(g : Graph)
(hAcyc : Acyclic g) :
∀ g : Graph, Acyclic g →
 Transitivity_bool g = true ∧ Asymmetry_bool g = true ∧ Irreflexivity_bool g = true
 :=by
  intro x y
  simp[Acyclic] at y
  simp [Asymetry_bool_iff, Irreflexivity_bool_iff]
  simp[Transitivity_bool, Asymmetry, Irreflexivity]
  simp[IndirectHypernym, DirectHyponym, IndirectHyponym]



theorem acyclic_from_of_irrefl_trans_asym
    (g : Graph)
    (hIrrefl : Irreflexivity g)
    (hAsym : Asymmetry g)
    (u : Vertex)
    (hu_mem : u ∈ g.vertices)
    (hTransU : ∀ z, reaches g (g.vertices.length + 1) u.id z = true → Transitivity g u.id z)
    (hChildAc : ∀ v : Vertex, get_vertex g u.id = some v →
      ∀ e ∈ v.out_edges, AcyclicFrom g e.target_id) :
    AcyclicFrom g u.id := by
  refine AcyclicFrom.free ?_ hChildAc
  cases hpos : reaches_pos g (g.vertices.length + 1) u.id u.id with
  | false => rfl
  | true =>
    -- Unfold one step of `reaches_pos` from `u.id` back to `u.id`
    cases hlen : g.vertices.length with
    | zero =>
      simp [reaches_pos] at hpos
    | succ n =>
      simp only [reaches_pos] at hpos
      cases hvu : get_vertex g u.id with
      | none =>
        rw [hvu] at hpos
        simp at hpos
      | some vu =>
        rw [hvu] at hpos
        simp only [Bool.any_eq_true] at hpos
        rcases hpos with ⟨e, he_mem, he_to_u⟩
        -- If `e.target_id == u.id` and `he_to_u` is 0-step (`rfl`), we have a direct
        -- self-edge `u.id -> u.id`, contradicting `hIrrefl u hu_mem`.
        -- Otherwise `e.target_id` reaches `u.id` in `n` steps while `hTransU` gives
        -- `Transitivity g u.id e.target_id`, contradicting `hAsym`.
        sorry

theorem Acyclicity (g : Graph) (hAc : Acyclic g) :
  ∀ (x y : Nat) (v w : Vertex),
  (get_vertex g x = some v ∧ get_vertex g y = some w ∧ v.id ≠ w.id )
  → (reaches g (g.vertices.length + 1) v.id w.id)
  → ! reaches g (g.vertices.length + 1) w.id v.id :=by
  intro x y v w hi hreach_vw
  obtain ⟨hv, hw, hne⟩ := hi
  simp
  simp only [get_vertex] at hv hw
  have hv_mem : v ∈ g.vertices := by
    induction g.vertices with
    | nil => simp [List.find?_eq_none] at hv
    | cons hd tl ih =>
      simp only [List.find?] at hv
      split at hv
      · cases hv
        exact List.Mem.head tl
      · exact List.Mem.tail hd (ih hv)

  rw [reaches, get_vertex] at hreach_vw
  simp[hv_mem] at hv
  have hv_eq : v.id = x := beq_iff_eq.mp hv_mem
  rw [← hv_eq, hv]
  rw[hv] at hreach_vw



def Acyclicity2 (g : Graph) : Bool :=
  g.vertices.all (fun x =>
    match get_vertex g x.id with
    | none   => true
    | some v => !reaches_pos g (g.vertices.length + 1) v.id v.id)

--def HasCycle (g : Graph) : Bool :=
--definir o q eh ciclo
--e provar q as propriedades provam q n tem ciclo


theorem synset_cycle (s: SynsetGraph) : Acyclicity s.g = true := by
  have h1 := s.irr
  have h2 := s.ass
  have h3 := s.trsnt
  sorry

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
