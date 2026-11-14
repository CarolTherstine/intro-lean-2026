--semantic lexical network - Wordnet
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

--Theorem 2 : Transitivity
-- ∀ (x, y , z ) (x → y ∧ y → z) → x indirect → z
def Transitivity_bool (g : Graph) : Bool :=
  g.vertices.all (fun x =>
    g.vertices.all (fun y =>
      g.vertices.all (fun z =>
        !(DirectHyponym g x.id y.id && DirectHyponym g y.id z.id) ||
         (IndirectHyponym g x.id z.id && !DirectHyponym g x.id z.id))))

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

end SynsetGraph

--================================================================
--                SANITY CHECKS
--================================================================
def check (g : Graph) : Bool :=
  Irreflexivity_bool g &&
  Asymmetry_bool g &&
  Transitivity_bool g &&
  HasOneUniqueRoot_bool g

def tree : Graph :=
  { vertices :=
    [ { id := 0, concept := "animal", out_edges :=
        [ { target_id := 1, relation_name := "is-a" }
        , { target_id := 2, relation_name := "is-a" } ] }
    , { id := 1, concept := "dog",    out_edges := [] }
    , { id := 2, concept := "cat",    out_edges := [] } ] }

#eval Irreflexivity_bool     tree   -- true
#eval Asymmetry_bool         tree   -- true
#eval Transitivity_bool      tree   -- true
#eval HasOneUniqueRoot_bool  tree   -- true
#eval check tree


def selfLoop : Graph :=
  { vertices :=
    [ { id := 0, concept := "a", out_edges := [{ target_id := 0, relation_name := "r" }] } ] }

def twoCycle : Graph :=
  { vertices :=
    [ { id := 0, concept := "a", out_edges := [{ target_id := 1, relation_name := "r" }] }
    , { id := 1, concept := "b", out_edges := [{ target_id := 0, relation_name := "r" }] } ] }

def forest2 : Graph :=
  { vertices :=
    [ { id := 0, concept := "a", out_edges := [{ target_id := 1, relation_name := "r" }] }
    , { id := 1, concept := "b", out_edges := [] }
    , { id := 2, concept := "c", out_edges := [{ target_id := 3, relation_name := "r" }] }
    , { id := 3, concept := "d", out_edges := [] } ] }

def noShortcut : Graph :=   -- 0 → 1 → 2 but NO 0 → 2
  { vertices :=
    [ { id := 0, concept := "a", out_edges := [{ target_id := 1, relation_name := "r" }] }
    , { id := 1, concept := "b", out_edges := [{ target_id := 2, relation_name := "r" }] }
    , { id := 2, concept := "c", out_edges := [] } ] }

def goodChain : Graph :=    -- 0 → 1 → 2, no shortcut: property holds
  { vertices :=
    [ { id := 0, concept := "a", out_edges := [{ target_id := 1, relation_name := "r" }] }
    , { id := 1, concept := "b", out_edges := [{ target_id := 2, relation_name := "r" }] }
    , { id := 2, concept := "c", out_edges := [] } ] }

def hasShortcut : Graph :=  -- 0 → 1 → 2 AND 0 → 2: property FAILS
  { vertices :=
    [ { id := 0, concept := "a", out_edges :=
        [ { target_id := 1, relation_name := "r" }
        , { target_id := 2, relation_name := "r" } ] }
    , { id := 1, concept := "b", out_edges := [{ target_id := 2, relation_name := "r" }] }
    , { id := 2, concept := "c", out_edges := [] } ] }

#eval Irreflexivity_bool    selfLoop    -- false  (0 → 0)
#eval Asymmetry_bool        twoCycle    -- false
#eval HasOneUniqueRoot_bool forest2     -- false  (two roots: 0 and 2)
#eval Transitivity_bool     noShortcut  -- true
#eval Asymmetry_bool        tree        -- true
#eval Transitivity_bool     tree        -- true
#eval HasOneUniqueRoot_bool tree        -- true
#eval Irreflexivity_bool    tree        -- true
#eval Transitivity_bool tree         -- true   (no 2-hop paths at all)
#eval Transitivity_bool goodChain    -- true   (0→1→2, no 0→2)   ← the graph you called noShortcut
#eval Transitivity_bool hasShortcut  -- false  (0→1→2 AND 0→2)   ← the actual counterexample
#eval Transitivity_bool twoCycle     -- false  (0→1→0: premise holds for x=0,y=1,z=0,
                                                --   and 0→0? no direct self-loop…
                                                --   but wait, see below)
