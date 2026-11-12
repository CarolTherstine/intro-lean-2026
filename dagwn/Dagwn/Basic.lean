--semantic lexical network - Wordnet
structure Edge where
  target_id : Nat
  relation_name : String
--  deriving Repr, BEq

structure Vertex where
  id : Nat
  concept : String
  out_edges : List Edge
--  deriving Repr, BEq

structure Graph where
  vertices : List Vertex
--  deriving Repr



def get_vertex (g : Graph) (id : Nat) :=
  g.vertices.find? (fun v => v.id == id)

def has_edge_to (edges : List Edge) (target : Nat) : Bool :=
  edges.any (fun e => e.target_id == target)

def IsHyponym (g : Graph) (x y : Nat) : Bool :=
  match get_vertex g x with
  | none => false
  | some v => has_edge_to v.out_edges y

def IsHypernym (g : Graph) (x y : Nat) : Bool :=
  IsHyponym g y x

--Aqui colocar vertice ou deiar nat considerando ser o ID?
def Irreflexivity (g : Graph) : Prop
  := ∀ i : Nat, (get_vertex g i).isSome → ¬ IsHypernym g i i

def Irreflexivity_bool (g : Graph) : Bool
  := g.vertices.all (fun x => !IsHypernym g x.id x.id)

--Theorem 1 : Irreflexivity
-- ∀ i (¬ (i → i))
structure Graph_Synset where
  g : Graph
  irr: Irreflexivity_bool g

structure Graph_Synset2 where
  g : Graph
  irr: Irreflexivity_bool g :=by rfl


def penguim : Vertex :=
  {id:= 2, concept:= "penguim" , out_edges := List.nil}

def bird : Vertex :=
  {id:= 1, concept:= "bird" , out_edges := [Edge.mk 2 "is_a"]}

def bird2: Vertex :=
  {id:= 3, concept:= "bird2" , out_edges := [Edge.mk 3 "is_a"]}

def graphh : Graph :=
  {vertices := [bird, penguim]}

def graphh2 : Graph :=
  {vertices := [bird, penguim, bird2]}

theorem prov_irr : Irreflexivity_bool (graphh) := by
  rfl

def graphsemantic : Graph_Synset :=
  {g:= graphh, irr:= rfl}

def graphsemantic2 : Graph_Synset2 :=
  {g:= graphh2}
--==========================================================
theorem Transitivity : ∀ i j k : Nat , ∀ g : Graph , (IsHypernym g i j ∧ IsHypernym g j k → IsHypernym g i k) := by
  intro i j k g
  rfl
--Theorem 2 : Transitivity
-- ∀ (i, j , k ) (i → j ∧ j → k) → i → k

--==========================================================

theorem Assymetry : ∀ i j: Nat, ∀ g : Graph, IsHypernym g i j → IsHyponym g j i := by
  intro i j
  rfl

--Theorem 3 : Assymetry
--∀ (i, j) (i → j) → ¬ (j → i)

--==========================================================
--Theorem 4 : Unique Root
  --Root(r)  :=  ∀ a ∈ S, r →* a
  --∃! r ∈ S, Root(r)

--==========================================================
--Theorem 5 : Inheritance Monoticity
    --∀ (a, b, p) (a →* b) → inh(a, p) → inh(b, p)

--==========================================================
--def IsValid (g : Graph) : Prop :=
--  ∀ v ∈ g.vertices, ¬ CanReach g.vertices v.id v.id

--def has_self_loop (i : Vertex) : Prop :=
--  (i, i) ∈ i.out_edges_list
