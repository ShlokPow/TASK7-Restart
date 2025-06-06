import copy
from collections import defaultdict

class Expr:
    """Base class for all expressions (Variable, Constant, Function, Predicate)."""
    pass

class Variable(Expr):
    def __init__(self, name):
        self.name = name

    def __repr__(self):
        return self.name

    def __eq__(self, other):
        return isinstance(other, Variable) and self.name == other.name

    def __hash__(self):
        return hash(("Variable", self.name))

class Constant(Expr):
    def __init__(self, name):
        self.name = name

    def __repr__(self):
        return self.name

    def __eq__(self, other):
        return isinstance(other, Constant) and self.name == other.name

    def __hash__(self):
        return hash(("Constant", self.name))

class Function(Expr):
    def __init__(self, name, args):
        self.name = name
        self.args = args  # list of Expr

    def __repr__(self):
        return f"{self.name}({', '.join(map(str, self.args))})"

    def __eq__(self, other):
        return isinstance(other, Function) and self.name == other.name and self.args == other.args

    def __hash__(self):
        return hash(("Function", self.name, tuple(self.args)))

class Predicate(Expr):
    def __init__(self, name, args):
        self.name = name
        self.args = args  # list of Expr

    def __repr__(self):
        return f"{self.name}({', '.join(map(str, self.args))})"

    def __eq__(self, other):
        return isinstance(other, Predicate) and self.name == other.name and self.args == other.args

    def __hash__(self):
        return hash(("Predicate", self.name, tuple(self.args)))

# -------------------------
# Substitution (theta) functions
# -------------------------

def is_variable(x):
    """Check if x is a Variable."""
    return isinstance(x, Variable)


def is_compound(x):
    """Check if x is a composite term (Function or Predicate)."""
    return isinstance(x, (Function, Predicate))


def occurs_check(var, x, theta):
    """Prevent cyclic substitutions: var cannot appear in x under current theta."""
    x = substitute(x, theta)
    if var == x:
        return True
    if is_compound(x):
        for arg in x.args:
            if occurs_check(var, arg, theta):
                return True
    return False


def unify(x, y, theta):
    """Unify two expressions x and y given substitution theta. Return extended theta or None on failure."""
    if theta is None:
        return None
    if x == y:
        return theta
    x = substitute(x, theta)
    y = substitute(y, theta)
    if is_variable(x):
        return unify_var(x, y, theta)
    if is_variable(y):
        return unify_var(y, x, theta)
    if is_compound(x) and is_compound(y) and x.__class__ == y.__class__ and x.name == y.name and len(x.args) == len(y.args):
        for x_arg, y_arg in zip(x.args, y.args):
            theta = unify(x_arg, y_arg, theta)
            if theta is None:
                return None
        return theta
    return None


def unify_var(var, x, theta):
    """Handle variable unification under theta, ensuring no circular refs."""
    if var in theta:
        return unify(theta[var], x, theta)
    if is_variable(x) and x in theta:
        return unify(var, theta[x], theta)
    if occurs_check(var, x, theta):
        return None
    new_theta = theta.copy()
    new_theta[var] = x
    return new_theta


def substitute(x, theta):
    """Apply substitution theta to term or predicate x."""
    if isinstance(x, Variable):
        return substitute(theta[x], theta) if x in theta else x
    if isinstance(x, Function):
        return Function(x.name, [substitute(arg, theta) for arg in x.args])
    if isinstance(x, Predicate):
        return Predicate(x.name, [substitute(arg, theta) for arg in x.args])
    return x  # Constant

# -------------------------
# Knowledge Base Representation
# -------------------------

class Clause:
    """Horn clause: head <- body. If body is empty, it's a fact."""
    def __init__(self, head, body=None):
        self.head = head            # Predicate
        self.body = body or []      # list of Predicates (conjunction)

    def __repr__(self):
        if not self.body:
            return f"{self.head}."
        return f"{self.head} <- {', '.join(map(str, self.body))}."

class KnowledgeBase:
    """Collection of Horn clauses, indexed by predicate name and arity."""
    def __init__(self):
        self.clauses = []
        self.index = defaultdict(lambda: defaultdict(list))  # name -> arity -> [Clause]

    def add_clause(self, clause):
        """Add a clause (fact or rule) to the KB."""
        self.clauses.append(clause)
        key = (clause.head.name, len(clause.head.args))
        self.index[clause.head.name][len(clause.head.args)].append(clause)

    def fetch_clauses_for_goal(self, goal):
        """Retrieve all clauses whose head matches goal's predicate name and arity."""
        return self.index.get(goal.name, {}).get(len(goal.args), [])

    def ask(self, query):
        """Public interface to ask a single query or a list of conjunctive queries.
        Returns a generator of substitutions (theta).
        """
        if isinstance(query, list):
            # Conjunctive query: ask [G1, G2, ...]
            yield from fol_bc_and(self, query, {}, set())
        else:
            # Single goal
            yield from fol_bc_or(self, query, {}, set())

# -------------------------
# Backward Chaining Algorithm
# -------------------------

def fol_bc_or(kb, goal, theta, visited):
    """OR node: try all clauses whose head can unify with goal."""
    # Avoid infinite loops: check if this goal+theta was already visited
    current = substitute(goal, theta)
    if (repr(current), frozenset(theta.items())) in visited:
        return
    new_visited = visited.copy()
    new_visited.add((repr(current), frozenset(theta.items())))

    for clause in kb.fetch_clauses_for_goal(goal):
        clause_copy = standardize_apart(clause)
        head, body = clause_copy.head, clause_copy.body
        theta_prime = unify(head, current, theta)
        if theta_prime is not None:
            if not body:
                # It's a fact
                yield theta_prime
            else:
                # It's a rule with a body of subgoals
                yield from fol_bc_and(kb, body, theta_prime, new_visited)


def fol_bc_and(kb, goals, theta, visited):
    """AND node: ensure all subgoals succeed under theta."""
    if theta is None:
        return
    if not goals:
        # No more goals: current theta is a solution
        yield theta
    else:
        first, rest = goals[0], goals[1:]
        for theta_prime in fol_bc_or(kb, first, theta, visited):
            yield from fol_bc_and(kb, rest, theta_prime, visited)

_counter = 0

def standardize_apart(clause):
    """Produce a variable-renamed copy of clause with unique variable names."""
    global _counter
    mapping = {}
    def rename(expr):
        if isinstance(expr, Variable):
            if expr not in mapping:
                mapping[expr] = Variable(f"_{expr.name}{_counter}")
            return mapping[expr]
        if isinstance(expr, Function):
            return Function(expr.name, [rename(arg) for arg in expr.args])
        if isinstance(expr, Predicate):
            return Predicate(expr.name, [rename(arg) for arg in expr.args])
        return expr  # Constant

    _counter += 1
    new_head = rename(clause.head)
    new_body = [rename(b) for b in clause.body]
    return Clause(new_head, new_body)

# -------------------------
# Example Usage
# -------------------------
if __name__ == "__main__":
    # Build a knowledge base with facts and rules
    kb = KnowledgeBase()

    # Facts (simple relationships)
    kb.add_clause(Clause(Predicate("father", [Constant("abe"), Constant("homer")])))
    kb.add_clause(Clause(Predicate("father", [Constant("homer"), Constant("bart")])) )
    kb.add_clause(Clause(Predicate("mother", [Constant("mona"), Constant("bart")]))
    )

    # Rules (general relationships)
    x = Variable("x")
    y = Variable("y")
    z = Variable("z")
    kb.add_clause(Clause(Predicate("parent", [x, y]), [Predicate("father", [x, y])]))
    kb.add_clause(Clause(Predicate("parent", [x, y]), [Predicate("mother", [x, y])]))
    kb.add_clause(Clause(Predicate("grandparent", [x, z]), [Predicate("parent", [x, y]), Predicate("parent", [y, z])]))
    kb.add_clause(Clause(Predicate("ancestor", [x, z]), [Predicate("parent", [x, z])]))
    kb.add_clause(Clause(Predicate("ancestor", [x, z]), [Predicate("parent", [x, y]), Predicate("ancestor", [y, z])]))

    # --- Valid Queries ---
    print("Query: grandparent(abe, bart)")
    results = list(kb.ask(Predicate("grandparent", [Constant("abe"), Constant("bart")] )))
    if results:
        print("YES")
    else:
        print("NO")

    print("\nQuery: ancestor(x, bart)")
    ancestor_results = list(kb.ask(Predicate("ancestor", [x, Constant("bart")])) )
    if ancestor_results:
        for theta in ancestor_results:
            print("x =", substitute(x, theta))
    else:
        print("NO ANSWERS")

    print("\nConjunctive Query: [father(abe, homer), parent(homer, bart)]")
    goals = [Predicate("father", [Constant("abe"), Constant("homer")]),
             Predicate("parent", [Constant("homer"), Constant("bart")])]
    conj_results = list(kb.ask(goals))
    if conj_results:
        for theta in conj_results:
            print("Conjunction holds under substitution:", theta)
    else:
        print("CONJUNCTION FAILED")

    # --- Test Cases for Failures / False Statements ---
    print("\n--- Failure / False Test Cases ---")

    # 1. Asking a false ground fact
    print("Query: grandparent(bart, abe)  # Should be false")
    results_false1 = list(kb.ask(Predicate("grandparent", [Constant("bart"), Constant("abe")])) )
    if results_false1:
        print("ERROR: Unexpectedly found a proof for grandparent(bart, abe)")
    else:
        print("NO (as expected)")

    # 2. Asking a false non-ground query
    print("\nQuery: parent(x, lisa)  # 'lisa' not in KB")
    results_false2 = list(kb.ask(Predicate("parent", [x, Constant("lisa")])) )
    if results_false2:
        print("ERROR: Unexpected proof for parent(x, lisa)")
    else:
        print("NO ANSWERS (as expected)")

    # 3. Conjunctive query where one predicate is false
    print("\nConjunctive Query: [father(abe, bart), mother(homer, bart)]  # second is false")
    goals_false3 = [Predicate("father", [Constant("abe"), Constant("bart")]),
                    Predicate("mother", [Constant("homer"), Constant("bart")])]
    results_false3 = list(kb.ask(goals_false3))
    if results_false3:
        print("ERROR: Conjunction should fail but returned", results_false3)
    else:
        print("CONJUNCTION FAILED (as expected)")

    # 4. Querying a predicate with wrong arity
    print("\nQuery: father(abe)  # Wrong arity, should fail gracefully")
    try:
        results_false4 = list(kb.ask(Predicate("father", [Constant("abe")])))
        if results_false4:
            print("ERROR: Unexpected proof for father(abe)")
        else:
            print("NO (as expected for wrong arity)")
    except Exception as e:
        print("Handled error for wrong arity:", e)

    # 5. Recursive failure (ancestor where no chain exists)
    print("\nQuery: ancestor(bart, abe)  # No backward chain")
    results_false5 = list(kb.ask(Predicate("ancestor", [Constant("bart"), Constant("abe")])) )
    if results_false5:
        print("ERROR: Unexpected proof for ancestor(bart, abe)")
    else:
        print("NO (as expected)")

    # Example: use functions inside predicates (placeholder)
    print("\nQuery with function: related(add(one, one), two)  # No clauses defined for 'related'")
    results_func = list(kb.ask(Predicate("related", [Function("add", [Constant("one"), Constant("one")]), Constant("two")])) )
    if results_func:
        print("ERROR: Unexpected proof for related(add(one, one), two)")
    else:
        print("NO (as expected for undefined predicate)")

    pass
