# Backward Chaining FOL Engine

A simple Python implementation of a backward chaining inference engine for Horn clauses in First-Order Logic (FOL). Supports:

* Variables, Constants, Functions, Predicates
* Unification with occurs-check
* Horn clauses (facts and rules) of any arity
* Conjunctive queries (multiple subgoals)
* Recursive rules with cycle detection
* Graceful handling of false or malformed queries

## Files

* **`backward_chaining_fol.py`**: Main engine with example queries and expected outputs.

## Running

```bash
python backward_chaining_fol.py
```

## Example Queries & Expected Outputs

### True Cases

1. **`grandparent(abe, bart)`**

   ```
   Query: grandparent(abe, bart)
   YES
   ```

2. **`ancestor(x, bart)`**

   ```
   Query: ancestor(x, bart)
   x = homer
   x = abe
   ```

3. **`[father(abe, homer), parent(homer, bart)]`**

   ```
   Conjunctive Query: [father(abe, homer), parent(homer, bart)]
   Conjunction holds under substitution: {}
   ```

### False / Failure Cases

1. **`grandparent(bart, abe)`**

   ```
   Query: grandparent(bart, abe)  # false
   NO (as expected)
   ```

2. **`parent(x, lisa)`**

   ```
   Query: parent(x, lisa)  # 'lisa' not in KB
   NO ANSWERS (as expected)
   ```

3. **`[father(abe, bart), mother(homer, bart)]`**

   ```
   Conjunctive Query: [father(abe, bart), mother(homer, bart)]  # false
   CONJUNCTION FAILED (as expected)
   ```

4. **`father(abe)`** (wrong arity)

   ```
   Query: father(abe)  # wrong arity
   NO (as expected for wrong arity)
   ```

5. **`ancestor(bart, abe)`**

   ```
   Query: ancestor(bart, abe)  # no chain
   NO (as expected)
   ```

6. **`related(add(one, one), two)`** (undefined predicate)

   ```
   Query with function: related(add(one, one), two)
   NO (as expected for undefined predicate)
   ```

## Extending

* Add facts/rules via `kb.add_clause(Clause(...))`.
* Query single goals or lists of goals with `kb.ask(...)`.
* Variables are returned via substitutions; ground queries print `YES`/`NO`.

*End*
