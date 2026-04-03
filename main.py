import sys
from BinaryTree import BinaryTree

# Ensure that an input file is provided as a command-line argument
if len(sys.argv) < 2:
    print("Usage:", sys.argv[0], "input_file")
    sys.exit()

input_filename = sys.argv[1]

# Read the input file containing a knowledge base in first-order logic
try:
    with open(input_filename, "r") as reader:
        lines = reader.readlines()
except FileNotFoundError:
    print("File was not found")
    sys.exit()

"""
Expected input file format:

1 <rule>
2 <rule>
...
Q <query>
"""

rules = []
query = None

# Process each line in the file by storing the query and converting rules into expression trees
for line in lines:
    # Remove leading and trailing whitespace
    line = line.strip()

    # skip empty lines
    if not line:
        continue

    # Split into identifier and content
    parts = line.split(maxsplit=1)

    identifier, content = parts

    # Save the query
    if identifier == "Q":
        query = content

    # Process each rule
    elif identifier.isdigit():
        expression_tree = BinaryTree.build_expression_tree(content)
        rules.append(expression_tree)

# Function to create a deep copy of a binary tree
def copy_tree(node):
    if node is None:
        return None

    new_node = BinaryTreeNode(node.data)
    new_node.set_left_child(copy_tree(node.left_child))
    new_node.set_right_child(copy_tree(node.right_child))

    return new_node

# Logical operations to convert expressions into Conjunctive Normal Form
# Delete biconditional operators
def del_biconditional(node):
    """
    Recursively traverses the expression tree and eliminates biconditional operators (<->).
    Each occurrence of α <-> β is replaced with an equivalent structure: (α -> β) AND (β -> α)
    """
    if node is None:
        return None

    # Recurse first (post-order)
    node.set_left_child(del_biconditional(node.left_child))
    node.set_right_child(del_biconditional(node.right_child))

    # If current node is biconditional
    if node.data == "<->":

        alpha = node.left_child
        beta = node.right_child

        # Build (α -> β)
        left_impl = BinaryTreeNode("->")
        left_impl.set_left_child(copy_tree(alpha))
        left_impl.set_right_child(copy_tree(beta))

        # Build (β -> α)
        right_impl = BinaryTreeNode("->")
        right_impl.set_left_child(copy_tree(beta))
        right_impl.set_right_child(copy_tree(alpha))

        # Build AND
        new_node = BinaryTreeNode("AND")
        new_node.set_left_child(left_impl)
        new_node.set_right_child(right_impl)

        return new_node

    return node

# Delete implication operators
def del_implication(node):
    """
    Recursively traverses the expression tree and eliminates implication operators (->).
    Each occurrence of α -> β is replaced with an equivalent structure: (NOT α) OR β
    """
    if node is None:
        return None

    # Recurse first (post-order)
    node.set_left_child(del_implication(node.left_child))
    node.set_right_child(del_implication(node.right_child))

    # If current node is implication
    if node.data == "->":

        alpha = node.left_child
        beta = node.right_child

        # Build NOT α
        not_alpha = BinaryTreeNode("NOT")
        not_alpha.set_left_child(copy_tree(alpha))

        # Build (NOT α) OR β
        new_node = BinaryTreeNode("OR")
        new_node.set_left_child(not_alpha)
        new_node.set_right_child(copy_tree(beta))

        return new_node

    return node

# Apply negation rules
def apply_negation(node):

    if node is None:
        return None

    # Recurse first (post-order)
    node.set_left_child(apply_negation(node.left_child))
    node.set_right_child(apply_negation(node.right_child))

    # Case: NOT node
    if node.data == "NOT":

        child = node.left_child

        if child is None:
            return node

        # Case 1: Double negation ¬(¬α) → α
        if child.data == "NOT":
            return apply_negation(child.left_child)

        # Case 2: ¬(α AND β) → (¬α OR ¬β)
        if child.data == "AND":
            new_node = BinaryTreeNode("OR")

            left_not = BinaryTreeNode("NOT")
            left_not.set_left_child(copy_tree(child.left_child))

            right_not = BinaryTreeNode("NOT")
            right_not.set_left_child(copy_tree(child.right_child))

            new_node.set_left_child(apply_negation(left_not))
            new_node.set_right_child(apply_negation(right_not))

            return new_node

        # Case 3: ¬(α OR β) → (¬α AND ¬β)
        if child.data == "OR":
            new_node = BinaryTreeNode("AND")

            left_not = BinaryTreeNode("NOT")
            left_not.set_left_child(copy_tree(child.left_child))

            right_not = BinaryTreeNode("NOT")
            right_not.set_left_child(copy_tree(child.right_child))

            new_node.set_left_child(apply_negation(left_not))
            new_node.set_right_child(apply_negation(right_not))

            return new_node

        # Case 4: ¬(FORALL X P(X)) → EXISTS X ¬P(X)
        if child.data == "FORALL":
            new_node = BinaryTreeNode("EXISTS")

            var = copy_tree(child.left_child)

            not_formula = BinaryTreeNode("NOT")
            not_formula.set_left_child(copy_tree(child.right_child))

            new_node.set_left_child(var)
            new_node.set_right_child(apply_negation(not_formula))
            
            return new_node

        # Case 5: ¬(EXISTS X P(X)) → FORALL X ¬P(X)
        if child.data == "EXISTS":
            new_node = BinaryTreeNode("FORALL")

            var = copy_tree(child.left_child)

            not_formula = BinaryTreeNode("NOT")
            not_formula.set_left_child(copy_tree(child.right_child))

            new_node.set_left_child(var)
            new_node.set_right_child(apply_negation(not_formula))

            return new_node
        
    # If NOT does not apply to a transformable structure, leave it unchanged
    return node

# Renames variables only if a conflict is detected.
def standardize_variables(node, mapping=None, used_vars=None):

    if node is None:
        return None

    if mapping is None:
        mapping = {}

    if used_vars is None:
        used_vars = set()

    # Case: quantifier
    if node.data in ["FORALL", "EXISTS"]:
        old_var = node.left_child.data

        # Detect conflict
        if old_var in used_vars:
            new_var = f"{old_var}_{len(used_vars)}"
        else:
            new_var = old_var

        # Update structures
        used_vars_new = used_vars.copy()
        used_vars_new.add(new_var)

        mapping_new = mapping.copy()
        mapping_new[old_var] = new_var

        node.set_left_child(BinaryTreeNode(new_var))
        node.set_right_child(standardize_variables(node.right_child, mapping_new, used_vars_new))

        return node

    # Case: leaf (variable)
    if node.left_child is None and node.right_child is None:
        if node.data in mapping:
            return BinaryTreeNode(mapping[node.data])
        return node

    # Recurse
    node.set_left_child(standardize_variables(node.left_child, mapping, used_vars))
    node.set_right_child(standardize_variables(node.right_child, mapping, used_vars))

    return node

# Move quantifiers outward
def move_quantifiers_left(node):
    """
    Recursively moves quantifiers outward so that all quantifiers appear
    at the front of the expression.
    """

    if node is None:
        return None

    node.set_left_child(move_quantifiers_left(node.left_child))
    node.set_right_child(move_quantifiers_left(node.right_child))

    # Case: binary operator with quantifier inside
    if node.data in ["AND", "OR"]:

        # Left side has quantifier
        if node.left_child and node.left_child.data in ["FORALL", "EXISTS"]:
            quant = node.left_child.data
            var = node.left_child.left_child
            sub = node.left_child.right_child

            new_node = BinaryTreeNode(quant)
            new_node.set_left_child(var)

            inner = BinaryTreeNode(node.data)
            inner.set_left_child(sub)
            inner.set_right_child(node.right_child)

            new_node.set_right_child(move_quantifiers_left(inner))
            return new_node

        # Right side has quantifier
        if node.right_child and node.right_child.data in ["FORALL", "EXISTS"]:
            quant = node.right_child.data
            var = node.right_child.left_child
            sub = node.right_child.right_child

            new_node = BinaryTreeNode(quant)
            new_node.set_left_child(var)

            inner = BinaryTreeNode(node.data)
            inner.set_left_child(node.left_child)
            inner.set_right_child(sub)

            new_node.set_right_child(move_quantifiers_left(inner))
            return new_node

    return node

# Eliminate existential quantifiers using Skolem functions
def build_skolem_term(name, args):
    node = BinaryTreeNode(f"{name}()")

    if len(args) >= 1:
        node.set_left_child(BinaryTreeNode(args[0]))
    if len(args) >= 2:
        node.set_right_child(BinaryTreeNode(args[1]))

    return node

def replace_variable(node, var, value_node):
    if node is None:
        return None

    # Leaf (variable)
    if node.left_child is None and node.right_child is None:
        if node.data == var:
            return value_node
        return node

    node.set_left_child(replace_variable(node.left_child, var, value_node))
    node.set_right_child(replace_variable(node.right_child, var, value_node))

    return node

def skolemize(node, universal_vars=None, counter=[0]):

    # Base case: empty node
    if node is None:
        return None

    # Initialize list of universally quantified variables in scope
    if universal_vars is None:
        universal_vars = []

    # Case: universal quantifier (FORALL)
    # Add the variable to the current scope and recurse on its subtree
    if node.data == "FORALL":
        var = node.left_child.data
        new_universal_vars = universal_vars + [var]

        node.set_right_child(skolemize(node.right_child, new_universal_vars, counter))
        return node

    # Case: existential quantifier (EXISTS)
    # Replace the quantified variable using a Skolem term
    if node.data == "EXISTS":
        var = node.left_child.data

        # Create Skolem term:
        # - If there are no universal variables in scope, use a constant (K_i)
        # - Otherwise, use a function (F_i) with current universal variables as arguments
        if not universal_vars:
            name = f"K{counter[0]}"
            args = []
        else:
            name = f"F{counter[0]}"
            args = universal_vars

        counter[0] += 1

        # Build the Skolem term as a subtree
        skolem_node = build_skolem_term(name, args)

        # Replace all occurrences of the variable in the subtree
        replaced = replace_variable(node.right_child, var, skolem_node)

        # Continue processing after removing the existential quantifier
        return skolemize(replaced, universal_vars, counter)

    # Recursive case: process both children
    node.set_left_child(skolemize(node.left_child, universal_vars, counter))
    node.set_right_child(skolemize(node.right_child, universal_vars, counter))

    return node

# Remove universal quantifiers (they become implicit)
def remove_universal_quantifiers(node):
    """
    Recursively removes universal quantifiers (FORALL) from the expression tree.
    """

    if node is None:
        return None

    # Case: FORALL
    if node.data == "FORALL":
        return remove_universal_quantifiers(node.right_child)

    # Recurse
    node.set_left_child(remove_universal_quantifiers(node.left_child))
    node.set_right_child(remove_universal_quantifiers(node.right_child))

    return node

# Distribute OR over AND to obtain Conjunctive Normal Form
def distribute_or_over_and(node):
    """
    Recursively applies distribution of OR over AND to transform the expression
    into a conjunction of disjunctions (CNF).

    (α AND β) OR γ → (α OR γ) AND (β OR γ)
    α OR (β AND γ) → (α OR β) AND (α OR γ)
    """

    if node is None:
        return None

    node.set_left_child(distribute_or_over_and(node.left_child))
    node.set_right_child(distribute_or_over_and(node.right_child))

    # Case: OR node
    if node.data == "OR":

        left = node.left_child
        right = node.right_child

        # (A AND B) OR C
        if left and left.data == "AND":
            A = left.left_child
            B = left.right_child
            C = right

            new_node = BinaryTreeNode("AND")

            left_or = BinaryTreeNode("OR")
            left_or.set_left_child(copy_tree(A))
            left_or.set_right_child(copy_tree(C))

            right_or = BinaryTreeNode("OR")
            right_or.set_left_child(copy_tree(B))
            right_or.set_right_child(copy_tree(C))

            new_node.set_left_child(distribute_or_over_and(left_or))
            new_node.set_right_child(distribute_or_over_and(right_or))

            return new_node

        # A OR (B AND C)
        if right and right.data == "AND":
            A = left
            B = right.left_child
            C = right.right_child

            new_node = BinaryTreeNode("AND")

            left_or = BinaryTreeNode("OR")
            left_or.set_left_child(copy_tree(A))
            left_or.set_right_child(copy_tree(B))

            right_or = BinaryTreeNode("OR")
            right_or.set_left_child(copy_tree(A))
            right_or.set_right_child(copy_tree(C))

            new_node.set_left_child(distribute_or_over_and(left_or))
            new_node.set_right_child(distribute_or_over_and(right_or))

            return new_node

    return node

# Extract clauses from CNF (separate conjunctions)
def extract_clauses(node):
    """
    Converts a CNF expression tree into a list of clauses.
    Each clause is a disjunction (OR subtree), and the conjunction (AND)
    is represented as a list of such clauses.
    """

    if node is None:
        return []

    # Case: AND → split into multiple clauses
    if node.data == "AND":
        return extract_clauses(node.left_child) + extract_clauses(node.right_child)

    # Otherwise, this is a single clause
    return [node]