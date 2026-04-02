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

        # Case 4: ¬(FORALL x P) → EXISTS x ¬P
        if child.data == "FORALL":
            new_node = BinaryTreeNode("EXISTS")

            var = copy_tree(child.left_child)
            formula = child.right_child

            not_formula = BinaryTreeNode("NOT")
            not_formula.set_left_child(copy_tree(formula))

            new_node.set_left_child(var)
            new_node.set_right_child(apply_negation(not_formula))

            return new_node

        # Case 5: ¬(EXISTS x P) → FORALL x ¬P
        if child.data == "EXISTS":
            new_node = BinaryTreeNode("FORALL")

            var = copy_tree(child.left_child)
            formula = child.right_child

            not_formula = BinaryTreeNode("NOT")
            not_formula.set_left_child(copy_tree(formula))

            new_node.set_left_child(var)
            new_node.set_right_child(apply_negation(not_formula))

            return new_node
        
    # If NOT does not apply to a transformable structure, leave it unchanged
    return node