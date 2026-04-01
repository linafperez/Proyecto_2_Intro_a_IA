from BinaryTreeNode import BinaryTreeNode
from collections import deque


class BinaryTree:
    def __init__(self):
        self.root = None

    def is_empty(self):
        return self.root is None

    def root_data(self):
        if self.is_empty():
            return None
        return self.root.get_data()
    
    def search(self, val):
        if self.is_empty():
            return False
        return self.root.search(val)

    def insert(self, parent, val):
        if self.is_empty():
            return False
        return self.root.insert(parent, val)

    def delete(self, val):
        if self.is_empty():
            return False

        if self.root.data == val:
            self.root = None
            return True

        return self.root.delete(val)

    def height(self):
        if self.is_empty():
            return -1
        return self.root.height()

    def size(self):
        if self.is_empty():
            return 0
        return self.root.size()

    def pre_order(self):
        if self.is_empty():
            return []
        return self.root.pre_order()

    def post_order(self):
        if self.is_empty():
            return []
        return self.root.post_order()

    def in_order(self):
        if self.is_empty():
            return []
        return self.root.in_order()

    def level_order(self):
        if self.is_empty():
            return []

        result = []
        queue = deque()
        queue.append(self.root)

        while queue:
            node = queue.popleft()
            result.append(node.data)

            if node.left_child is not None:
                queue.append(node.left_child)

            if node.right_child is not None:
                queue.append(node.right_child)

        return result

    @staticmethod
    # Convert a string into a list of tokens
    def tokenize(rule):

        tokens = []
        i = 0

        # Process every character in the input string
        while i < len(rule):

            # Skip whitespace characters
            if rule[i].isspace():
                i += 1
                continue

            # Treat parentheses as individual tokens
            if rule[i] in "()":
                tokens.append(rule[i])
                i += 1
                continue

            # Treat the implication operator "->" as a single token
            if rule[i:i+2] == "->":
                tokens.append("->")
                i += 2
                continue

            # Read a complete word (predicate, variable, constant, or keyword)
            # Continue until a space or parenthesis is found
            j = i
            while i < len(rule) and not rule[i].isspace() and rule[i] not in "()":
                i += 1

            # Extract and store the token
            tokens.append(rule[j:i])

        return tokens

    # Parsing by precedence
    @staticmethod
    def parse_implication(tokens, index):
        left = BinaryTree.parse_or(tokens, index)

        while index[0] < len(tokens) and tokens[index[0]] == "->":
            op = tokens[index[0]]
            index[0] += 1

            right = BinaryTree.parse_implication(tokens, index)

            node = BinaryTreeNode(op)
            node.set_left_child(left)
            node.set_right_child(right)

            left = node

        return left
    
    @staticmethod
    def parse_or(tokens, index):
        left = BinaryTree.parse_and(tokens, index)

        while index[0] < len(tokens) and tokens[index[0]] == "OR":
            op = tokens[index[0]]
            index[0] += 1

            right = BinaryTree.parse_and(tokens, index)

            node = BinaryTreeNode(op)
            node.set_left_child(left)
            node.set_right_child(right)

            left = node

        return left
    
    @staticmethod
    def parse_and(tokens, index):
        left = BinaryTree.parse_not(tokens, index)

        while index[0] < len(tokens) and tokens[index[0]] == "AND":
            op = tokens[index[0]]
            index[0] += 1

            right = BinaryTree.parse_not(tokens, index)

            node = BinaryTreeNode(op)
            node.set_left_child(left)
            node.set_right_child(right)

            left = node

        return left
    
    @staticmethod
    def parse_not(tokens, index):
        if tokens[index[0]] == "NOT":
            index[0] += 1
            child = BinaryTree.parse_not(tokens, index)

            node = BinaryTreeNode("NOT")
            node.set_left_child(child)

            return node

        return BinaryTree.parse_quantifier(tokens, index)
    
    @staticmethod
    def parse_quantifier(tokens, index):
        if tokens[index[0]] in ["FORALL", "EXISTS"]:
            quantifier = tokens[index[0]]
            index[0] += 1

            variable = tokens[index[0]]
            index[0] += 1

            # Create quantifier node
            node = BinaryTreeNode(quantifier)
            node.set_left_child(BinaryTreeNode(variable))

            # Parse body (can be parenthesized)
            if tokens[index[0]] == "(":
                index[0] += 1
                subtree = BinaryTree.parse_implication(tokens, index)
                index[0] += 1  # skip ')'
            else:
                subtree = BinaryTree.parse_implication(tokens, index)

            node.set_right_child(subtree)

            return node

        return BinaryTree.parse_atom(tokens, index)
    
    @staticmethod
    def parse_atom(tokens, index):
        token = tokens[index[0]]
        index[0] += 1

        # Case 1: Parenthesized expression
        if token == "(":
            node = BinaryTree.parse_implication(tokens, index)
            index[0] += 1  # skip ')'
            return node

        # Case 2: Predicate like Animal(X)
        if "(" in token:
            name = token[:token.index("(")]
            args = token[token.index("(")+1:-1].split(",")

            node = BinaryTreeNode(name)

            if len(args) >= 1:
                node.set_left_child(BinaryTreeNode(args[0]))
            if len(args) >= 2:
                node.set_right_child(BinaryTreeNode(args[1]))

            return node

        # Case 3: Variable or constant
        return BinaryTreeNode(token)

    @staticmethod
    # Build an expression tree from a first-order logic rule.
    def build_expression_tree(rule):

        # Tokenize the input string
        tokens = BinaryTree.tokenize(rule)

        # Use an index pointer to traverse tokens
        index = [0]

        # Parse the expression
        root = BinaryTree.parse_implication(tokens, index)

        return root