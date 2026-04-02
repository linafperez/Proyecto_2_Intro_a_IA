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
    
    def tokenize(rule):

        tokens = []
        i = 0

        while i < len(rule):

            # Skip spaces
            if rule[i].isspace():
                i += 1
                continue

            # Brackets
            if rule[i] in "[]":
                tokens.append(rule[i])
                i += 1
                continue

            # Biconditional
            if rule[i:i+3] == "<->":
                tokens.append("<->")
                i += 3
                continue

            # Implication
            if rule[i:i+2] == "->":
                tokens.append("->")
                i += 2
                continue

            # Read full token
            j = i
            paren_count = 0

            while i < len(rule):
                if rule[i] == "(":
                    paren_count += 1
                elif rule[i] == ")":
                    paren_count -= 1

                # Stop if space or bracket AND not inside predicate
                if paren_count == 0 and (rule[i].isspace() or rule[i] in "[]"):
                    break

                i += 1

            tokens.append(rule[j:i])

        return tokens
    
    # Shunting yard algorithm implementation 
    def infix_to_postfix(rule):

        tokens = BinaryTree.tokenize(rule)

        output = []
        op_stack = []

        precedence = {
            "FORALL": 6,
            "EXISTS": 6,
            "NOT": 5,
            "AND": 4,
            "OR": 3,
            "->": 2,
            "<->": 1
        }

        operators = set(precedence.keys())

        i = 0
        while i < len(tokens):
            token = tokens[i]

            # CASE 1: operand (predicate, variable, constant)
            if token not in operators and token not in ["[", "]"]:
                output.append(token)

            # CASE 2: opening bracket
            elif token == "[":
                op_stack.append(token)

            # CASE 3: closing bracket
            elif token == "]":
                while op_stack and op_stack[-1] != "[":
                    output.append(op_stack.pop())
                op_stack.pop()  # remove "["

            # CASE 4: unary operators (FORALL, EXISTS, NOT)
            elif token in ["FORALL", "EXISTS", "NOT"]:
                op_stack.append(token)

            # CASE 5: binary operators
            else:
                while (op_stack and op_stack[-1] != "[" and precedence.get(op_stack[-1], 0) >= precedence[token]):
                    output.append(op_stack.pop())

                op_stack.append(token)

            i += 1

        # Empty stack
        while op_stack:
            output.append(op_stack.pop())

        return output
    
    def build_expression_tree(rule):

        postfix = BinaryTree.infix_to_postfix(rule)

        stack = []

        binary_ops = {"AND", "OR", "->", "<->"}
        unary_ops = {"NOT"}

        i = 0
        while i < len(postfix):
            token = postfix[i]

            # CASE 1: binary operator
            if token in binary_ops:
                right = stack.pop()
                left = stack.pop()

                node = BinaryTreeNode(token)
                node.set_left_child(left)
                node.set_right_child(right)

                stack.append(node)

            # CASE 2: unary operator
            elif token in unary_ops:
                child = stack.pop()

                node = BinaryTreeNode(token)
                node.set_left_child(child)

                stack.append(node)

            # CASE 3: quantifiers
            elif token in ["FORALL", "EXISTS"]:
                formula = stack.pop()
                variable = stack.pop()

                node = BinaryTreeNode(token)
                node.set_left_child(variable)
                node.set_right_child(formula)

                stack.append(node)

            # CASE 4: predicate
            elif "(" in token:
                name = token[:token.index("(")]
                args_str = token[token.index("(")+1:-1]
                args = [a.strip() for a in args_str.split(",")]

                node = BinaryTreeNode(f"{name}()")

                if len(args) >= 1:
                    node.set_left_child(BinaryTreeNode(args[0]))

                if len(args) >= 2:
                    node.set_right_child(BinaryTreeNode(args[1]))

                stack.append(node)

            # CASE 5: variable / constant
            else:
                stack.append(BinaryTreeNode(token))

            i += 1

        return stack.pop()