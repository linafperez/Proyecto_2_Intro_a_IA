class BinaryTreeNode:
    def __init__(self, data):
        self.data = data
        self.left_child = None
        self.right_child = None

    def get_data(self):
        return self.data
    
    def set_data(self, val):
        self.data = val

    def get_left_child(self):
        return self.left_child
    
    def get_right_child(self):
        return self.right_child
    
    def set_left_child(self, left):
        self.left_child = left

    def set_right_child(self, right):
        self.right_child = right

    def search(self, val):
        if self.data == val:
            return True

        if self.left_child is not None:
            if self.left_child.search(val):
                return True

        if self.right_child is not None:
            if self.right_child.search(val):
                return True

        return False

    def insert(self, parent, val):
        if self.data == parent:
            if self.left_child is None:
                self.left_child = BinaryTreeNode(val)
                return True
            elif self.right_child is None:
                self.right_child = BinaryTreeNode(val)
                return True
            else:
                return False

        if self.left_child is not None:
            if self.left_child.insert(parent, val):
                return True

        if self.right_child is not None:
            if self.right_child.insert(parent, val):
                return True

        return False

    def delete(self, val):
        # check left child
        if self.left_child is not None:
            if self.left_child.data == val:
                self.left_child = None
                return True

            if self.left_child.delete(val):
                return True

        # check right child
        if self.right_child is not None:
            if self.right_child.data == val:
                self.right_child = None
                return True

            if self.right_child.delete(val):
                return True

        return False
    
    def is_leaf(self):
        return self.left_child is None and self.right_child is None

    def height(self):
        if self.is_leaf():
            return 0

        left_height = -1
        right_height = -1

        if self.left_child is not None:
            left_height = self.left_child.height()

        if self.right_child is not None:
            right_height = self.right_child.height()

        return max(left_height, right_height) + 1

    def size(self):
        count = 1

        if self.left_child is not None:
            count += self.left_child.size()

        if self.right_child is not None:
            count += self.right_child.size()

        return count

    def pre_order(self):
        result = []
        result.append(self.data)

        if self.left_child is not None:
            result += self.left_child.pre_order()

        if self.right_child is not None:
            result += self.right_child.pre_order()

        return result

    def post_order(self):
        result = []

        if self.left_child is not None:
            result += self.left_child.post_order()

        if self.right_child is not None:
            result += self.right_child.post_order()

        result.append(self.data)

        return result

    def in_order(self):
        result = []

        if self.left_child is not None:
            result += self.left_child.in_order()

        result.append(self.data)

        if self.right_child is not None:
            result += self.right_child.in_order()

        return result