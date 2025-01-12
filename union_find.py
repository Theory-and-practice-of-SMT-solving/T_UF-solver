class UnionFind:
    def __init__(self):
        
        self.parent = {}
        self.rank = {}

    def find(self, element):
        
        if self.parent[element] != element:
            # path compression: recursively set the parent to the representative
            self.parent[element] = self.find(self.parent[element])
        return self.parent[element]

    def union(self, element1, element2):
        root1 = self.find(element1)
        root2 = self.find(element2)

        if root1 != root2:
            # union by rank: 
            if self.rank[root1] > self.rank[root2]:
                self.parent[root2] = root1
            elif self.rank[root1] < self.rank[root2]:
                self.parent[root1] = root2
            else:
                # if ranks are the same, arbitrarily choose one as root and increment its rank
                self.parent[root2] = root1
                self.rank[root1] += 1

    def add(self, element):
 
        if element not in self.parent:
            self.parent[element] = element
            self.rank[element] = 0

    def connected(self, element1, element2):
        
        # vê se estão no mesmo set
        return self.find(element1) == self.find(element2)

# Exemplos de uso:
uf = UnionFind()

# add elems
uf.add('a')
uf.add('b')
uf.add('c')
uf.add('d')

# unions
uf.union('a', 'b')
uf.union('c', 'd')

# find representantes
print(uf.find('a'))
print(uf.find('b'))

# checkar connectividade
print(uf.connected('a', 'b'))  # Output: True
print(uf.connected('a', 'c'))  # Output: False

# mais elementos
uf.union('b', 'c')
print(uf.connected('a', 'c'))  # Output: True

