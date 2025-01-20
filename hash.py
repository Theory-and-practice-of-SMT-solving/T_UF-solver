class HashConsing:
    def __init__(self):
        self.store = {}

    def get(self, obj):
        # Cria um hash baseado no conteúdo do objeto
        obj_hash = hash(obj)
        if obj_hash not in self.store:
            self.store[obj_hash] = obj
        return self.store[obj_hash]

# Exemplo de uso
consing = HashConsing()

a = consing.get([1, 2, 3, 4, 5, 6, 7, 8])
b = consing.get([1, 2, 3, 4, 5, 6, 7, 8])

print(a is b)  # True, porque 'a' e 'b' referenciam o mesmo objeto