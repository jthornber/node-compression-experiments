import heapq

instructions = [
    ("key frame", 691),
    ("inc thin", 22602),
    ("dec thin", 3650),
    ("inc data", 861029),
    ("dec data", 127048),
    ("len", 180056),
    ("len small", 350116),
    ("emit", 1014670),
    ("new reg", 13938),
    ("switch reg", 240558),
    ("shift", 41975),
    ("halt", 691),
]


class Node:
    def __init__(self, name, freq):
        self.name = name
        self.freq = freq
        self.left = None
        self.right = None

    def __lt__(self, other):
        return self.freq < other.freq


def build_huffman_tree(instructions):
    heap = [Node(name, freq) for name, freq in instructions]
    heapq.heapify(heap)

    while len(heap) > 1:
        left = heapq.heappop(heap)
        right = heapq.heappop(heap)
        merged = Node(None, left.freq + right.freq)
        merged.left = left
        merged.right = right
        heapq.heappush(heap, merged)

    return heap[0]


def generate_codes(root, current_code="", codes={}):
    if root is None:
        return

    if root.name is not None:
        codes[root.name] = current_code
        return

    generate_codes(root.left, current_code + "0", codes)
    generate_codes(root.right, current_code + "1", codes)
    return codes


root = build_huffman_tree(instructions)
huffman_codes = generate_codes(root)

# Sort by code length, then alphabetically
for name, code in sorted(huffman_codes.items(), key=lambda x: (len(x[1]), x[0])):
    print(f"{name}: {code}")
