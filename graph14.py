import networkx as nx

G = nx.DiGraph()

u = [0, 0, 0, 0, 0, 0, 1, 1, 1, 2, 2, 2, 2, 2, 2, 3, 3, 4, 4, 4, 5, 5, 5, 5, 6, 6, 6, 7, 7, 7, 7, 7, 8, 8, 8, 8, 8, 8, 9, 9]
v = [1, 5, 7, 7, 8, 9, 0, 3, 3, 0, 0, 4, 8, 9, 9, 2, 5, 0, 1, 5, 3, 4, 6, 9, 2, 8, 9, 4, 6, 6, 6, 6, 3, 3, 4, 6, 7, 7, 0, 7]
w = zip (u,v)


#w = [(0,1),(0,1),(1,2),(1,3),(1,4),(1,5),(1,5),(1,6),(2,0),(2,0),(3,2),(3,2),(4,3),(4,7),(5,4),(5,9),(5,9),(6,7),(6,9),(7,3),(7,8),(8,1),(8,7),(9,6),(9,8)]

G.add_edges_from(w)

p = nx.is_strongly_connected(G)

print(p)

for i in G.edges():
    print("\n")
    for path in nx.all_simple_paths(G,source=i[0], target=i[1]):
       print(i) 
       print(path)
