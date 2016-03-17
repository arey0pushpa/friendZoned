import networkx as nx

G = nx.Graph()




#u = [0, 0, 0, 1, 1, 1, 1, 2, 2, 2, 3, 3, 3, 4, 4, 5, 5, 6, 6, 7]
#v = [3, 4, 5, 0, 4, 5, 6, 1, 6, 7, 1, 7, 9, 6, 8, 4, 6, 5, 9, 9]

#w = zip(u,v)



w =  [(0,1),(0,3),(0,4) ,(1,0), (1,4),(2,1), (3,1),(3,2),(4,2),(4,3)]
G.add_edges_from(w)

#b1  = nx.is_strongly_connected(G)
b2 = nx.is_biconnected(G)


#print(b1)
print(b2)

#basis = nx.simple_cycles(G)
#k = 0
#for i in basis :
#    k = k + 1
#    print(i)
    
#print("# elementary cycles are : ", k)





