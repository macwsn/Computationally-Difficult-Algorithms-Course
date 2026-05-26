import random
# Buduj rozwiazywalna plansze: dla kazdego celu wytycz sciezke od jakiegos lasera.
# Prosto: postaw lasery na brzegach strzelajace w glab, cele na ich liniach (0 luster),
# plus kilka celow wymagajacych 1 odbicia.
def gen(W,H,seed):
    random.seed(seed)
    g=[['.' ]*W for _ in range(H)]
    targets=[]
    lasers=[]
    # lasery z lewej krawedzi strzelajace w prawo, cel gdzies na linii
    rows=random.sample(range(H), min(H, 30))
    for r in rows:
        g[r][0]='>'
        # cel na tej linii
        c=random.randint(2,W-1)
        if g[r][c]=='.':
            g[r][c]='O'
    # lasery z gory strzelajace w dol
    cols=random.sample(range(1,W), min(W-1, 30))
    for c in cols:
        if g[0][c]=='.':
            g[0][c]='V'
            r=random.randint(2,H-1)
            if g[r][c]=='.':
                g[r][c]='O'
    return g
if __name__=='__main__':
    W,H=100,100
    g=gen(W,H,1)
    nO=sum(row.count('O') for row in g)
    nL=sum(sum(1 for ch in row if ch in 'AV<>') for row in g)
    print(W,H,nO+5)  # L = liczba celow + zapas
    for row in g:print(''.join(row))
