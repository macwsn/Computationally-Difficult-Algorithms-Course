import random, time
from collections import deque
DR=[-1,0,1,0]; DC=[0,1,0,-1]
SLASH=[1,0,3,2]; BACKSLASH=[3,2,1,0]
BS=chr(92); MIRR=set(['/',BS])
def reflect(d,m): return SLASH[d] if m=='/' else BACKSLASH[d]

def inb(r,c):return 0<=r<H and 0<=c<W
def lasers_of(g):
    o=[]
    for i in range(W*H):
        ch=g[i];r,c=i//W,i%W
        if ch=='>':o.append((r,c,1))
        elif ch=='A':o.append((r,c,0))
        elif ch=='V':o.append((r,c,2))
        elif ch=='<':o.append((r,c,3))
    return o
def trace_lit(g):
    lit=bytearray(W*H);vis=set()
    for(lr,lc,ld)in lasers_of(g):
        r,c,d=lr+DR[ld],lc+DC[ld],ld
        while 0<=r<H and 0<=c<W:
            idx=r*W+c;vi=(idx<<2)|d
            if vi in vis:break
            vis.add(vi);ch=g[idx]
            if ch=='#':break
            if ch=='O':lit[idx]=1
            if ch in MIRR:d=reflect(d,ch)
            r+=DR[d];c+=DC[d]
    return lit
def crit(g):
    bl=bytearray(W*H)
    for(lr,lc,ld)in lasers_of(g):
        path=[];vis=set();r,c,d=lr+DR[ld],lc+DC[ld],ld;lastO=-1
        while 0<=r<H and 0<=c<W:
            idx=r*W+c;vi=(idx<<2)|d
            if vi in vis:break
            vis.add(vi);ch=g[idx]
            if ch=='#':break
            path.append(idx)
            if ch=='O':lastO=len(path)-1
            if ch in MIRR:d=reflect(d,ch)
            r+=DR[d];c+=DC[d]
        for k in range(lastO+1):bl[path[k]]=1
    return bl
def bfs(g,budget,onlyTarget=-1):
    isT=bytearray(1 if g[i]=='O' else 0 for i in range(W*H));lit=trace_lit(g);bl=crit(g)
    INF=10**9;dist={};par={};mirAt={};done=set();dq=deque()
    def enc(r,c,d):return((r*W+c)<<2)|d
    for(lr,lc,ld)in lasers_of(g):
        r0,c0=lr+DR[ld],lc+DC[ld]
        if not inb(r0,c0):continue
        if g[r0*W+c0]=='#':continue
        e=enc(r0,c0,ld)
        if dist.get(e,INF)!=0:dist[e]=0;par[e]=-1;mirAt[e]=0;dq.appendleft((0,e))
    def relax(ne,nc,pe,mir,cur):
        if nc<dist.get(ne,INF):
            dist[ne]=nc;par[ne]=pe;mirAt[ne]=mir
            (dq.appendleft if nc==cur else dq.append)((nc,ne))
    while dq:
        cost,e=dq.popleft()
        if e in done:continue
        if cost!=dist.get(e,INF):continue
        done.add(e);idx=e>>2;d=e&3;r=idx//W;c=idx%W;ch=g[idx]
        if ch=='#':continue
        if isT[idx] and not lit[idx] and cost<=budget and (onlyTarget<0 or idx==onlyTarget):
            added=0;cur=e
            while cur!=-1:
                m=mirAt[cur]
                if m:
                    pe=par[cur];pidx=pe>>2
                    if g[pidx]=='.':g[pidx]=m;added+=1
                cur=par[cur]
            return idx,added
        if ch in MIRR:
            nd=reflect(d,ch);nr,nc2=r+DR[nd],c+DC[nd]
            if inb(nr,nc2)and g[nr*W+nc2]!='#':relax(enc(nr,nc2,nd),cost,e,0,cost)
        else:
            nr,nc2=r+DR[d],c+DC[d]
            if inb(nr,nc2)and g[nr*W+nc2]!='#':relax(enc(nr,nc2,d),cost,e,0,cost)
            if ch=='.' and not bl[idx] and cost<budget:
                for mir in['/',BS]:
                    nd=reflect(d,mir);mr,mc=r+DR[nd],c+DC[nd]
                    if inb(mr,mc)and g[mr*W+mc]!='#':relax(enc(mr,mc,nd),cost+1,e,mir,cost)
    return -1,0
def clit(g,T):lit=trace_lit(g);return sum(1 for t in T if lit[t])
def greedy_pass(L,dl,T,nT):
    global g
    used=sum(1 for ch in g if ch in MIRR)
    for it in range(nT*2+8):
        if time.time()>dl:break
        lit=trace_lit(g);pl=sum(1 for t in T if lit[t])
        if pl==nT:return True
        budget=L-used
        if budget<0:break
        snap=g[:];found,added=bfs(g,budget)
        if found<0:break
        if used+added>L:g=snap;break
        if added==0:g=snap;break
        nl=clit(g,T)
        if nl<=pl:g=snap;break
        used+=added
    return clit(g,T)==nT
def solve(L,dl):
    global g
    T=[i for i in range(W*H) if g[i]=='O'];nT=len(T)
    if nT==0:return True,nT
    greedy_pass(L,dl,T,nT)
    # faza dogrywki: probuj oswietlic kazdy nieoswietlony cel osobno (onlyTarget),
    # co pozwala przekierowac promienie do trudnych celow.
    bestG=g[:];bestLit=clit(g,T)
    while time.time()<dl:
        lit=trace_lit(g)
        unlit=[t for t in T if not lit[t]]
        if not unlit:break
        progress=False
        for tgt in unlit:
            if time.time()>dl:break
            used=sum(1 for ch in g if ch in MIRR);budget=L-used
            if budget<0:break
            snap=g[:];found,added=bfs(g,budget,onlyTarget=tgt)
            if found<0:g=snap;continue
            nl=clit(g,T)
            if nl<=bestLit:g=snap;continue
            bestLit=nl;bestG=g[:];progress=True
        if not progress:break
    g=bestG;return bestLit==nT,bestLit

random.seed(42)
W=H=100
# Random board: some lasers, walls, targets
g=['.']*(W*H)
nL=50; nT=200; nWall=500
cells=random.sample(range(W*H),nL+nT+nWall)
i=0
for _ in range(nL): g[cells[i]]=random.choice(['A','V','<','>']);i+=1
for _ in range(nT): g[cells[i]]='O';i+=1
for _ in range(nWall): g[cells[i]]='#';i+=1
T=[k for k in range(W*H) if g[k]=='O']
print("board 100x100, lasers=%d targets=%d walls=%d L=200"%(nL,len(T),nWall))
t0=time.time()
ok,lit=solve(200, t0+30)
print("time=%.2fs solved=%s lit=%d/%d"%(time.time()-t0,ok,lit,len(T)))
