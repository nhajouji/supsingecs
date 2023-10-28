################################
# Supersingular Isogeny Graphs #
################################



###############
# Import data #
###############

import pandas as pd

adf = pd.read_pickle('adf.pk')
dmcdf = pd.read_pickle('dmsCdf.pk')

supersingularprimes = list(adf['l'].values)


#############################
# Tools for computing in Fp #
#############################

square_root_dictionaries = {}
non_squares = {}
qrvs = {}

def qr(d,p):
    if p not in qrvs:
        qrv = [0,1]+[-1 for a in range(2,p)]
        for r in range(2,(p+1)//2):
            qrv[(r*r)%p]+=2
        qrvs[p] = qrv
    return qrvs[p][((d)%p)]

# The following function returns a dictionary indexed by elements of Fp,
# whose values are lists of square roots in Fp.
def sqrtdicmod(p):
    if p not in square_root_dictionaries:
        rtdic = {a:[] for a in range(p)}
        for a in range(p):
            rtdic[(a*a)%p].append(a)
        square_root_dictionaries[p] = rtdic
    return square_root_dictionaries[p]

# The following function picks a nonsquare in Fp that will be used
# to construct F_p^2.

def getnonsquare(p):
    if p in non_squares:
        return non_squares[p]
    heeg = [-1,-2,-3,-7,-11,-19,-43,-67,-163]
    dic = sqrtdicmod(p)
    for d in heeg:
        if len(dic[d%p])==0:
            non_squares[p]=d
            return d
    dic = sqrtdicmod(p)
    ns = -5
    while len(dic[ns%p])>0 and abs(ns)<p:
        ns-=2
    non_squares[p] = ns
    return ns


#######################
# Computing the trace #
#######################

def sqff(n):
    n0 = abs(n)
    m = 1
    s = n0//n
    while n0 % 4 == 0:
        n0 = n0//4
        m*=2
    while n0 % 9 == 0:
        n0 = n0//9
        m*=3
    d = 5
    e = 1
    while d*d <= n0:
        while n0 % (d*d) == 0:
            n0 = n0//(d*d)
            m*=d
        e*=-1
        d+=3+e
    dsc = s*n0
    if dsc % 4 != 1:
        dsc*=4
        m = m//2
    return (dsc,m)

def support(l):
    dms = []
    a = 0
    while a*a < 4*l:
        dms.append(sqff(a*a-4*l))
        a+=1
    return dms

def trace_coefs(l):
    sup = support(l)
    dcs = {dm[0]:0 for dm in sup}
    for dm in sup:
        dcs[dm[0]]+= list(dmcdf.loc[dmcdf.index==dm]['Count'].values)[0]
    if -3 in dcs:
        dcs[-3]-=2
    if -4 in dcs:
        dcs[-4]-=1
    for d in dcs:
        if d%l == 0:
            dcs[d]=dcs[d]//2
    return dcs

def trace_error(p,l):
    sup = support(l)
    error = 0
    badpairs = []
    for dm in sup:
        if dm[1]% p == 0 and qr(dm[0],p)!= 1:
            degorig = list(dmcdf.loc[dmcdf.index==dm]['Count'].values)[0]
            d = dm[0]
            m = dm[1]
            while m % p == 0:
                m = m//p
            degnew = list(dmcdf.loc[dmcdf.index==(d,m)]['Count'].values)[0]
            diff = degorig-degnew
            if d % p == 0:
                error+=diff
            else:
                error+=2*diff
    return error

def trace_pred(p,l):
    trcoefs = trace_coefs(l)
    tr = l
    for d in trcoefs:
        tr-=qr(d,p)*trcoefs[d]
    return tr-trace_error(p,l)
    

####################
# Computing in Fp2 #
####################

class EltFp2:
    # An element is described by specifying an integer n = a+bp and a prime p.
    # This represents us the element a + b sqrt(-d) in F_p^2.
    def __init__(self,n,p):
        self.char = p
        self.nonsquare = getnonsquare(p)
        self.proj1 = n % p
        self.proj2 = (n//p) % p
        self.vec = (self.proj1,self.proj2)
    def __repr__(self):
        p = self.char
        n = self.nonsquare
        a = self.proj1
        b = self.proj2
        if a == 0 and b == 0:
            return "0"
        elif a == 0:
            return str(b)+" sqrt("+str(n)+")"
        elif b == 0:
            return str(a)
        else:
            return str(a)+"+"+str(b)+" sqrt(" +str(n)+")"
    def __int__(self):
        return self.proj1+self.char*self.proj2

# We can add and multiply elements of Fp2.    
    def __add__(self,other):
        p = self.char
        a12 = (self.proj1 + other.proj1)%p
        b12 = (self.proj2 + other.proj2)%p
        return EltFp2(a12+p*b12,p)
    
    def __mul__(self,other):
        a1 = self.proj1
        a2 = other.proj1
        b1 = self.proj2
        b2 = other.proj2
        p = self.char
        ns = self.nonsquare
        a3 = (a1*a2+ns*b1*b2) % p
        b3 = (a1*b2+a2*b1) % p
        return EltFp2(a3+p*b3,p)
    
    def __rmul__(self,n):
        p = self.char
        scalar = EltFp2(n%p,p)
        return scalar*self
    
    def __neg__(self):
        return (-1)*self
    
    def __sub__(self,other):
        return self + (-other)
    
    def __pow__(self,n):
        if self.vec==(0,0):
            return self
        p = self.char
        e = n % (p*p-1)
        g2a = self
        ge = EltFp2(1,p)
        while e > 0:
            if e % 2 == 1:
                ge*= g2a
            g2a*= g2a
            e = e//2
        return ge

    def ev_quot(self,coefs):
        p = self.char
        cs = [c*EltFp2(1,p) for c in coefs[::-1]]
        qcs = [cs[0]]
        for c in cs[1:]:
            qcs.append(qcs[-1]*self+c)
        qcs = qcs[::-1]
        return [qcs[0],qcs[1:]]
        
    def ord_van(self,coefs):
        ev0 = self.ev_quot(coefs)
        ct = 0
        cs = coefs.copy()
        while len(cs)>1 and int(ev0[0])==0:
            ct+=1
            cs = ev0[1]
            ev0 = self.ev_quot(cs)
        return ct

    def eval_poly(self,coefs):
        p = self.char
        ev = EltFp2(0,p)
        for c in coefs[::-1]:
            ev*=self
            ev+= c * EltFp2(1,p)
        return ev

    def order_vanishing(self,coefs):
        p = self.char
        cs = coefs.copy()
        e = 0
        while len(cs)>int(self.eval_poly(cs))==0:
            e+=1
            cs = [i*cs[i] %p for i in range(1,len(cs))]
        return e
    
    def conj(self):
        a = self.proj1
        b = self.proj2
        p = self.char
        return EltFp2(a+(p-b)*p,p)

    def trace(self):
        return (self+self.conj()).proj1
    
    def norm(self):
        return (self*self.conj()).proj1
    
    def mult_inv(self):
        p = self.char
        n = self.norm()
        if n == 0:
            return 'Div by 0'
        else:
            return pow(n,-1,p)*(self.conj())
        
    def __floordiv__(self,den):
        return self*(den.mult_inv())
    

    def sqrts(self):
        nrm = self.norm()
        p = self.char
        d = self.nonsquare
        dic = sqrtdicmod(p)
        if len(dic[nrm])==0:
            return []
        a = self.proj1
        b = self.proj2
        if b == 0:
            if len(dic[a])>0:
                return [EltFp2(x,p) for x in dic[a]]
            else:
                adinv=(a*pow(d,-1,p))%p
                return [EltFp2(p*y,p) for y in dic[adinv]]
        else:
            rtnrm = dic[nrm][0]
            x2 = ((a+rtnrm)*((p+1)//2))%p
            if len(dic[x2])==0:
                x2 = ((a-rtnrm)*((p+1)//2))%p
            x1 = dic[x2][0]
            y1 = (b * pow(2*x1,-1,p))%p
            sqrt1 = EltFp2(x1+p*y1,p)
            sqrt2 = (-1)*sqrt1
            return [sqrt1,sqrt2]

# The following function returns the roots of a quadratic polynomial.

# Input: a pair (a,b), where a, b are elements of F_p^2.
# Output: The set of roots of x^2 + a x + b = 0 in F_p^2.

def quad_roots(ab):
    a = ab[0]
    b = ab[1]
    d = a*a-4*b
    rtsd = d.sqrts()
    return [pow(2,-1,a.char)*(r-a) for r in rtsd]
    


#########################
# 2-isogeny computation #
#########################

#j_invariant_ab computes j-invariants of elliptic curves with a 2-torsion point

# Input: a pair (a,b), where a, b are elements of F_p^2.
# Output: The j-invariant of y^2 = x(x^2+ax + b)
def j_invariant_ab(ab):
    a = ab[0]
    b = ab[1]
    return 256*((a*a-3*b)**3)//((a*a-4*b)*b*b)

# two_iso_abs computes models of all curves which are 2-isogenous
# to a given curve.

# Input: a pair (a,b), where a, b are elements of F_p^2, that represents
#        the curve y^2 = x(x^2 + ax b)

# Output: A list [(a1,b1),(a2,b2),(a3,b3)], where each pair (ai,bi) represents
#        a curve given by an equation of the same form, which is 2-isogenous
#        to the original curve

def two_iso_abs(ab):
    a0 = ab[0]
    b0 = ab[1]
    ab0s = [ab]
    rs = quad_roots(ab)
    for r in rs:
        ar = a0+3*r
        br = (ar+a0)*r+b0
        ab0s.append((ar,br))
    isocoefs = [((-2)*cs[0],cs[0]**2-4*cs[1]) for cs in ab0s]
    return isocoefs

# findSSab finds a model of some supersingular curve with a 2-torsion point.

# Input: A prime p
# Output: A pair (a,b), where a, b are integers, that represent the s.s.e.c.:
#         y^2 = x(x^2 + ax + b)

def findSSab(p):
    # If p is 3 mod 4, then j = 1728 is supersingular, so we return (0,1)
    if p % 4 == 3:
        return (0,1)
    # Otherwise, we will look for an equation of the form y^2 = (x-a)(x^2-ns)
    # where ns is a nonsquare, which represents a ssec.
    # We will need information about squares in various forms, so we collect all
    # this information to begin.
    sqrtdic = sqrtdicmod(p)
    qrs = [-1+len(sqrtdic[a]) for a in range(p)]
    ns = getnonsquare(p)
    # We construct a vector vns whose ith entry is (i^2 - ns)^(p-1)/2
    vns= [qrs[(a*a-ns)%p] for a in range(p)]
    for a in range(p):
        # We compute the dot product of vns and wa,
        # where wa is the vector whose ith entry is 1 if i-a is a square,
        # 0 if i= a, -1 if i-a is not a square.
        # The value of this dot product is equal to the trace of Frobenius
        # acting on y^2 = (x-a)(x^2-ns), so this equation is ss iff
        # the dot product is 0.
        tr = sum([vns[i]*qrs[(i+a)%p] for i in range(p)])
        if tr == 0:
            return ((2*a)%p,(a*a-ns)%p)
    return 'Not found'


# two_iso_graph uses the preceding functions to obtain the full 2-isogeny
# graph.
# It is used in the initialization of the SupSingGraphs class to obtain
# the set of supersingular j-invariants.

# Input: A prime p
# Output: A dictionary representing the 2-isogeny graph mod p.
#         The keys are supersingular j-invariants.
#        The value associated to each j_0 in the dictionary
#        is a list containing 3 j-invariants j_1,j_2,j_3,
#        which means the graph contains edges j_0 -> j_1, j_0 -> j_2, j_0->j_3


def two_iso_graph(p):
    dic = sqrtdicmod(p)
    ab_int = findSSab(p)
    ab = (ab_int[0]*EltFp2(1,p),ab_int[1]*EltFp2(1,p))
    models = [ab]
    edges = {}
    checked = []
    while len(models)>0:
        newmodels = []
        for ab0 in models:
            j0 = j_invariant_ab(ab0)
            if j0.vec not in checked:
                ab1s = two_iso_abs(ab0)
                edges[j0] = [j_invariant_ab(ab1) for ab1 in ab1s]
                newmodels+=ab1s
                checked.append(j0.vec)
        models = newmodels
    return edges

# graph2mat takes as input a dictionary, which represents an isogeny graph
# as above, and returns an adjacency matrix representing that graph.

# Input: A dictionary representing an l-isogeny graph.
# Output: The adjacency matrix

# Note: the keys are should be integers, and the values should be lists of integers
# whose elements all belong to the set of keys.

def graph2mat(g):
    js = list(g.keys())
    jis = {js[i]:i for i in range(len(js))}
    mat = []
    for j1 in js:
        jr = [0 for j in js]
        for j2 in g[j1]:
            jr[jis[j2]]+=1
        mat.append(jr)
    return mat

########
# Main #
########

class SupSingGraphs:
    def __init__(self,p):
        self.char = p
        self.g2 = two_iso_graph(p)
    def __repr__(self):
        p = self.char
        return 'Information about supersingular graphs in characteristic '+str(p)

    def j_invariants(self):
        return list((self.g2).keys())

    # The following function computes the l-isogeny graph using the Atkin modular
    # polynomials.

    # Input: A supersingular prime l
    # Out: The l-isogeny grah

    def isogeny_graph(self,l):
        p = self.char
        if l not in supersingularprimes:
            return 'Not found'
        p = self.char
        js = self.j_invariants()
        coefdic = {int(js[i1]*js[i2]):{}
                   for i1 in range(len(js)-1) for i2 in range(i1+1,len(js))}
        for i1 in range(len(js)-1):
            j1 = js[i1]
            for i2 in range(i1+1,len(js)):
                j2 = js[i2]
                coefdic[int(j1*j2)][int(j1+j2)] = [j1,j2]
        gr = {int(j):[] for j in js}
        ac = list((adf.loc[adf.l==l])['a_coefs'].values)[0]
        b1c = list((adf.loc[adf.l==l])['b_coefs1'].values)[0]
        b3c = list((adf.loc[adf.l==l])['b_coefs3'].values)[0]
        for yi in range(p*p):
            y = EltFp2(yi,p)
            by = (y.eval_poly(b1c)*(y.eval_poly(b3c)**3))
            if int(by) in coefdic:
                ay = y.eval_poly(ac)
                if int(ay) in coefdic[int(by)]:
                    xys = coefdic[int(by)][int(ay)]
                    e0 = 1
                    e1 = 1
                    if int(xys[0])== 0:
                        e0 = 3
                    elif int(xys[0])==1728%p:
                        e0 = 2
                    if int(xys[1]) == 0:
                        e1 = 3
                    elif int(xys[1]) == 1728%p:
                        e1 = 2
                    gr[int(xys[0])]+= e0* [int(xys[1])]
                    gr[int(xys[1])]+= e1* [int(xys[0])]
        for jn in gr:
            gr[jn]+=(l+1-len(gr[jn]))*[jn]
        return gr

    def adj_matrix(self,l):
        if l not in supersingularprimes:
            return 'Not found'
        else:
            return graph2mat(self.isogeny_graph(l))
