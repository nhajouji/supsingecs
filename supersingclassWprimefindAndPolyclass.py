# The following program takes as input a prime p,
# and returns a list of supersingular j values.

# getPrimesUpTo(m) takes an integer m as input,
# and returns a list of all primes <= m.

def getPrimesUp2(m):
    if m < 2:
        return []
    elif m == 2:
        return [2]
    elif m == 3:
        return [2,3]
    cands = [0,0,1]+[(i % 2) for i in range(3,m+1)]
    for a in range(9,m+1,3):
        cands[a] = 0
    e = -1
    p = 5
    while p**2 <= m:
        for pm in range(p**2,m+1,p):
            cands[pm]=0
        p+=3+e
        e*=-1
        while cands[p] == 0:
            p+=3+e
            e*=-1
    primes = [a for a in range(m+1) if cands[a] == 1]
    return primes

# We will be working in F_p^2, so we will construct a class that represents
# elements in that field

# First, we need tools for doing arithmetic in Fp.
# Most of these are already built in - we just need a way of dividing elements.

# To divide in F_p, we essentially need to be able to solve the diophantine eq
# ax+by = 1 for x,y. We can do this using the Euclidean algorithm.

# The function axbySolve produces x,y such that ax+by is the gcd of a,b.
# Note that a,b are assumed to be positive in the code for axbySolve.

# magicBox0 will translate data obtained from the Euclidean algorithm
# into data needed to find x,y
# This function is only called by axbySolve
def magicBox0(last4,a2):
    n0 = last4[0][0]
    n1 = last4[1][0]
    d0 = last4[0][1]
    d1 = last4[1][1]
    n2 = a2*n1+n0
    d2 = a2*d1+d0
    newlast4 = [last4[1],[n2,d2]]
    return newlast4

# axbySolve takes a pair of integers a,b,
# which are assumed to be positive,
# and returns a pair of integers x,y that satisfy ax+by = gcd(a,b)

def axbySolve(a,b):
    m = min(a,b)
    n = max(a,b)
    lst4 = [[0,1],[1,0]]
    while n % m !=0:
        q = n//m
        r = n % m
        lst4 = magicBox0(lst4,q)
        newn = m
        newm = r
        n = newn
        m = newm
    q = n//m
    lst4 = magicBox0(lst4,q)
    xy = lst4[0]
    if a<b:
        if xy[0]*a>xy[1]*b:
            return [xy[0],-xy[1]]
        else:
            return [-xy[0],xy[1]]
    elif xy[0]*b>xy[1]*a:
        return [-xy[1],xy[0]]
    else:
        return [xy[1],-xy[0]]

# The following function takes as input an integer a and a prime p,
# an integer b such that ab is congruent to 1 mod p.


# invMod takes as input an integer a and a prime p, and
# returns an integer x that satisfies ax = 1 mod p.
# The inverse is computed using axbySolve.
# If a is congruent to 0 mod p, the function returns the string '1/0'
def invMod(a,p):
    if a % p == 0:
        return '1/0'
    xy = axbySolve(a,p)
    return xy[0] %p

# We now construct a class representing elements of Fp2.
# An element of Fp2 looks like a + b sqrt(ns), where a, b are elements of Fp
# and ns is a nonzero element of Fp that does not have a square root in Fp.

# To describe an element in a field Fp2, we need to specify:
# The prime p, a nonsquare ns, and the two coefficients a,b
# This data represents the element a + b sqrt(ns) in Fp2.

def fp2str(a,b,n):
    if a == 0 and b == 0:
            return "0"
    elif a == 0:
        return str(b)+" sqrt("+str(n)+")"
    elif b == 0:
        return str(a)
    else:
        return str(a)+"+"+str(b)+" sqrt(" +str(n)+")"



class ElementFp2:
# The class is initialized by specifying the 4 integers (p, ns, a, b).
    def __init__(self,p,n,a,b):
        self.char = p
        self.nonsquare = n
        self.proj1 = a % p
        self.proj2 = b % p
        self.vec = (a%p,b%p)
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
# Two elements of Fp2 should be considered equal if the characteristic
# and nonsquare coincide, and the coefficients coincide mod p.
    def __eq__(self,other):
        p1 = self.char
        p2 = other.char
        if p1!=p2:
            return False
        ns1 = self.nonsquare
        ns2 = other.nonsquare
        if ns1!=ns2:
            return False
        a1 = self.proj1
        a2 = other.proj1
        b1 = self.proj2
        b2 = other.proj2
        return ((a1-a2)%p1==0) and ((b1-b2)%p1==0) 

# We can add and multiply elements of Fp2.    
    def __add__(self,other):
        a1 = self.proj1
        a2 = other.proj1
        b1 = self.proj2
        b2 = other.proj2
        p = self.char
        ns = self.nonsquare
        return ElementFp2(p,ns,(a1+a2) % p, (b1+b2)%p)
    
    def __mul__(self,other):
        a1 = self.proj1
        a2 = other.proj1
        b1 = self.proj2
        b2 = other.proj2
        p = self.char
        ns = self.nonsquare
        a3 = (a1*a2+ns*b1*b2) % p
        b3 = (a1*b2+a2*b1) % p
        return ElementFp2(p,ns,a3,b3)
# Given an element x in Fp2 and an integer c,
# we can compute the scalar multiple cx by x.scale(c)
    def scale(self,c):
        p = self.char
        ns = self.nonsquare
        cfp2 = ElementFp2(p,ns,c,0)
        return self*cfp2
# We can subtract elements.
# Subtraction is implemented by combining addition and scalar multiplication
    def __sub__(self,other):
        return self + other.scale(-1)
# x.conj() returns the Galois conjugate of x    
    def conj(self):
        a = self.proj1
        b = self.proj2
        p = self.char
        ns = self.nonsquare
        return ElementFp2(p,ns, a, p-b)
# x.norm() computes the norm of x by multiplying x and x.conj().
# Note: The output of x.norm() will be an integer, NOT an element of Fp2
    def norm(self):
        cnj = self.conj()
        n2 = self*cnj
        return n2.proj1
    
# x.multInv() returns the multiplicative inverse of x.
# The norm and conjugate of x are computed.
# The multiplicative inverse of the norm is computed using invMod,
# and the inverse of x is then computed by rescaling the conjugate of x
# by the inverse of the norm of x.
    def multInv(self):
        cnj = self.conj()
        nrm2 = self*cnj
        n = nrm2.proj1
        p = self.char
        ninv = invMod(n,p)
        rec = cnj.scale(ninv)
        return rec

    def inFp(self):
        b = self.proj2
        return b==0

# x.minPoly('t') returns the minimal polynomial of x over Fp, in the variable t.
# If x is in Fp, then the minimal polynomial of x will be the string 't-x'
# Otherwise, the minimal polynomial will be a string of the form 't^2+at +b'
# where a is negative of the trace of x and b is the norm.

    def minPoly(self,x):
        p = self.char
        a = self.proj1
        b = self.proj2
        if b == 0:
            return x+'-'+str(a)
        else:
            c0 = self.norm()
            c1 = (-2*self.proj1)%p
            return x+"^2+"+str(c1)+x+'+'+str(c0)

    

# To solve quadratic equations, we need to be able to compute square roots.

# genSqrtDic takes as input a prime p and an integer d.
# The function assumes that d is a nonresidue mod p,
# and returns a dictionary whose keys are tuples of integers (a,b),
# and where the value of (a,b) is the set of square roots of a+b sqrt(d)
# in the field F_p^2. The square roots are represented as elements of Fp2.

def genSqrtDic(p,d):
    dic = {(a,b):[] for a in range(p) for b in range(p)}
    for a in range(p):
        for b in range(p):
            rt = ElementFp2(p,d,a,b)
            dic[(rt*rt).vec].append(rt)
    return dic

# solveQuadratic takes as input a tuple ab = (a,b), where a, b are in Fp2.
# Note that a,b should be defined using the same nonsquare ns in Fp2.
# The pair ab represents a quadratic eqution x^2 + ax + b =0.
# We also need a dictionary, which should be obtained using genSqrtDic(p,ns),
# where ns is the same nonsquare used to define a and b.
# The function assumes that the keys of dic are tuples (a0,b0) that represent
# a0+b0 sqrt(ns) in Fp2, and the value of (a0,b0) is a list of elements in Fp2
# that square to a0+b0 sqrt(ns).
# The output of solveQuadratic is a list of the roots of the quadratic equation.

def solveQuadratic(ab,dic):
    a = ab[0]
    b = ab[1]
    p = a.char
    half = (p+1)//2
    d = disc(ab)
    rtds = dic[d.vec]
    rtsab = [(r-a).scale(half) for r in rtds]
    return rtsab


# Elliptic curves

# All curves will be represented by equations of the form y^2 = x(x^2+ax+b)
# To describe a curve, we specify the coefficients (a,b) as a tuple of length 2.
# The coefficients are assumed to be elements of Fp2.

# For such a pair, we compute the discriminant and j-invariant using disc/jInv:

def disc(ab):
    a = ab[0]
    b = ab[1]
    return a*a+b.scale(-4)

def jInv(ab):
    a = ab[0]
    b = ab[1]
    num = ((a*a-b.scale(3))*(a*a-b.scale(3))*(a*a-b.scale(3))).scale(256)
    den = b*b*disc(ab)
    return num*(den.multInv())

# weirCoefsFrom2tor computes "short Weierstrass coefficients" from a pair (a,b).
# This is not needed in any of the current code, but may be useful in the future.


def jFromFG(fg):
    f = fg[0]
    g = fg[1]
    f2 = f*f
    f3 = f2*f
    num = f3.scale(4*1728)
    d = f3.scale(4)+g*g.scale(27)
    den = d.multInv()
    return num * den

# For a given curve, there are three pairs (a,b) we need to use.
# If we have one pair (a,b), we can obtain the other two pairs by:

# First, solving the quadratic equation x^2 + ax + b.
# There will be two solutions, r1 and r2.

# Second, we do a change of variable xi <-> x+ri to the cubic x(x^2+ax+b).
# This gives us two new equations xi(xi^2 + ai xi + bi).

# The function allPairs will take as input a pair (a,b),
# and return a list containing all 3 pairs needed.

# Since we need to solve quadratic equations, we also need a square root dict.

def allPairs(ab,dic):
    rts = solveQuadratic(ab,dic)
    r0 = rts[0]
    r1 = rts[1]
    a0 = r0.scale(2)-r1
    b0 = r0 *(r0-r1)
    a1 = r1.scale(2)-r0
    b1 = r1 * (r1 - r0)
    return [ab, (a0,b0), (a1,b1)]


# twoIsog takes as input a pair (a,b) that represents an elliptic curve,
# and produces a new pair of the same type
# that represents the 2-isogenous curve.

def twoIsog(ab):
    a = ab[0]
    b = ab[1]
    a2 = a.scale(-2)
    b2 = disc(ab)
    return (a2,b2)


# twoIsogenyGraph

# ab2graphDic takes as input an pair ab0 = (a0,b0) that represents
# an equation for a supersingular curve of the form y^2 = x(x^2 + a0 x + b0)
# and a dictionary of square roots.
# The function computes the 2-isogeny graph from this data,
# and returns a dictionary whose keys are the supersingular j-invariants,
# encoded as tuples of integers, and the value associated to each key is
# a set containing the endpoints of the three edges leaving that vertex.

# To use ab2GraphsAndModels, we need a pair ab0 and a dictionary.
# The pair ab0 = (a0,b0) should be a tuple of elements of Fp2,
# that represents a supersingular curve given by an equation:
# y^2  = x^3 + a0 x + b0.
# The dictionary should take as input pairs (c0,c1) of elements in Fp,
# that represents an element of Fp2, and should return a list of
# the square roots of (c0,c1) in Fp2. The square roots should be elements of Fp2.

# The dictionary and the pair ab0 should be expressed relative to the same
# nonsquare; this function is used when the class supSingFp2 is initialized.
# getMatJsNSsqrtD finds a nonsquare, which it uses to obtain ab0,
# and then generates a dictionary of square roots in terms of that nonsquare.
# This will ensure the pair is compatible.

def ab2GraphsAndModels(ab0,dic):
    js = []
    eqs = [ab0]
    graph = {}
    models = {}
    while len(eqs) > 0:
        neweqs = []
        for ab in eqs:
            jab = jInv(ab).vec
            if jab not in js:
                js.append(jab)
                jabModels = allPairs(ab,dic)
                ab2s = [twoIsog(ab1) for ab1 in jabModels]
                jab2s = [jInv(ab2).vec for ab2 in ab2s]
                graph.update({jab:jab2s})
                models.update({jab:jabModels})
                for i in [0,1,2]:
                    if jab2s[i] not in js:
                        neweqs.append(ab2s[i])
        eqs = neweqs
    return [graph,models]


# To start the main algorithm, we need to find a suitable nonsquare in Fp.
# A nonsquare is suitable if and only if it appears in the following list:

nonSquares = [-1,-2,-3,-7,-11,-19,-43,-67,-163]

# For any odd prime p < 15073, one of those integers is a guaranteed to work.

# chooseNonSquare takes as input a prime p,
# and returns a suitable nonsquare if one exists.
# To determine whether integers are squares, we use quadratic reciprocity.
# If a nonsquare can't be found in the list, an error message is returned.
def chooseNonSquare(p):
    if p % 4 == 3:
        return -1
    elif p % 3 == 2:
        return -3
    elif p % 8 == 5:
        return -2
    for d in [-7,-11,-19,-43,-67,-163]:
        q = -d
        sqs = [a**2 % q for a in range(1,(q+1)//2)]
        p0 = p % q
        if p0 not in sqs:
            return d
    return "Couldn't find one - make sure p is an odd prime, and p < 15073 "

# The nonsquare we obtained will determine our starting elliptic curve.
# If the nonsquare is -1,-2,-3 or -7, the corresponding elliptic curve
# can be described by an equation y^2 = x(x^2 + ax + b) with a,b in Z.
# As a result, we do not have to do any additonal work to obtain (a,b).

# If the nonsquare is -11, -19, -43, -67, -163, the elliptic curve we will use
# does not have 2-torsion over Z, so we will have to start with a pair
# fg = (f,g), where f, g are integers representing y^2 = x^3 + fx + g.
# The cubic x^3 + fx + g does not have a root in Z, but will have one in Z/p.
# To obtain (a,b), we simply need to find a root of r of x^3 + fx + g.
# The coefficients a,b can be obtained from r, f, g.

fgs=[(-264,1694),(-152,722),(-3440,77658),(-29480,1948226),(-8697680,9873093538)]
fgDic = {nonSquares[4+i]:fgs[i] for i in range(5)}

#evCubic takes as input a pair fg = (f,g), an integer x and a prime p,
#and returns the value x^3 + fx +g mod p.

def evCubic(fg,x,p):
    f = fg[0]
    g = fg[1]
    return ((x**3)+f*x+g) % p

# findCoefs0 takes p as an input,
# uses chooseNonSquare to find a suitable nonsquare d.
# If d = -1,-2,-3 or -7, findCoefs returns a pair of integers (a,b)
# such that y^2 = x(x^2+ax +b) is supersingular.
# If d is not one of those values, findCoefs0 checks fgDic for coefficients
# (f,g) representing an elliptic curve y^2 = x^3 + fx + g.
# The program then uses evCubic to search for a solution to the cubic;
# once a solution is found, the program computes a change of variable
# to produce a suitable pair (a,b).

def findCoefs0(p):
    d = chooseNonSquare(p)
    if d == -1:
        return (ElementFp2(p,-1,0,0),ElementFp2(p,-1,-1,0))
    elif d == -3:
        return (ElementFp2(p,-3,3,0),ElementFp2(p,-3,3,0))
    elif d == -2:
        return (ElementFp2(p,-2,4,0),ElementFp2(p,-2,2,0))
    elif d == -7:
        return (ElementFp2(p,-7,-21,0),ElementFp2(p,-7,112,0))
    else:
        fg = fgDic[d]
        f = fg[0]
        x= 0
        while x < p and evCubic(fg,x,p)!= 0:
            x+=1
        if x == p:
            return "No 2-torsion found"
        else:
            return (ElementFp2(p,d,(3*x)%p,0),ElementFp2(p,d,(3*x*x+f)%p,0))

# We now have everything in place.
# superSingularJs takes as input a prime p,
# uses findCoefs0 to obtain a pair (a,b) that represents a supersingular curve,
# then uses ab2alljs to obtain all j-invariants from the pair (a,b).

def getMatJsNSsqrtD(p):
    ab0 = findCoefs0(p)
    d = ab0[0].nonsquare
    sqrtdic = genSqrtDic(p,d)
    graphmodel = ab2GraphsAndModels(ab0,sqrtdic)
    graph = graphmodel[0]
    models = graphmodel[1]
    js = list(graph.keys())
    js.sort(key = lambda x:x[0]+p*min(x[1],p-x[1]))
    nojs = len(js)
    idic = {js[i]:i for i in range(nojs)}
    mat = []
    for i in range(nojs):
        ji = js[i]
        endpts = graph[ji]
        endptis = [idic[j] for j in endpts]
        row = [0] * nojs
        for k in endptis:
            row[k]+=1
        mat.append(row)
    return [mat,js,d,models,sqrtdic]

# Creating an element in class supSingFp2 runs getMatJsNSsqrtD(p)
# to compute the 2-isogeny graph and collect all the data obtained.
# Once the class is initialized, the j-invariants, models, etc. are easily
# obtained from the data we just obtained, without having to repeat the initial
# long computation.

def fgFromjFp2(j):
    p = j.char
    if j.vec == (0,0):
        return (ElementFp2(p,j.nonsquare,0,0),ElementFp2(p,j.nonsquare,1,0))
    elif j.proj1 == 1728 % p and j.proj2 == 0:
        return (ElementFp2(p,j.nonsquare,-1,0),ElementFp2(p,j.nonsquare,0,0))
    else:
        fnum = j.scale(27%p)
        gnum = j.scale(54%p)
        den = ElementFp2(p,j.nonsquare,1728,0)-j
        deninv = den.multInv()
        return (fnum*deninv,gnum*deninv)


class supSingFp2:
# Computes the 2-isogeny graph using getMatJsNSsqrtD;
# the data can be accessed in the future as self.rawdata
# without needing to repeat the initial computation.
    def __init__(self,p):
        self.char = p
        self.rawdata = getMatJsNSsqrtD(p)
    def __repr__(self):
        p = self.char
        return "Data about supersingular curves in characteristic "+str(p)
# self.js() converts the j-invariants in rawdata to elements of Fp2
# and returns a list containing the result
    def js(self):
        data = self.rawdata
        d = data[2]
        p = self.char
        jpairs = data[1]
        return [ElementFp2(p,d,ab[0],ab[1]) for ab in jpairs]
# self.twoIsogMat() returns the adjacency matrix of the 2-isogeny graph
    def twoIsogMat(self):
        data = self.rawdata
        return data[0]
# self.twoTorModels(j) returns a list containing 3 pairs (a,b)
# that can be used to represent the elliptic curve with given j-invariant.
# These models were obtained during the computation of the 2-isogeny graph;
    def twoTorModels(self,j):
        data = self.rawdata
        return data[3][j.vec]
# self.fgs() returns the set of (f,g)'s for all possible j-invariants.
    def fgs(self):
        j0s = self.js()
        return [fgFromjFp2(j) for j in j0s]
# self.jPolyFacs('x') returns a set of minimal polynomials of j-invariants
# in the variable 'x'.
    def jPolyFacs(self,x):
        js = self.js()
        p = self.char
        facs = []
        for j in js:
            if 2*(j.proj2)<p:
                facs.append(j.minPoly(x))
        return facs
# self.jPoly('x') is similar to jPolyFacs, but returns the product of the
# factors as a single string.
    def jPoly(self,x):
        pfs = self.jPolyFacs(x)
        p1 = ''
        p2 = ''
        for f in  pfs:
            if len(f) == 1:
                p1 = f+ p1
            elif f[1] != '^':
                p1+='('+f+')'
            else:
                p2+='('+f+')'
        return p1+p2
 



# Polynomials

def remLeadZerosFp2(l):
    if l[-1].vec != (0,0):
        return l
    p = l[0].char
    while len(l) >1 and l[-1].vec == (0,0):
        l = l[:-1]
    return l
    
def degFp2(l):
    l0 = remLeadZerosFp2(l)
    p = l0[-1].char
    if len(l0) > 1:
        return len(l0)-1
    elif l0[0].norm() %p == 0:
        return -1
    else:
        return 0

def xnFp2(p,ns,x,n):
        c1 = ElementFp2(p,ns,1,0)
        cs = [ElementFp2(p,ns,0,0)]*n+[c1]
        return PolyFp2(p,ns,cs,x)
    
class PolyFp2:
    def __init__(self,p,ns,cs,x = 'x'):
        cs0 = remLeadZerosFp2(cs)
        self.char = p
        self.nonsquare = ns
        self.var = x
        self.coefs = cs0
        self.deg = degFp2(cs0)
        self.leadCoef = cs0[-1]
    def __repr__(self):
        cs = self.coefs
        x = self.var
        ns = cs[0].nonsquare
        polystr = fp2str(cs[0].proj1,cs[0].proj2,ns)
        if len(cs)==1:
            return polystr
        polystr +='+'+fp2str(cs[1].proj1,cs[1].proj2,ns)+x
        if len(cs)==2:
            return polystr
        for i in range(2,len(cs)):
            polystr+='+'+fp2str(cs[i].proj1,cs[i].proj2,ns)+x+'^'+str(i)        
        return polystr
    def __add__(self,other):
        p = self.char
        ns = self.nonsquare
        cs1 = self.coefs
        cs2 = other.coefs
        x = self.var
        if len(cs1)<len(cs2):
            cs1+=(len(cs2)-len(cs1))*[ElementFp2(p,ns,0,0)]
        elif len(cs2)< len(cs1):
            cs2+=(len(cs1)-len(cs2))*[ElementFp2(p,ns,0,0)]
        cs1plus2 = remLeadZerosFp2([cs1[i]+cs2[i] for i in range(len(cs1))])
        return PolyFp2(p,ns,cs1plus2,x)
    def __mul__(self,other):
        p = self.char
        ns = self.nonsquare
        x = self.var
        cs1 = self.coefs
        cs2 = other.coefs
        cs1times2 = [ElementFp2(p,ns,0,0)]*(len(cs1)+len(cs2)-1)
        for i in range(len(cs1)):
            for j in range(len(cs2)):
                cs1times2[i+j]+=cs1[i]*cs2[j]
        return PolyFp2(p,ns,cs1times2,x)
    def scaleFp2(self,c):
        p = self.char
        ns = self.nonsquare
        x = self.var
        cpoly = PolyFp2(p,ns,[c],x)
        return self*cpoly
    def scaleInt(self,n):
        p = self.char
        ns = self.nonsquare
        x = self.var
        nfp2 = ElementFp2(p,ns,n,0)
        npoly = PolyFp2(p,ns,[nfp2],x)
        return self*npoly
    def __sub__(self,other):
        return self+ (other.scaleInt(-1))
    def __abs__(self):
        if self.deg == -1:
            return self
        an= self.leadCoef
        anInv = an.multInv()
        monic = self.scaleFp2(anInv)
        return monic
    def timesxn(self,n):
        p = self.char
        ns = self.nonsquare
        x = self.var
        xn = xnFp2(p,ns,x,n)
        return self*xn
    def __divmod__(self,other):
        if other.deg == -1:
            return "Division by 0"
        p = self.char
        ns = self.nonsquare
        x = self.var
        rem = self
        q = PolyFp2(p,ns,[ElementFp2(p,ns,0,0)],x)
        monic = abs(other)
        if other.deg == 0:
            c0 = other.leadCoef
            dv = self.scaleFp2(c0.multInv())
            return (dv,q)
        while other.deg <= rem.deg:
            lcr = rem.leadCoef
            q0 = PolyFp2(p,ns,[lcr],'x')
            n = rem.deg - other.deg
            q0xn = q0.timesxn(n)
            q+=q0xn
            rem-=q0xn*monic
        lc0 = other.leadCoef
        return (q.scaleFp2(lc0.multInv()),rem)
    def __floordiv__(self,other):
        if other.deg == -1:
            return "Division by 0"
        dm = divmod(self,other)
        return dm[0]
    def __mod__(self,other):
        if other.deg == -1:
            return "Division by 0"
        dm = divmod(self,other)
        return dm[1]
    
def gcd(poly1,poly2):
        if poly1.deg >= poly2.deg:
            big = poly1
            small = poly2
        else:
            big = poly2
            small = poly1
        if small.deg < 0:
            return big
        elif small.deg == 0:
            return abs(small)
        while (big%small).deg >= 0:
            rem = big % small
            big = small
            small = rem
        return abs(small)


# Elliptic curves

def divPoly3Fp2(fg,x):
    f = fg[0]
    g = fg[1]
    p = f.char
    ns = f.nonsquare
    cs = [f*f.scale(-1),g.scale(12),f.scale(6),ElementFp2(p,ns,3,0)]
    return PolyFp2(p,ns,cs,x)

def 


