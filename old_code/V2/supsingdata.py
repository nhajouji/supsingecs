################################
# Supersingular Isogeny Graphs #
################################

#############################
# Tools for computing in Fp #
#############################

# To divide in F_p, we essentially need to be able to solve the diophantine eq
# ax+by = 1 for x,y. We can do this using the Euclidean algorithm.


# SqrtDFp

# Input: A prime p
# Output: A dictionary whose keys are integers r in range(p),
#         and where dic[r] is a list of the square roots of r in Z/p

def sqrtDFp(p):
    rtdic= {a:[] for a in range(p)}
    for a in range(p):
        rtdic[(a*a)%p].append(a)
    return rtdic


# chooseNonSquare

# Input: A prime p, assumed to be smaller than 15073
# Output: A quadratic nonresidue -d in F_p, where d is a Heegner number

def chooseNonSquare(p):
    # The suitable nonsquares are:
    nonSquares = [-1,-2,-3,-7,-11,-19,-43,-67,-163]
    # Now we go through the list until we find one which is not a square.
    # -1 is not a square mod p iff p is 3 mod 4
    if p % 4 == 3:
        return -1
    # Otherwise p is 1 mod 4, so -1 is a square. Furthermore, for any prime q,
    # p is a square mod q iff q is a square mod p.
    # Putting it all together, -q is a square mod p iff q is a square mod p
    # iff p is a square mod q.
    # So, -3 is not a square mod p iff p is not a square mod 3 iff p is 2 mod 3:
    elif p % 3 == 2:
        return -3
    # Similarly, -2 is not a square mod p iff 2 is not a square.
    # 2 is a square mod p iff p is 1 or 7 mod 8, so 2 is a nonsquare iff
    # p is +/- 3 mod 8.
    # However, we know that p is NOT 3 mod 8, otherwise p would be 3 mod 4,
    # which has already been checked for. Therefore, -2 is a nonsquare iff
    # p % 8 = 5 (for primes at this stage in the algorithm).
    elif p % 8 == 5:
        return -2
    # For the remaining possible values, there are multiple residue classes
    # that can work. We check each of the remaining nonsquares in the list
    # until we find one that works.
    for d in [-7,-11,-19,-43,-67,-163]:
        q = -d
        sqs = [a**2 % q for a in range(1,(q+1)//2)]
        p0 = p % q
        if p0 not in sqs:
            return d
    return "Couldn't find one - make sure p is an odd prime, and p < 15073 "


####################
# Computing in Fp2 #
####################

class ElementFp2:
# The class is initialized by specifying the 3 integers (p, a, b).
    def __init__(self,p,a,b=0):
        self.char = p
        self.nonsquare = chooseNonSquare(p)
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

# We can add and multiply elements of Fp2.    
    def __add__(self,other):
        a1 = self.proj1
        a2 = other.proj1
        b1 = self.proj2
        b2 = other.proj2
        p = self.char
        return ElementFp2(p,(a1+a2) % p, (b1+b2)%p)
    
    def __mul__(self,other):
        a1 = self.proj1
        a2 = other.proj1
        b1 = self.proj2
        b2 = other.proj2
        p = self.char
        ns = self.nonsquare
        a3 = (a1*a2+ns*b1*b2) % p
        b3 = (a1*b2+a2*b1) % p
        return ElementFp2(p,a3,b3)
    def __rmul__(self,n):
        p = self.char
        v= self.vec
        return ElementFp2(p,(v[0]*n)%p,(v[1]*n)%p)
    def __neg__(self):
        return (-1)*self
    def __sub__(self,other):
        return self+(-other)
    def eval_poly(self,coefs):
        p = self.char
        t0 = ElementFp2(p,1)
        ev = ElementFp2(p,0)
        for c in coefs[::-1]:
            ev*=self
            ev+=c *t0
        return ev
# x.conj() returns the Galois conjugate of x    
    def conj(self):
        a = self.proj1
        b = self.proj2
        p = self.char
        return ElementFp2(p, a, p-b)
# x.norm() computes the norm of x by multiplying x and x.conj().
# Note: The output of x.norm() will be an integer, NOT an element of Fp2
    def norm(self):
        cnj = self.conj()
        n2 = self*cnj
        return n2.proj1
    def trace(self):
        cnj = self.conj()
        tr2 = self+cnj
        return tr2.proj1

    def __pow__(self,n):
        if self.norm()==0:
            return self
        p = self.char
        an = ElementFp2(p,1)
        a = self
        if n < 0:
            a_norm = (a*a.conj()).proj1
            # We replace a by its multiplicative inverse
            a = pow(a_norm,-1,p)*a.conj()
            n*= (-1)
        while n > 0:
            if n % 2 == 1:
                an*= a
            a*=a
            n = n//2
        return an

    def __floordiv__(self,other):
        return self * pow(other,-1)

    
    def sqrts(self,dic):
        nrm = self.norm()
        p = self.char
        d = self.nonsquare
        if nrm == 0:
            return [self]
        elif len(dic[nrm])==0:
            return []
        a = self.proj1
        b = self.proj2
        if b == 0:
            if len(dic[a])>0:
                return [ElementFp2(p,x) for x in dic[a]]
            else:
                adinv=(a*pow(d,-1,p))%p
                return [ElementFp2(p,0,y) for y in dic[adinv]]
        else:
            rtnrm = dic[nrm][0]
            x2 = ((a+rtnrm)*((p+1)//2))%p
            if len(dic[x2])==0:
                x2 = ((a-rtnrm)*((p+1)//2))%p
            x1 = dic[x2][0]
            y1 = (b * pow(2*x1,-1,p))%p
            sqrt1 = ElementFp2(p,x1,y1)
            sqrt2 = (-1)*sqrt1
            return [sqrt1,sqrt2]

    def min_poly_coefs(self):
        a = self.proj1
        b = self.proj2
        p = self.char
        if b == 0:
            return [(-a)%p,1,0]
        else:
            return [self.norm(),(-1*self.trace())%p,1]


# solveQuadFp2 is used in the computation of the l-isogeny graphs for l = 2,11
# Input 1: A pair (a,b),with a,b in Fp2, that represents x^2+a*x + b = 0
# Input 2: A dictionary whose keys are integers r in range(0,p), and where
# the values are (possibly empty) lists containing square roots of r in Z/pZ.

def solveQuadFp2(ab,dic):
    a = ab[0]
    b = ab[1]
    p = a.char
    cp = a//ElementFp2(p,-2)
    disc = a*a+((-4)*b)
    return [cp+(pow(2,-1,p)*rtd) for rtd in disc.sqrts(dic)]
# Note that input 2 can be obtained using sqrtDFp.

# findRootFp 
# Input 1: A list of integers [c0,c1,..,cd]
# Input 2: A prime p
# Output: A list containing 0 or 1 roots of the polynomial c0+c1*x+...+cd x^d
# in Z/pZ.

# The program searches for a root of the polynomial by evaluating it at points
# in F_p until it finds a root, or runs out of elements in F_p.

def findRootFp(coefs,p):
    for n in range(p):
        x = ElementFp2(p,n)
        evx = x.evalPoly(coefs)
        if evx.norm() == 0:
            return [x]
    return []



###################################
# Supersingular graph Computations#
###################################


class supSingData:
    def __init__(self,p):
        self.char = p
        self.sqrtDicFp = sqrtDFp(p)
        self.nonsquare = chooseNonSquare(p)
        
    def __repr__(self):
        p = self.char
        return "Data about supersingular curves in characteristic "+str(p)
    
    def nonsquarelist(self):
        p = self.char
        ds = [-1,-2,-3,-7,-11,-19,-43,-67,-163]
        rtd = self.sqrtDicFp
        return [d for d in ds if len(rtd[d%p])==0]

    ###################
    # 2-Isogeny Graph #
    ###################

    # ab2sChar0 checks if there is a curve E/Q that has a 2-torsion point
    # over Q, and whose reduction mod p is supersingular.
    # For each such curve (if any exist), we obtain a pair (a,b),
    # where a,b are elements of Fp2, that give an equation for that curve
    # of the form y^2 = x(x^2+ax+b).
    def ab2sChar0(self):
        dsSmall = [-1,-2,-3,-7]
        p = self.char
        rtd = self.sqrtDicFp
        ds = [d for d in dsSmall if len(rtd[d%p])==0]
        if len(ds)==0:
            return []
        ab1 = (ElementFp2(p,0),ElementFp2(p,-1))
        ab2 = (ElementFp2(p,4),ElementFp2(p,2))
        ab3 = (ElementFp2(p,3),ElementFp2(p,3))
        ab7 = (ElementFp2(p,-21),ElementFp2(p,112))
        abdic = {-1:ab1,-2:ab2,-3:ab3,-7:ab7}
        return [abdic[d] for d in ds]

    # When ab2sChar0 fails to find a model for a supersingular curve, we use
    # ab2find to obtain such a model.

    def ab2find(self):
        dsBig = [-11,-19,-43,-67,-163]
        p = self.char
        rtd = self.sqrtDicFp
        ds = [d for d in dsBig if len(rtd[d%p])==0]
        fg11 = (ElementFp2(p,-264),ElementFp2(p,1694))
        fg19 = (ElementFp2(p,-152),ElementFp2(p,722))
        fg43 = (ElementFp2(p,-3440),ElementFp2(p,77658))
        fg67 = (ElementFp2(p,-29480),ElementFp2(p,1948226))
        fg163 = (ElementFp2(p,-8697680),ElementFp2(p,9873093538))
        fgdic = {-11:fg11,-19:fg19,-43:fg43,-67:fg67,-163:fg163}
        fg0 = fgdic[max(ds)]
        coefs = [fg0[1],fg0[0],0,1]
        rts = findRootFp(coefs,p)
        if len(rts)==0:
            return rts
        else:
            x = rts[0]
            return [((-3)*x,3*x*x+fg0[0])]
        

    # isoCoefs2 is used in the computation of the 2-isogeny graph.
    
    # Input: a pair (a,b), where a, b are elements of Fp2 represent
    # an equation y^2 = x(x^2 + ax + b) for a supersingular curve.

    # Output: A list [(a_1,b_1),(a_2,b_2),(a_3,b_3)], where the (a_i,b_i)
    # represent the same type of object as (a,b).
    # Precisely, the 3 pairs we obtain describe the three curves that
    # are 2-isogenous to the curve represented by (a,b).

    def isoCoefs2(self,ab):
        rtd = self.sqrtDicFp
        # First, solve the quadratic equation x^2+ax + b
        rts = solveQuadFp2(ab,rtd)
        r0 = rts[0]
        r1 = rts[1]
        # Next, we compute the change of variable to obtain new pairs (a,b)
        # that represent the original curve.
        a0 = 2*r0-r1
        b0 = r0 *(r0-r1)
        a1 = 2*r1-r0
        b1 = r1 * (r1 - r0)
        # We compute the coefficients (-2a, a^2-4b) of the isogenous curves.
        isopairs = []
        for ab1 in [ab, (a0,b0), (a1,b1)]:
            isopairs.append(((-2)*ab1[0],(ab1[0]**2)+(-4)*ab1[1]))
        return isopairs

    # j2 is used in the compuation of the 2-isogeny graph to
    # compute j-invariants of the curves we encounter.

    # Input: (a,b), where a,b are ElementFp2
    # Output: the j-invariant of the curve y^2 = x(x^2+ax+b)

    def j2(self,ab):
        a = ab[0]
        b = ab[1]
        a2 = a*a
        d = a2+b.scale(-4)
        n0 = (a2+b.scale(-3)).scale(4)
        return (n0**3).scale(4)//(b*b*d)

    # isoGr2 computes the 2-isogeny graph.
    
    # Output: A dictionary with keys (a,b), where a,b are integers,
    # and (a,b) represents the supersingular j-invariant a+bsqrt(d).
    # The values of the dictionary are lists containing 3 vectors (a_i,b_i),
    # each representing the j-invariant of a curve 2-isogenous to (a,b).
    
    def isoGr2(self):
        # We construct a list that will be populated with the j-invariants
        # of the supersingular curves we obtain.
        js = []
        # To start the algorithm, we need coefficients for a supersingular
        # curve of the form y^2 = x(x^2+ax+b).
        # We can obtain these in constant time if at least one of -1,-2,-3,-7
        # is a nonsquare in F_p.
        if len(self.ab2sChar0())>0:
            eqs = self.ab2sChar0()
        # Otherwise we use ab2find to compute an equation over Fp
        else:
            eqs = self.ab2find()
        # We now have at least one pair (a,b) in eqs.
        # We construct a dictionary that will store the data we obtain
        # once we start the algorithm.
        graph = {}
        # We now compute new equations from the equations we have,
        # until we stop obtaining new j-invariants.
        while len(eqs)>0:
            neweqs = []
            for ab in eqs:
                jab = self.j2(ab)
                jabv = jab.vec
                if jabv not in js:
                    j1v = jabv
                    js.append(jabv)
                    ab2s = self.isoCoefs2(ab)
                    neweqs+=ab2s
                    jab2s = [self.j2(ab2) for ab2 in ab2s]
                    graph.update({jabv:[j.vec for j in jab2s]})
            eqs = neweqs
        return graph

    ##############################
    # Supersingular j-invariants #
    ##############################
    
    # The supersingular j-invariants are obtained from the 2-isogeny graph.
    
    # self.js returns the set of j-invariants as elements of Fp2.

    def js(self):
        p = self.char
        g2 = self.isoGr2()
        jvs = list(g2.keys())
        jvs.sort(key = lambda x:x[0]+p*min(x[1],p-x[1]))
        # The tuples we have are converted into elements of Fp2,
        # and the answer is returned.
        return [ElementFp2(p,ab[0],ab[1]) for ab in jvs]
        
    
    ##########################
    # Modular Curve Formulas #
    ##########################

    
    # For l = 5,7,13, the modular curve X_0(l) has genus 0.
    # We've chosen model with the cusps at 0, infinity.
    # For a nonzero element t in Fp2, viewed as a non-cuspidal point
    # of X_0(l), we can use jX0(l, t) to obtain the j-invariant of the
    # curve represented by t on X_0(l)

    # Input: an integer l in {5,7,13}; a nonzero element t in F_p^2
    # Output: the j-invariant of the associated curve, as an element of F_p^2
    

    def jX0(self,l,t):
        p = self.char
        t0 = ElementFp2(p,1)
        if l == 3:
            return ((t.evalPoly([-4,3]))**3)*(t.evalPoly([4,-27]))//(4*(t**3))
        elif l == 5:
            return ((t.evalPoly([5,10,1]))**3)//t
        elif l == 7:
            return (t.evalPoly([-49,13,-1]))*((t.evalPoly([1,-5,1]))**3)//t
        elif l == 13:
            return ((t.evalPoly([1,-19,20,-7,1]))**3)*t.evalPoly([-13,5,-1])//t
        else:
            return 'Not found'


    ###########
    # X_0(11) #
    ###########

    # x11ptsFromInt #
    
    # Input: an integer n
    # Output: the set of points [(x,y_i)] on X_0(11)
    # where x = (n%p) + sqrt(d) (n//p).

    def x11ptsFromInt(self,i):
        p = self.char
        if i == 16:
            return [(ElementFp2(p,16),ElementFp2(p,-60))]
        sqrtdic = self.sqrtDicFp        
        half = ElementFp2(p,pow(2,-1,p))
        x = ElementFp2(p,i%p,i//p)
        d = x.evalPoly([-79,-40,-4,4])
        rtds = d.sqrts(sqrtdic)
        if len(rtds)==0:
            return []
        else:
            rtd = rtds[0]
            y1 = (ElementFp2(p,1)+rtd)//ElementFp2(p,2)
            if rtd.norm() == 0:
                return [(x,y1)]
            else:
                return [(x,y1),(x,y1-rtd)]

    # jX0l11 #
    
    # Input: a point (x,y) on X_0(11)
    # Output: the j-invariant of the domain of the isog. rep'd by (x,y)
    

    def jX0l11(self,pt):
        p = self.char
        t0 = ElementFp2(p,1,0)
        x = pt[0]
        y = pt[1]
        if x.vec == (16%p,0) and y.vec== ((-60)%p,0):
            return ElementFp2(p,(-11*13%p)*(169%p))
        elif x.vec == (5,0) and y.vec== ((-5)%p,0):
            return ElementFp2(p,-(2**15))
        elif x.vec == (5,0):
            return ElementFp2(p,-121)
        num0 = x.evalPoly([217,140,-114,12,1])+y*(x.evalPoly([-32,40,-8]))
        if num0.norm() == 0:
            return num0
        num = num0**3
        den = ((x.evalPoly([51,-29,4])+4*y-x*y)**2)*(x.evalPoly([19,-5])+y)
        if den.norm() == 0:
            return 'Singular?'
        return num//den

    # jX0l11iso #
    
    # Input: a point (x,y) on X_0(11)
    # Output: the j-invariant of the codomain of the isog. rep'd by (x,y)

    def jX0l11iso(self,pt):
        p = self.char
        t0 = ElementFp2(p,1,0)
        x = pt[0]
        y = pt[1]
        if x.vec == (16%p,0) and y.vec== ((-60)%p,0):
            return t0.scale(-121)
        elif x.vec == (5,0) and y.vec== ((-5)%p,0):
            return t0.scale(-(2**15))
        elif x.vec == (5,0):
            return t0.scale((-11*131%p)*(131*131 %p))
        x2 = x*x
        x3 = x2*x
        xisoN = (x2.scale(16)+x.scale(214)+y.scale(121)+t0.scale(-260))
        yisoN = x3.scale(61)+x2.scale(2759)+(x*y).scale(726)+x.scale(-3730)
        yisoN+=y.scale(3025)+t0.scale(-18020)
        d0 = x + t0.scale(-16)
        dx = d0*d0
        xiso = xisoN//dx
        yiso = yisoN//(dx*d0)
        xy2 = (xiso,yiso)
        return self.jX0l11(xy2)

    ###########
    # isoGr11 #
    ###########

    # self.isoGr11 computes the 11-isogeny graph
    
    def isoGr11(self):
        p = self.char
        if p == 61:
            m61 = [[6,1,1,2,2],[1,7,2,1,1],[1,2,5,2,2],[2,1,2,1,6],[2,1,2,6,1]]
            jvs = [j.vec for j in self.js()]
            edges = {}
            for i in range(5):
                ji = jvs[i]
                ri = m61[i]
                eji = []
                for i2 in range(5):
                    eji+=ri[i2]*[jvs[i2]]
                edges.update({ji:eji})
            return edges
        t0 = ElementFp2(p,1,0)
        js = self.js()
        jvs = [j.vec for j in js]
        ssns = [0 for i in range(p**2)]
        for j in jvs:
            ssns[j[0]+p*j[1]]+=1
        edges = {jv:[] for jv in jvs}
        edgesSeen = 0
        if p == 131:
            edges[(0,0)]+=3*[(10,0)]
            edgesSeen+=3
        n = 0
        while n + 1 < p**2 and edgesSeen < len(jvs)*12:
            ptns = self.x11ptsFromInt(n)
            for pt in ptns:
                jpt = self.jX0l11(pt)
                jtv = jpt.vec
                if ssns[jtv[0]+p*jtv[1]]>0:
                    jtv2 = (self.jX0l11iso(pt)).vec
                    edges[jtv].append(jtv2)
                    edgesSeen+=1
                    if jtv == (0,0) and jtv2!= (0,0):
                        edges[jtv]+=2*[jtv2]
                        edgesSeen+=2
                    if jtv == (1728%p,0) and jtv2!= jtv:
                        edges[jtv]+=[jtv2]
                        edgesSeen+=1
            n+=1
        return edges
    
    ##################
    # Isogeny Graphs #
    ##################

    def isoGr(self,l):
        p = self.char
        if l == 2:
            return self.isoGr2()
        elif l == 11:
            return self.isoGr11()
        elif l == 3:
            c = ((4*pow(27,-1,p))**2)%p
        elif l == 5:
            c = 125
        elif l == 7:
            c = 49
        elif l == 13:
            c = 13
        else:
            return 'Not found'
        t0 = ElementFp2(p,1)
        js = self.js()
        jvs = [j.vec for j in js]
        ssns = [0 for i in range(p**2)]
        for j in jvs:
            ssns[j[0]+p*j[1]]+=1
        edges = {jv:[] for jv in jvs}
        edgesSeen = 0
        n = 1
        while n < p**2 and edgesSeen < len(jvs)*(l+1):
            t = ElementFp2(p,n%p,n//p)
            jtv = (self.jX0(l,t)).vec
            if ssns[jtv[0]+p*jtv[1]]>0:
                t2 = (t0.scale(c) // t)
                jtv2 = (self.jX0(l,t2)).vec
                edges[jtv].append(jtv2)
                edgesSeen+=1
                if jtv == (0,0) and jtv2!= (0,0):
                    edges[jtv]+=2*[jtv2]
                    edgesSeen+=2
                if jtv == (1728%p,0) and jtv2!= jtv:
                    edges[jtv]+=[jtv2]
                    edgesSeen+=1
            n+=1
        return edges

    
    ######################
    # Adjacency Matrices #
    ######################

    # mat computes the adjacency matrix of the l-isogeny graph.
    # Input: An integer l from the set {2,3,5,7,11,13}
    # Output: The adjacency matrix for the l-isogeny graph.

    def mat(self,l):
        p = self.char
        if l == 2:
            dic = self.isoGr2()
        elif l in [3,5,7,11,13]:
            dic = self.isoGr(l)
        else:
            return 'Not found'
        js = list(dic.keys())
        # We sort the j-invariants so that all j-invariants in Fp appear
        # before j-invariants in Fp^2
        js.sort(key = lambda x:x[0]+p*min(x[1],p-x[1]))
        # The number of vertices determines the size of the matrix.
        l = len(js)
        # The ordering of the rows in the matrix will be determined by the order
        # of the j-invariants in js. We record the position of each element using
        # jsi.
        j2i = {js[i]:i for i in range(l)}
        # We create a matrix of the correct size and fill it with 0's.
        mat = [[0 for i in range(l)] for j in range(l)]
        # For each i, we look up the edges coming out of vertex i,
        # determine the index of each endpoint using j2i,
        # and add a 1 to the corresponding row entry on the ith row.
        for i in range(l):
            for j in dic[js[i]]:
                ji = j2i[j]
                mat[i][ji]+=1
        # Finally, we return the matrix we just produced.
        return mat



################
# Prime Finder #
################

def primesBetween(a,b):
    a = max(2,a)
    if b < a:
        return []
    elif b == 2:
        return [2]
    elif b == 3:
        if a == 2:
            return [2,3]
        else:
            return [3]
    m = b
    # The following code is going to compute the set of primes < m
    # First, we create a list that will keep track of the primes-
    # the set contains m+1 elements, and for integers k <= m,
    # cands[k] = 0 records the fact that k is composite.
    # To begin, every even element other than 2 is set to 0,
    # to record the fact that 2 is the only even prime.
    cands = [0,0,1]+[(i % 2) for i in range(3,m+1)]
    # Next, we record that multiples of 3 other than 3 are composite.
    # Note that 6 is already known to be composite, 
    # so we can start at 9.
    for i in range(9,m+1,3):
        cands[i] = 0
    # Now we start going through the list of candidates to find primes p,
    # and updating the list by recording that all multiples of the prime,
    # which lie between p^2 and m inclusive, are composite.
    # We can stop once p^2 > m, since all multiples of p^2 will exceed m.
    # We start at p = 5, and we will only check odd numbers
    # that are not multiples of 3.
    # To avoid the multiples of 3, we will jump ahead by either 2 or 4
    # at each step. The number e records whether we need to jump by 2 or 4
    # at each step.
    e = -1
    p = 5
    while p**2 <= m:
        # This assumes p is prime. This is the case when p = 5,
        # and will be the case at the end of the loop when p is redefined.
        # As mentioned above, we start by recording that all multiples of
        # p between p^2 and m are composite.
        for pm in range(p**2,m+1,p):
            cands[pm]=0
        # Now we look for the next prime.
        # We alternate adding 2 and 4 to p and then checking whether
        # p is prime by checking if cands[p] is 0 or not.
        p+=3+e
        e*=-1
        while cands[p] == 0:
            p+=3+e
            e*=-1
    # When the loop ends, cands[p] = 0 if and only if p is 0,
    # so we can obtain the set of primes:
    primes = [p for p in range(a,m+1) if cands[p] == 1]
    return primes

