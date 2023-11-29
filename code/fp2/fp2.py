
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
    

