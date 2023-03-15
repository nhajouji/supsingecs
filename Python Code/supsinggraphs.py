# The following program takes as input a prime p,
# and returns a list of supersingular j values.

# To get started, we need a prime.
# primesBetween(a,b) returns a list of all primes p satisfying a<= p <= b.

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


# We will be working in F_p^2, so we will construct a class that represents
# elements in that field

# First, we need tools for doing arithmetic in Fp.
# Most of these are already built in - we just need a way of dividing elements.

# To divide in F_p, we essentially need to be able to solve the diophantine eq
# ax+by = 1 for x,y. We can do this using the Euclidean algorithm.

# The function invMod takes as input a pair of integers a,p,
# where p is assumed to be prime and a is assumed to be nonzero,
# and returns an integer x satisfying ax = 1 mod p.

def invMod(a,p):
    # First, check if we're dividing by 0:
    if a % p == 0:
        return '1/0'
    m = a % p
    n = p
    # We're going to find solutions x, y to the equation
    # ax + py = 1, by starting with two initial approximations
    # and obtaining increasingly good close values of x,y using
    # the Euclidean algorithm.
    last2 = [[0,1],[1,0]]
    s = 1
    # Our last 2 approximations are recorded in lst4.
    while n % m !=0:
        # We obtain q, r such that n = q m + r
        q = n//m
        r = n % m
        # We will use q to obtain a better approximation.
        x2 = q*last2[1][0]+last2[0][0]
        y2 = q*last2[1][1]+last2[0][1]
        # The pair (x2, y2) is an even better approximation of x,y.
        # We only need to keep our two most recent approximations:
        last2 += [[x2,y2]]
        last2 = last2[1:]
        n = m
        m = r
        # Finally, we multiply s by -1 to keep track of the parity
        # of the number of steps we've taken.
        s*=-1
    # The final pair (x,y) we obtain will satisfy ax-py = +/- 1,
    # where the sign is determined by s.
    xy = last2[1]
    return (xy[0]*s)%p

# We now construct a class representing elements of Fp2.
# An element of Fp2 looks like a + b sqrt(ns), where a, b are elements of Fp
# and ns is a nonzero element of Fp that does not have a square root in Fp.
# To describe an element in a field Fp2, we need to specify:
# The prime p, a nonsquare ns, and the two coefficients a,b




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
        # First check the characteristics are equal
        p1 = self.char
        p2 = other.char
        if p1!=p2:
            return False
        # Next, check the nonsquares are the same.
        # e.g. 1+sqrt(-1) is not the same as 1 + sqrt(-3)
        ns1 = self.nonsquare
        ns2 = other.nonsquare
        if ns1!=ns2:
            return False
        # Check that the coordinates are equal mod p
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
    def __pow__(self,other):
        if self.norm()==0:
            return self
        p = self.char
        e = other % (p-1)
        if e == 0:
            return self//self
        elif e == 1:
            return self
        else:
            be = list(bin(e)[2:])[::-1]
            a = self
            a2ns = [a]
            while len(a2ns)<len(be):
                a2ns.append(a2ns[-1]*a2ns[-1])
            ae = a//a
            for i in range(len(be)):
                if be[i]=='1':
                    ae*=a2ns[i]
            return ae
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
    def trace(self):
        cnj = self.conj()
        tr2 = self+cnj
        return tr2.proj1
    
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

    def __floordiv__(self,other):
        return self * other.multInv()

    def minPolyCoefs(self):
        a = self.proj1
        b = self.proj2
        p = self.char
        if b == 0:
            return [(-a)%p,1,0]
        else:
            return [self.norm(),(-1*self.trace())%p,1]

# x.minPoly('t') returns the minimal polynomial of x over Fp, in the variable t.
# If x is in Fp, then the minimal polynomial of x will be the string 't-x'
# Otherwise, the minimal polynomial will be a string of the form 't^2+at +b'
# where a is negative of the trace of x and b is the norm.    


# Primitive root

# fp2primtRt takes as input a prime p, assumed to be between 5 and 15072,
# and returns a primitive root for F_p^2.
# The primitive roots are obtained by solving Conway polynomials;
# we have a list of Conway polynomials available for p between 5 and 15072
# so that they do not have to be computed.

def fp2primRt(p):
    #We start by reading the file containing Conway polynomial data
    cpf = open("conway.txt","r")
    cpl0 = cpf.read()
    cpf.close()
    #We format the data in the file so that we can access it more easily.
    cpl1 = cpl0.split('\n')
    cpl2 = [s.split(',') for s in cpl1]
    cpls = [[int(s) for s in l] for l in cpl2 if len(l)==2]
    primes = primesBetween(5,15072)
    # Since we can only proceed if we have primes between 5 and 15072,
    # we check that the input is, indeed, a prime in that range.
    if p not in primes:
        return "Not found - are you sure you have a prime p < 15072?"
    conwayD = {primes[i]:cpls[i][::-1] for i in range(len(primes))}
    # Now we know p has an entry in conwayD so we look it up:
    cp = conwayD[p]
    # To obtain the primitive root, we solve the quadratic encoded in cp.
    # Note that cp is a pair of integers a, b that represents x^2+ax+b = 0,
    # so we're simply solving a quadratic equation.
    cd = (cp[0]**2-(4*cp[1]))%p
    cprt1 = (cp[0]*invMod(-2,p))%p
    # The root will be an element of Fp2, so we need to express the answer
    # as an element of Fp2. For that, we need to make sure we know the square
    # root that gets used to represent elements of Fp2.
    ns = chooseNonSquare(p)
    # Finally, we're going to solve the quadratic.
    # We know the discriminant of the quadratic; we know it is a nonsquare in
    # Fp; and we know ns is a nonsquare in Fp.
    # This means cd/ns is a square in Fp - so we look for a square root
    # of (cd/ ns) in Fp.
    cprt2sq = (cd*invMod(ns,p))%p
    # If cd = ns, we don't actually have to work to find that square root.
    if cprt2sq == 1:
        rtd = 1
    # If they're not equal, we have to search in Fp for a square root.
    else:
        sq = cprt2sq
        rt = 2
        while 2*rt<= p+1 and (rt*rt) % p != sq:
            rt +=1
        if 2*rt == p+1:
            return 'Check p = '+str(p)
        rtd = rt %p
    # Once we have that square root, we finishe compute a root of the quadratic
    # using the quadratic formula, and return the answer as an element of Fp2.
    cprt2 = (rtd*invMod(2,p))%p
    return ElementFp2(p,ns,cprt1,cprt2)

# genPowLog takes as input a prime p, and returns the primitive root of Fp2,
# along with a pair of dictionaries.
# The first dictionary records the powers of the primitive root in Fp2,
# and the second records the discrete logs of all nonzero elements
# (where the base of the discrete log is the primitive element).

# We will use genPowLog to solve quadratics & to speed up evaluation of
# polynomials.

def genPowLog(p):
    # We start by computing the primitive root.
    g = fp2primRt(p)
    # The nonsquare we will be using is already encoded in the primitive root;
    # we read it off so we don't have to recompute it.
    ns = g.nonsquare
    # We will be computing powers ge of g.
    ge = g
    # The 0th power is obviusly 1 - this is represented as (1,0) in Fp2.
    # The log of (1,0) is 0.
    # We record these values in the powers,logs dictionaries. As we compute more
    # powers of g, we will record the power and log in these dictionaries.
    powers = {0:(1,0)}
    logs = {(1,0):0}
    e = 1
    # To begin, we compute all powers of g until we find a power of g
    # (after e = 0) that lives in Fp.
    while ge.proj2 != 0:
        powers.update({e:ge.vec})
        logs.update({ge.vec:e})
        ge*=g
        e+=1
    gfp = ge.proj1
    # Now, we no longer need to multiply pairs of elements in Fp2 -
    # we will compute powers of gfp - which must itself be a primitive root
    # of Fp - and then rescale the powers of g we've already computed,
    # by powers of gfp.
    gfpn = gfp
    efp = e
    while gfpn != 1:
        # First, multiply every one of the early powers of g by gfpn,
        # and record the results.
        for i in range(e):
            gi=powers[i]
            gigfpn = ((gi[0]*gfpn)%p,(gi[1]*gfpn)%p)
            powers.update({i+efp:gigfpn})
            logs.update({gigfpn:i+efp})
        #Then raise the power of gfpn.
        efp+=e
        gfpn = (gfpn*gfp)%p
    return [g,powers,logs]

# solveQuadFp2 takes as input a pair (a,b), where a, b are in Fp2 and represent
# a quadratic equation x^2 + ax + b = 0, and a pair of dictionaries pl
# assumed to contain dictionaries obtained from genPowLog.
# It then produces a list containing all roots of the quadratic,
# as elements of Fp2.
def solveQuadFp2(ab,pl):
    # We read the entries of the two lists and give them names.
    powD = pl[0]
    logD = pl[1]
    a = ab[0]
    b = ab[1]
    # We read off the prime and nonsquare from the coefficients.
    p = a.char
    ns = a.nonsquare
    # We compute the discriminant of the quadratic.
    disc = a**2+b.scale(-4)
    # If the discriminant is 0, we do not need to worry about finding
    # a square root of the discriminant - it is its own square root.
    if disc.norm() == 0:
        rtd =disc
    # As long as the discriminant is nonzero, we can compute the square root
    # by using the log dictionary.
    else:
        # First, compute the log of the discriminant.
        logd = logD[disc.vec]
        # If the discrete log is odd, then the discriminant is not a square,
        # so the quadratic has no roots in Fp2.
        if logd % 2 == 1:
            return []
        # Otherwise, we can obtain a square root by raising the primitive root
        # g to half of log d.
        rtdvec = powD[logd//2]
        # We compute g^(log d/2) using our powers dictionary, and convert
        # the vector we get into an element of Fp2.
        rtd = ElementFp2(p,ns,rtdvec[0],rtdvec[1])
    # Finally, we obtain roots of the quadratic using the quadratic formula.
    rtab1 = (rtd-a).scale(p//2)
    if rtd.norm() == 0:
        return [rtab1]
    rtab2 = (rtd.scale(-1)-a).scale(p//2)
    return [rtab1,rtab2]

# To compute the 3-isogeny graph, we will need to be able to solve cubics.
# However, the cubics we will be interested in have a very specific form:
# They look like 12 a b^2 - 12 a b x + 4 a x^2 + 3 x^3 = 0, where a,b
# are elements of Fp2.


# The function solveCubicFp2 takes as input a pair (a,b),
# where a, b are elements of Fp2, and a power log dictionary pl,
# and returns the roots of the cubic determined by (a,b).

def solveCubicFp2(ab,pl):
    # We read the entries of the two lists and give them names.
    powD = pl[0]
    logD = pl[1]
    a = ab[0]
    b = ab[1]
    # We read off the prime and nonsquare from the coefficients.
    p = a.char
    ns = a.nonsquare
    # We need a primitive cube root of unity:
    w3vec = powD[(p**2)//3]
    w3 = ElementFp2(p,ns,w3vec[0],w3vec[1])
    # We need a cube root of the following cube:.
    cube = (a*a.scale(-2))*(a.scale(4)+b.scale(27))
    # If the cube is 0, we do not need to worry about finding
    # a cube root - it is its own square root.
    if cube.norm() == 0:
        r =disc
    # If the cube is nonzero, we use the log dictionary.
    else:
        # First, compute the log of the cube.
        logc = logD[cube.vec]
        # If the discrete log is not divisible by 3, something is wrong -
        # but that means the cubic has no roots, so we return the empty list.
        if logc % 3 != 0:
            return []
        # Otherwise, we can obtain a cube root by raising the primitive root
        # g to a third of the log of the cube.
        rtcvec = powD[logc//3]
        # We compute g^(log c/3) using our powers dictionary, and convert
        # the vector we get into an element of Fp2.
        r = ElementFp2(p,ns,rtcvec[0],rtcvec[1])
    c = ElementFp2(p,ns,2,0).scale(invMod(9,p))
    rtpart1 = c.scale(-2)*a
    rtpart2 = c*r
    rtpart3 = c * (a*(a.scale(4)+b.scale(27)))//r
    rt1 = rtpart1 + rtpart2+rtpart3
    rt2 = rtpart1 + (w3*rtpart2)+ (w3*w3*rtpart3)
    rt3 = rtpart1 + (w3*w3* rtpart2)+(w3*rtpart3)
    return [rt1,rt2,rt3]





# evalIntPolyFp2 is used to speed up computation of polynomials by using
# the output of genPowLog.
# The coefficients of the polynomial are assumed to be integers;
# x should be an element of Fp2; and powlog should be obtained via genPowLog.
# The output will be an element of Fp2.

def evalIntPolyFp2(coefs,x,powlog):
    p = x.char
    ns = x.nonsquare
    # We read off the prime and nonsquare from x.
    # We also convert the constant term in the polynomial to an element of Fp2.
    ev0 = ElementFp2(p,ns,coefs[0],0)
    # We check if x == 0; if it is, we return the constant term.
    if x.norm()==0:
        return ev0
    # If x is not 0, we can compute log(x) using our log dictionary.
    xi = powlog[1][x.vec]
    # Now, we go through the list of coefficients:
    for d in range(1,len(coefs)):
        cd = coefs[d]
        # If the coefficient is 0, we don't need to do anything.
        if cd % p !=0:
            # If the coefficient is nonzero, we use the powers dictionary
            # to compute xd.
            xdvec = powlog[0][(xi*d)%((p**2)-1)]
            # We convert the vector we obtain from the dictionary to
            # an element of Fp2.
            xd = ElementFp2(p,ns,xdvec[0],xdvec[1])
            # We rescale xd by the appropriate coefficient, and add it
            # to our running evaluation.
            ev0+=xd.scale(cd)
    # Once we've done this for all coefficients, we can return the evaluation.
    return ev0

    




# 2-Isogeny Graph computation

# To start the main algorithm, we need to find a suitable nonsquare in Fp.

# chooseNonSquare takes as input a prime p,
# and returns a suitable nonsquare if one exists.
# To determine whether integers are squares, we use quadratic reciprocity.
# If a nonsquare can't be found in the list, an error message is returned.
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


# findCoefs0 takes as input a prime p, and a pair of dictionaries as input,
# and returns a pair (a,b), where a, b are elements of Fp2,
# that represents a supersingular elliptic curve y^2 = x(x^2+ ax + b).
# If d = -1,-2,-3, or -7, we don't actually need the dictionaries -
# the program will return a pair (a,b) that was precomputed.
# For the remaining values of d, we only have precomputed equations for
# supersingular curves of the form y^2 = x^3 + fx + g - these curves do not
# have 2-torsion over Q, so we can't find a single equation 
# of the form y^2 = x(x^2+ax + b), where a,b are integers, that would work
# for all primes p. However, we DO have 2-torsion in Fp, so we CAN find
# an equation of the form y^2 = x(x^2 + ax + b), with a,b in Fp - all we need
# to do is find a root of the cubic x^3 + fx + g.
# findCoefs0 uses evalIntPolyFp2 to evaluate the cubic at values of Fp until
# it finds a root - since findCoefs0 needs a powerlog dictionary, we include
# it as an input in findCoefs0.

def findCoefs0(p,pl):
    # Choose the nonsquare
    d = chooseNonSquare(p)
    nonSquares = [-1,-2,-3,-7,-11,-19,-43,-67,-163]
    # Load equations (f,g) for d in [-11,-19,-43,-67,-163]
    fgs = [(-264,1694),(-152,722),(-3440,77658),(-29480,1948226)]
    fgs+=[(-8697680,9873093538)]
    fgDic = {nonSquares[4+i]:fgs[i] for i in range(5)}
    # If d in [-1,-2,-3,-7] return precomputed (a,b)
    if d == -1:
        return (ElementFp2(p,-1,0,0),ElementFp2(p,-1,-1,0))
    elif d == -3:
        return (ElementFp2(p,-3,3,0),ElementFp2(p,-3,3,0))
    elif d == -2:
        return (ElementFp2(p,-2,4,0),ElementFp2(p,-2,2,0))
    elif d == -7:
        return (ElementFp2(p,-7,-21,0),ElementFp2(p,-7,112,0))
    else:
        # If d not in [-1,-2,-3,-7], look up coefs (f,g)
        fg = fgDic[d]
        f = fg[0]
        # We start searching for a root with x = 0.
        x= ElementFp2(p,d,0,0)
        # We will be adding 1 to x if x is not a root; we define the 1
        # element in Fp2.
        one = ElementFp2(p,d,1,0)
        # We keep track of how many evaluations we've done; if there's
        # a typo and we don't have a 2-torsion point, we don't want the
        # program to search forever. 
        ct = 0
        while ct < p and evalIntPolyFp2([fg[1],fg[0],0,1],x,pl).norm()!= 0:
            x+=one
            ct+=1
        # When the loop stops, we've either checked every element of Fp,
        # or we've found a 2-torsion point.
        if ct == p:
            return "No 2-torsion found"
        # If we did find a 2-torsion point, then the equation of the form
        # y^2 = x(x^2 + ax + b) can be computed from x and f:
        else:
            return (x.scale(-3),x*x.scale(3)+one.scale(f))


# The equations we obtain from findCoefs0 (and all equations used in the
# computation of the 2-isogeny graph) will be of the y^2 = x(x^2+ax + b).
# Given a pair (a,b), with a,b in Fp2, that represents an elliptic curve,
# we can readily compute the discriminant of the quadratic (x^2+ax+b),
# and the j-invariant of the associated elliptic curve, using:

def disc(ab):
    a = ab[0]
    b = ab[1]
    return a*a+b.scale(-4)

def j2T(ab):
    a = ab[0]
    b = ab[1]
    num = ((a*a-b.scale(3))*(a*a-b.scale(3))*(a*a-b.scale(3))).scale(256)
    den = b*b*disc(ab)
    return num*(den.multInv())


# Similarly, given a pair (a,b) representing a 3-torsion model,
# the j-invariant of a 3-torsion model can be computed directly from the
# pair (a,b).


# j3T takes as input a pair (a,b) representing a 3-torsion model,
# and returns the j-invariant of the elliptic curve represented by (a,b).
def j3T(ab):
    a = ab[0]
    b = ab[1]
    num = a.scale(-256)*((a+b.scale(6))**3)
    den = (b**3)*(a.scale(4)+b.scale(27))
    return num//den

# Every elliptic curve E has three isogenies E-> E' of degree 2.
# twoIsoPairs takes as input a pair (a,b), representing a supersingular curve
# y^2 = x(x^2 + ax + b) over Fp2, and returns a list containing three new
# pairs of the same form, representing the elliptic curves E' that are
# on the receiving end of the degree 2 isogenies from E.

# First, the program generates two other pairs (a,b), that also represent
# the original curve E. To do this, it solves the quadratic equation
# x^2 + ax + b = 0 using solveQuadFp2, and computes the two changes of variable
# that move the roots of the quadratic to (0,0).
# Then, the program computes the pairs representing the isogenous curves
# easily from (a,b) - the isogenous pair is (-2a, a^2 - 4b). 

def twoIsoPairs(ab,pl):
    # First, solve the quadratic equation x^2+ax + b
    rts = solveQuadFp2(ab,pl)
    r0 = rts[0]
    r1 = rts[1]
    # Next, we compute the change of variable to obtain new pairs (a,b)
    # that represent the original curve.
    a0 = r0.scale(2)-r1
    b0 = r0 *(r0-r1)
    a1 = r1.scale(2)-r0
    b1 = r1 * (r1 - r0)
    # Now we have three pairs - (a,b), (a0,b0), (a1,b1) - that represent our
    # original curve. For each of these pairs, we compute (-2a, a^2-4b).
    isopairs = []
    for ab in [ab, (a0,b0), (a1,b1)]:
        a = ab[0]
        a2 = a.scale(-2)
        b2 = disc(ab)
        isopairs.append((a2,b2))
    # The pairs just obtained represent elliptic curves which are 2-isogenous
    # to y^2 = x(x^2 + ax + b).
    return isopairs


# ab0toAllabs3 takes a pair (a,b) that represents an elliptic curve
# given by an equation of the form y^2 = x^3 + a(x-b)^2, and returns a set
# that contains 4 pairs of (a,b)'s that represent the same equation.
# The first element in the output is always the pair we input.

def ab0toAllabs3(ab,pl):
    rts = solveCubicFp2(ab,pl)
    absall = [ab]
    a = ab[0]
    b = ab[1]
    for r in rts:
        ai = a+r.scale(3)
        if ai.norm() != 0:
            bi = (a*b.scale(-2)+a*r.scale(2)+ r*r.scale(3))//(ai.scale(-2))
            absall.append((ai,bi))
    return absall

# threeIsoPairs is similar to twoIsoPairs: it takes as input a pair (a,b),
# which represents a 3-torsion model for some curve,
# and returns a list containing four pairs (a,b) that represent curves isogenous
# to the input.
# To obtain the new pairs, the function has to solve the associated cubic,
# so we need to include a power-log dictionary in the input so that we can
# use solveCubicFp2.

def threeIsoPairs(ab,pl):
    # First, solve the associated cubic equation
    rts = solveCubicFp2(ab,pl)    
    # Next, we compute the change of variable to obtain new pairs (a,b)
    # that represent the original curve.
    absall = [ab]
    a = ab[0]
    b = ab[1]
    for r in rts:
        ai = a+r.scale(3)
        if ai.norm() != 0:
            bi = (a*b.scale(-2)+a*r.scale(2)+ r*r.scale(3))//(ai.scale(-2))
            absall.append((ai,bi))
    # Now we have all pairs (ai,bi) that represent our original curve.
    # For each of these pairs, we compute pairs that represent the
    # isogenous curves
    absNw = [(ab[0].scale(-27),ab[0].scale(4)+ab[1].scale(27)) for ab in absall]
    # Finally, we return the pairs that represent the isogenous curves.
    return absNw




#ab2graph takes as input a pair ab0, representing an equation y^2 = x(x^2+ax+b),
# for a supersingular curve over Fp^2, and a pair of dictionaries that
# it will use to compute square roots.
# It returns the associated 2-isogeny graph, as a dictionary.
# The keys of the dictionary will be pairs (c0,c1) that represent
# supersingular j-invariants; and the values of the dictionary will be
# 3-element lists containing the endpoints of the edges coming out of a given
# j-invariant.
def ab2Graph(ab0,pl):
    # We create a list that will be populated with the j-invariants.
    js = []
    # We also create a list containing equations we may need to use.
    eqs = [ab0]
    # We create an empty dictionary that will be filled up with edges
    # once we start computing things.
    graph = {}
    # The program checks whether there are any equations we need to investigate;
    # to begin, there will be exactly one element in that set, namely the
    # equation ab0.
    while len(eqs) > 0:
        # We create a new list where we will store new equations we've found
        # that need to be examined further.
        neweqs = []        
        for ab in eqs:
            # For each equation we have, we compute the j-invariant.
            # If we've already seen that j-invariant, we don't do anything.
            jab = j2T(ab).vec
            if jab not in js:
                # If we haven't seen it, we add it to the list of j-invariants
                # we have seen, so that we don't repeat this computation
                # in the future.
                js.append(jab)
                # Next, we compute equations for all curves 2-isogenous to
                # the curve we have.
                ab2s = twoIsoPairs(ab,pl)
                # Then we compute their j-invariants. These j-invariants
                # need to be stored as edges in the graph.
                jab2s = [j2T(ab2).vec for ab2 in ab2s]
                graph.update({jab:jab2s})
                # Finally, if any of the new equations represent j-invariants
                # we haven't seen, we add them to the list of new equations.
                for i in [0,1,2]:
                    if jab2s[i] not in js:
                        neweqs.append(ab2s[i])
        # Once we've made our way through the list of equations,
        # we replace it with the set of newequations we just obtained.
        eqs = neweqs
    # The loop repeats until no new j-invariants are found.
    # The program then returns the graph it just computed.
    return graph

# iso3Graph takes as input a prime p, which is assumed to be 2 mod 3,
# as well as a power-log dictionary, and returns the 3-isogeny graph.
# The algorithm is similar to the 2-isogeny graph computation, although
# we do not call findCoefs0 for the 3-isogeny graph: we always start with
# the curve with j-invariant 0, even if p is 3 mod 4. (If p is both 2 mod 3
# and 3 mod 4, then both 0 and 1728 are supersingular; the 2-isogeny graph
# "prioritizes" the 1728 over the 0 curve, but the 3-isogeny graph completely
# ignores the 1728 until it appears at a later stage in the isogeny graph.

def graph3(p,pl):
    # We create a list that will be populated with the j-invariants.
    js = [(0,0)]
    if p % 3 != 2:
        return js
    # To be consistent with the rest of our computations, we still use
    # chooseNonSquare to choose our nonsquare: if p is 3 mod 4, we will be using
    # -1 as our nonsquare; otherwise we will take -3 as our nonsquare.
    ns = chooseNonSquare(p)
    one = ElementFp2(p,ns,1,0)
    # We also create a list containing equations we may need to use.
    ab0 = (one.scale(-162),one.scale(-3))
    eqs = [ab0]
    j1 = (-12288000)%p
    # We create an dictionary that will be filled up with edges
    # once we start computing things. Initially, we record the edges
    # coming out of j = 0.
    graph = {(0,0):[(0,0)]+3*[(j1,0)]}
    # The program checks whether there are any equations we need to investigate;
    # to begin, there will be exactly one element in that set, namely the
    # equation ab0.
    while len(eqs) > 0:
        # We create a new list where we will store new equations we've found
        # that need to be examined further.
        neweqs = []        
        for ab in eqs:
            # For each equation we have, we compute the j-invariant.
            # If we've already seen that j-invariant, we don't do anything.
            jab = j3T(ab).vec
            if jab not in js:
                # If we haven't seen it, we add it to the list of j-invariants
                # we have seen, so that we don't repeat this computation
                # in the future.
                js.append(jab)
                # Next, we compute equations for all curves 3-isogenous to
                # the curve we have.
                ab2s = threeIsoPairs(ab,pl)
                neweqs+=ab2s
                # Then we compute their j-invariants. These j-invariants
                # are stored as edges in the graph.
                jab2s = [j3T(ab2).vec for ab2 in ab2s]
                graph.update({jab:jab2s})        
        # Once we've made our way through the list of equations,
        # we replace it with the set of newequations we just obtained.
        eqs = neweqs
    # The loop repeats until no new j-invariants are found.
    # The program then returns the graph it just computed.
    return graph

# graph2mat converts the data in the dictionary produced by ab2Graph
# (as well as some later functions) into an ordinary matrix - that is,
# a list of lists of integers.
def graph2mat(dic,p):
    # First, we need the keys of the dictionary - these represent the vertices.
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

# We now have everything in place to obtain the supersingular j-invariants,
# as well as the 2-isogeny graph.

# getSupSingRawData takes as input a prime p, and returns a list containing:

# First, the 2-isogeny graph, as a dictionary; the keys of the dictionary are
# pairs of integers (a,b), which represent the j-invariant a+b sqrt(d).
# The values of the dictionary are 3-element lists of pairs (a,b),
# which represent the 3-isogenous j-invariants in the same way.

# Second, a primitive root of Fp2 - note that the nonsquare d, which is needed
# to interpret the keys of the graph, is encoded in the primitive root,
# and can be recovered as g.nonsquare (where g is the primitive root)

# Finally, we have the power/log dictionaries that were computed in the process
# these will be used to streamline future computations.

# Altogether the output is [2-iso graph, primitive root, powerDic,logDic]

def getSupSingRawData(p):
    # First, we use genPowLog to obtain the primitive root/powers/logs
    gpl = genPowLog(p)
    pl = gpl[1:]
    # We use the powerlog dictionaries to obtain ab0
    ab0 = findCoefs0(p,pl)
    # We compute the 2-isogeny graph
    graph = ab2Graph(ab0,pl)
    # We return the raw data
    return [graph]+gpl



# Modular curve computations


######################
#To be removed soon #
######################

#This is currently used in computation of 3-isogeny graph when p = 1 mod 3.
#It will be removed in the future.
def x3jpairs(t):
    p = t.char
    ns = t.nonsquare
    if t.norm() == 0:
        return "Nodal curve"
    t0 = t//t
    df2 = t0.scale(4)+t.scale(27)
    if df2.norm() == 0:
        return "Nodal curve"
    den12 = t*df2
    den1 = t*t*den12
    den2 = df2*df2*den12
    num1r = t0+t.scale(6)
    num1 = num1r*num1r*num1r.scale(-256)
    num2r = t0+t.scale(-54)
    num2 = num2r*num2r*num2r.scale(-256)
    return [num1//den1,num2//den2]


###################################
# Supersingular graph Computations#
###################################


class supSingFp2:
# Computes the 2-isogeny graph using getSupSingRawData;
# the data can be accessed in the future as self.rawdata
# without needing to repeat the initial computation.
    def __init__(self,p):
        self.char = p
        self.rawdata = getSupSingRawData(p)
        self.iso2graph = self.rawdata[0]
        self.primrt = self.rawdata[1]
        self.pl = self.rawdata[-2:]
        self.nonsquare = (self.primrt).nonsquare
    def __repr__(self):
        p = self.char
        return "Data about supersingular curves in characteristic "+str(p)
# self.js() converts the j-invariants in rawdata to elements of Fp2
# and returns a list containing the result
    def js(self):
        p = self.char
        graph = self.iso2graph
        d = self.nonsquare
        # We read the j's off from the keys in the 2-isogeny graph
        jvecs = list(graph.keys())
        # We sort the j's
        jvecs.sort(key = lambda x:x[0]+p*min(x[1],p-x[1]))
        # The tuples we have are converted into elements of Fp2,
        # and the answer is returned.
        return [ElementFp2(p,d,ab[0],ab[1]) for ab in jvecs]

    
    # The following computes j-invariants from a modular parameter t
    def jX0(self,l,t):
        p = self.char
        ns = self.nonsquare
        t0 = ElementFp2(p,ns,1,0)
        if l == 5:
            return ((t*t+t.scale(10)+t0.scale(5))**3)//t
        elif l == 7:
            t2 = t*t
            num= (t2+t.scale(-13)+t0.scale(49)) *((t2+t.scale(-5)+t0)**3)
            return (num.scale(-1))//t            
        elif l == 13:
            t2 = t*t
            t3 = t2*t
            t4 = t2*t2
            n1 = (t4+t3.scale(-7)+t2.scale(20)+t.scale(-19)+t0)**3
            n2 = t2.scale(-1)+t.scale(5)+t0.scale(-13)
            return (n1*n2)//t
        else:
            return 'Not found'

    # This computes j-invariant of pt = (x,y) on X_0(11)
    # Note that (x,y) should not be a point of order 5
    def jX0l11(self,pt):
        p = self.char
        ns = self.nonsquare
        t0 = ElementFp2(p,ns,1,0)
        x = pt[0]
        y = pt[1]
        x2 = x*x
        x3 = x2*x
        x4 = x3*x
        num0 = t0.scale(217)+x.scale(140)+x2.scale(-114)+x3.scale(12)+x4
        num0+= y*(t0.scale(-32)+x.scale(40)+x2.scale(-8))
        if num0.norm() == 0:
            return num0
        num = num0**3
        den=((t0.scale(51)+x.scale(-29)+x2.scale(4)+y.scale(4)-xy)**2)
        den*= (t0.scale(19)+x.scale(-5)+y)
        return num//den

    # For l = 11, we will do following:
    # Check if -121, -11*131^3, -2^15 ss; if they are, add relevant edges
    # to graph.
    # For z0 in Fq, z0 != 5, 16, find all pts (z0,w) on X_0(11)-
    # There are 0, 1 or 2 such points.
    # For each of those points, we compute j11(z0,w)
    # If j11(z0,w) is supersingular, we compute (z1,w1) = (16,61)-(z0,w),
    # evaluate j11(z1,w1) and add the edges to the graph.
        

    def isoG(self,l):
        if l == 2:
            return self.iso2graph
        elif l == 5:
            c = 125
        elif l == 7:
            c = 49
        elif l == 13:
            c = 13
        elif l > 13:
            return 'Not found'
        p = self.char
        ns = self.nonsquare
        if l == 3:
            if p % 3 == 2:
                return graph3(p,self.pl)
            else:
                return self.isoGraph3()
        t0 = ElementFp2(p,ns,1,0)
        js = self.js()
        jvs = [j.vec for j in js]
        ssns = [0 for i in range(p**2)]
        for j in jvs:
            ssns[j[0]+p*j[1]]+=1
        edges = {jv:[] for jv in jvs}
        edgesSeen = 0
        n = 1
        while n < p**2 and edgesSeen < len(jvs)*(l+1):
            t = ElementFp2(p,ns,n%p,n//p)
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

    def mat(self,l):
        if l not in [2,3,5,7,13]:
            return 'Not found'
        else:
            p = self.char
            graph = self.isoG(l)
            return graph2mat(graph,p)
    

    # This will eventually be removed, as it does the same thing as graph3
    # but takes much longer.
    
    def isoGraph3(self):
        js = self.js()
        pl = self.pl
        p = self.char
        ns = self.nonsquare
        jvecs = [j.vec for j in js]
        jtest = [0]*(p*p)
        seen = [0]*(p*p)
        seen[0]+=1
        for j in jvecs:
            jn = j[0]+p*j[1]
            jtest[jn]+=1
        edges = {jv:[] for jv in jvecs}
        edgesSeen = 0
        if p % 3 == 2:
            edges[(0,0)]+=[(0,0)]+3*[(-12288000%p, 0)]
            edgesSeen+=4
        for a in range(p):
            for b in range(p):
                t = ElementFp2(p,ns,a,b)
                tn = a+p*b
                if seen[tn] > 0:
                    continue
                else:
                    seen[tn]+=1
                    pair = x3jpairs(t)
                    if len(pair)==2:
                        j1 = pair[0]
                        if j1.vec == (0,0):
                            continue
                        elif j1.vec == (1728%p,0):
                            if p % 4 == 3:
                                edges[(1728%p,0)]+=2*[pair[1].vec]
                                edgesSeen+=2
                                if edgesSeen == len(js)*4:
                                        return edges
                        else:
                            j1v = j1.vec
                            j1n = j1v[0]+p*j1v[1]
                            if jtest[j1n]==1:
                                edges[j1v].append(pair[1].vec)
                                edgesSeen+=1
                                if edgesSeen == len(js)*4:
                                        return edges
        return edges
        
