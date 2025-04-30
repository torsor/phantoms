#!/usr/bin/env python
# coding: utf-8

# # Linear System Dimension (LSD) version "GhostRider"
# 
# The code counts the dimension of linear systems on certain rational algebraic surfaces by counting the number of polynomials which are written as sums of monomials of particular forms which pass through some randomly chosen points with specific multiplicity.
# 

# **preamble**

# In[ ]:


import time
import datetime
import sys


# In[ ]:


class Timer:
    def __init__(self):
        self.start = self.now()
        self.lap = self.now()

    def lap_report(self):
        return round(self.lap(), 2)

    def end_report(self):
        return round(self.end(), 2)

    def now(self):
        return time.time()

    def lap(self):
        interval = self.now() - self.lap()
        self.lap = self.now()
        return interval

    def end(self):
        return self.now() - self.start

    def __repr__(self):
        return str(datetime.timedelta(seconds=float(self.end_report())))


# In[ ]:


VERBOSE = True
#VERBOSE = False


# In[ ]:


def say(message):
    if VERBOSE:
        print(message, flush=True)

def say_return(message):
    if VERBOSE:
        print(message, end="\r", flush=True)

def say_inline(message):
    if VERBOSE:
        sys.stdout.write(message)


# **end random preamble**

# ---

# **Random generation of points**
# 
# The main point of this code is to compute the dimension of linear systems of certain rational surfaces. We will do this by choosing a Zariski open set isomorphic to the affine plane $\mathbb A^2$, and converting a problem in terms of a homogeneous coordinate ring of the surface into inhomogeneous coordiates of the affine plane.
# 
# We will be interested in imposing conditions of base points with multiplicity. While we are interested in using points which are in general position, in practice we will work with randomly generated collections of points. 
# 
# By upper semicontinuity, a computation which yields $0$ in this case will give a proof that the general system with base points of the assigned multiplicity is also dimension $0$. On the other hand, validation of a nonzero value requires additional scrutiny.

# In[ ]:


# generate pairs [[p0, p1], m] consisting of the coordinates of a point in the plane
# with randomly generated coordinates

from random import randint

# largest coordinate in characteristic 0 (fixed global variable!)
M = 1000

def points_with_multiplicities(mult_list):
    n = len(mult_list)
    random_points = [[randint(1,M), randint(1, M)] for p in range(n)]
    points =random_points
    return [[points[i], mult_list[i]] for i in range(n)]

class PointMaker:
    def __init__(self, mult_list, char):
        n = len(mult_list)
        if char == 0:
            random_points = [[randint(0,M), randint(0, M)] for p in range(n)]
        else:
            random_points = [[randint(0, char), randint(0, char)] for p in range(n)]
        points = random_points
        self.mpoints = [[points[i], mult_list[i]] for i in range(n)]



# ---

# ## Enumerating Global Sections (with no basepoints)

# The functions below are designed to construct a generic polynomial of some fixed degree

# **Enumerating global sections of divisors on the projective plane $\mathbb P^2$**
# 
# The routine below enumerates the sections of the divisor $aH$ on the $\mathbb P^2$
# 
# Monomials in the variables $x, y, z$ of this bidegree, and then dehomogenize by evaluating $z = 1$, to obtain a collection of polynomials in variables which we refer to as $x$ and $y$ (which are actually $x/z$ and $y/z$).
# 
# The monomial $x^i y^j$ is represented by the pair
# 
#     [i, j]
#     
#     

# ---

# In[ ]:


# find exponents for polys in 2 variables of degree at most "degree"

def coeff_pairs(degree):
    a = degree
    return [[i, j] for i in range(a+1) for j in range(a+1) if i + j <= a]


# In[ ]:


print(coeff_pairs(5))


# **Enumerating global sections of divisors on the Hirzebruch surface $\mathbb F_2$**
# 
# The routine below enumerates the sections of the divisor $eh + fH$ on the Hirzebruch surface $\mathbb F_2 = \mathbb P_{\mathbb P^1}(\mathcal O_{\mathbb P^1} \oplus \mathcal O_{\mathbb P^1}(-2))$. 
# 
# Here $h$ represents the class of (the pullback of) a point on the base $\mathbb P^1$ and $H$ the class of a section.
# 
# The surface can be presented via a bigraded homogeneous coordinate ring $\mathbb C[x, y, z, w]$ where $deg(x) = (1, 0)$, $deg(y) = (-2, 1)$, $deg(z) = (1, 0)$ and $deg(w) = (0, 1)$.
# 
# Using this representation, given a particular class in $eh + fH \in Pic(\mathbb F_2)$, we enumerate all monomials in the variables above of this bidegree, and then dehomogenize by evaluating $y = z = 1$, to obtain a collection of polynomials in variables which we refer to as $x$ and $y$ (which are actually $x/z$ and $yz^2/w$).
# 
# The monomial $x^i y^j$ is represented by the pair
# 
#     [i, j]
#     
#     

# In[ ]:


# enumerate exponents of hirzebruch monomials of a given bidegree

def h_coeff_pairs(bidegree):
    [e, d] = bidegree
    m_list = []
    for j in range(d + 1):
        for i in range(e + 2*j + 1):
            m_list.append([i, j])
    return m_list


# In[ ]:


print(h_coeff_pairs([5, 4]))


# ---

# ## Generic polynomials, partial derivatives, and thier evaluation

# ### Generic polynomial
# 
# The main goal of this class is to repesent and work with a "generic polynomial" in the variables $x$ and $y$ in the affine plane representing global sections of some particular line bundle on our rational surface.
# 
# To produce these requires us to first give an allowable list of monomials in such polynomials, and then construct the generic polynomial as a polynomial of the form
# 
# $\sum a_{i,j} x^i y^j \in F[a_{i,j}, x, y]_{i,j \in S}$ ranging over some set $S$ of allowable pairs $(i,j)$, for $F$ either $\mathbb Q$ or $\mathbb F_p$ for some $p$

# In[ ]:


###################################################################################
# bookkeeping for coefficients of polynomials
###################################################################################

# get named coefficient 'a_i_j' corresponding to a given exponent pair [i, j]
def coeff_from_pair(p):
    return 'a_'+str(p[0])+'_'+str(p[1])

# given a list of exponent pairs, produce a list of the names of these
def coeffs(c_pairs):
    return [coeff_from_pair(p) for p in c_pairs]
#list(coeff_dict(c_pairs).keys())


###################################################################################
###################################################################################
###################################################################################

class GenericPoly:
    def __init__(self):
        self.g = None
        self.partial_dict = dict()
        self.char = 0

    # coeff_pairs is a list of pairs of the form [i, j] representing the monomial term x^i y^j
    def setup(self, coeff_pairs):
        self.coeff_pairs = coeff_pairs
        say("setting up generic polynomial in characteristic " + str(self.char))


        # coeff_name_dict is a dictionary whose keys are strings of the form 'a_i_j' 
        # where [i,j] is one of our monomial pairs and whose values are the pair [i,j]
        # so it looks like: {'a_i_j':[i,j]}
        self.coeff_name_dict = {'a_'+str(p[0])+'_'+str(p[1]):p for p in coeff_pairs}

        # coeff_names is a list of strings of the form 'a_i_j' where [i,j] is one of our monomial pairs
        self.coeff_names = list(self.coeff_name_dict.keys())

        # coeff_name_list is a dictionary (bad naming I know) which gives a numerical ordering to each
        # of the coeff_names
        # i.e. {'a_0_0': 0, 'a_1_0': 1} etcetera
        cns = self.coeff_names
        self.coeff_name_list = {cns[i]:i for i in range(len(cns))}

        if self.char == 0:
            self.R = PolynomialRing(QQ, self.coeff_names + ['x', 'y']);
        else:
            self.R = PolynomialRing(GF(self.char), self.coeff_names + ['x', 'y']);
        self.R.inject_variables(verbose=False);
        self.x = x
        self.y = y

        # var_dict is a dictionary of the form {'a_i_j': a_i_j} where strings are identified with
        # the corresponding variable objects in SAGE
        self.var_dict = {str(var):var for var in self.R.gens()}

        # we take our pairs [i,j] representing monomial x^iy^j with corresponding coeff a_i_j
        # and 
        cd = self.coeff_name_dict

        # monomial dictionary
        md = {c:self.x^cd[c][0]*self.y^cd[c][1] for c in self.coeff_names}

        say("initializing generic polynomial")
        self.g = 0
        i = 0

        t = Timer()
        total = len(self.coeff_names)
        for cn in self.coeff_names:
            sub_start_time = time.time()
            self.g = self.g + self.var_dict[cn]*md[cn]
            sub_end_time = time.time()
            elapsed_time = sub_end_time - sub_start_time
            i = i + 1
#            say_inline(".")
            say_return("assigning monomial " + str(i) + " of " + str(total))
        say("done. time elapsed: " + str(t))

        self.partial_dict[(0, 0)] = self.g

    def set_standard_poly(self, degree):
        self.degree = degree
        self.setup(coeff_pairs(degree))

    def set_h_poly(self, bidegree):
        self.degree = bidegree[0] + 3*bidegree[1] + 4
        # this seems to be the correct max degree of the generic polynomial
        self.setup(h_coeff_pairs(bidegree))

    def generic_partial(self, partial_bidegree):
        b = partial_bidegree
        if sum(partial_bidegree) > self.degree:
            return self.R(0)
        elif b in self.partial_dict:
            return self.partial_dict[b]
        elif b[1] > 0:
#            say_inline("*")
            answer = self.generic_partial((b[0], b[1] - 1)).derivative(y)
            self.partial_dict[b] = answer
            return answer
        elif b[0] > 0:
#            say_inline("*")
            answer = self.generic_partial((b[0] - 1, b[1])).derivative(x)
            self.partial_dict[b] = answer
            return answer
        else:
            print("I shouldn't be here")

    def coeff_vect(self, coeff_poly):
        v = []
        for c in self.coeff_names:
            if coeff_poly == 0:
                entry = 0
            else:
                coeff = self.var_dict[c]
                entry = coeff_poly.coefficient(coeff)
            v.append(entry)
        return v

    def partial_evaluate(self, point, partial_bidegree):
        [p1, p2] = point
        cns = self.coeff_names
        return self.generic_partial(partial_bidegree).subs(x = p1, y = p2)

    def partial_evaluate_to_vector(self, point, partial_bidegree):
        [p1, p2] = point
        cns = self.coeff_names
        cp = self.generic_partial(partial_bidegree).subs(x = p1, y = p2)
        if cp == 0:
            return [0]*len(cns)
        else:
            lpe = list(cp)
            v = [0]*len(cns)
            for p in lpe:
                cname = str(p[1])
                index = self.coeff_name_list[cname]
                coeff_value = p[0]
                v[index] = coeff_value
            return v


# ## Counting Sections with basepoints

# The SectionCounter object takes a generic polynomial from the prior computation:
# $P(x, y) = \sum a_{i,j} x^i y^j \in F[a_{i,j}, x, y]_{i,j \in S}$ ranging over some set $S$ of allowable pairs $(i,j)$
# and a collection of points $p_k$ in the plane with multiplicity $m_k$. It then produces a matrix giving the linear conditions on the $a_{i,j}$ which ensure that the polynomial $P$ vanishes at the points $p_k$ to order $m_k$ (given by the vanishing of the $(m_k - 1)$'th order partial derivatives at the point)

# In[ ]:


class SectionCounter:
    def __init__(self):
        self.generic_poly = None

        # data related to a list of points together with multiplicities

        # points with multiplicity
        self.mpoints = []
        # maximum degree of vanishing of partial derivatives 
        #(tells us how high degree of partial derivatives we need to take later)
        self.max_vanishing = None

        # linear equations on coefficients are added here as they are generated
        self.matrix_rows = []
        self.matrix = None

    # m_list is a list of multiplicities for potential points    
    def set_mpoints(self, m_list):
        self.mpoints = PointMaker(m_list, self.generic_poly.char).mpoints
        self.max_vanishing = max([m[1] for m in self.mpoints])

    def add_matrix_row(self, point, partial_derivative_index_pair):
        ip = partial_derivative_index_pair
        t = Timer()
        ev = self.generic_poly.partial_evaluate_to_vector(point, ip)
#        print("polynomial evaluated in " + str(t.end_report()) + " seconds.")
        self.matrix_rows.append(ev)

    def add_matrix_rows(self, point, multiplicity):
        m = multiplicity
        ips = [(i, j) for i in range(m) for j in range(m) if i + j < m]
        i = 0
        for ip in ips:
            i = i + 1
            self.add_matrix_row(point, ip)
            say_return("evaluating partial " + str(i) + " of " + str(len(ips)+ 1))
#            say_inline(".")
        return len(ips)

    def add_all_matrix_rows(self):
        t = Timer()
        say("constructing equations")
        i = 0
        for mpoint in self.mpoints:
            t2 = Timer()
            i = i + 1
            num_ips = self.add_matrix_rows(mpoint[0], mpoint[1])
            say(str(i) + " of " + \
                  str(len(self.mpoints)) + " points complete (" + str(t2) + "). " + str(len(self.generic_poly.partial_dict)) \
                  + " partials in total computed, " + str(num_ips) + " partials just evaluated.")
        rows = self.matrix_rows
        say("\nconstructing equations done. time elapsed:  " + str(t))
        say("I found " + str(len(rows)) + " equations in " + str(len(rows[0])) + " variables.")    

    def set_matrix(self):
        c = self.generic_poly.char
        say("setting up matrix for equations in characteristic " + str(c))
        rows = self.matrix_rows
        if c == 0:
            self.matrix = Matrix(QQ, rows)
        else:
            self.matrix = Matrix(GF(c), rows)

    def set_dimension(self):
        m = self.matrix
        say_inline("solving equations...")
        t = Timer()
        k = m.right_kernel()
        say("solved. time elapsed: " + str(t))
        self.kernel = k
        self.dimension = k.dimension()

    def solve(self):
        self.add_all_matrix_rows()
        self.set_matrix()
        self.set_dimension()
        d = self.dimension
        say("\ndimension is: " + str(d) + "\n")

    @classmethod
    def new_s(cls, degree, m_list, char):
        gs = cls()
        gp = GenericPoly()
        if char != 0:
            gp.char = char
        gp.set_standard_poly(degree)
        gs.generic_poly = gp
        gs.set_mpoints(m_list)
        return gs

    @classmethod
    def new_h(cls, bidegree, m_list, char):
        gs = cls()
        gp = GenericPoly()
        if char != 0:
            gp.char = char
        gp.set_h_poly(bidegree)
        gs.generic_poly = gp
        gs.set_mpoints(m_list)
        return gs



# ---
# 
# ## Some shortcut routines

# Below are some routines to automate the process of computing the dimension of the linear system corresponding to a randomly chosen set of points with given multiplicites either on $\mathbb P^2$ or on the Hirzebruch surface $\mathbb F_2$. 

# In[ ]:


def solve_s(degree, m_list, char):
    print(r'computing dimension of a linear system on $\mathbb P^2$ of degree ' + str(degree) \
         + " in characteristic " + str(char))
    print(r'with randomly chosen basepoints with multiplicities ' + ", ".join([str(m) for m in m_list]))
    t = Timer()
    gs = SectionCounter.new_s(degree, m_list, char)
    gs.solve()
    print("dimension = " + str(gs.dimension))
    print("Total time elapsed: " + str(t) + "\n\n")

def solve_h(bidegree, m_list, char):
    print(r'computing dimension of a linear system on $\mathbb F_2$ of degree ' + str(bidegree) \
         + " in characteristic " + str(char))
    print("with randomly chosen basepoints with multiplicities " + ", ".join([str(m) for m in m_list]))
    t = Timer()    
    gs = SectionCounter.new_h(bidegree, m_list, char)
    gs.solve()
    gs.solve()
    print("dimension = " + str(gs.dimension))
    print("Total time elapsed: " + str(t) + "\n\n")


# ---
# 
# # Computations

# ## $\mathbb P^2$ blown up at 10 points
# 

# In[ ]:


solve_s(3, [1,60], 0)


# In[ ]:


solve_s(18, [8, 8, 5, 4, 4, 4, 4, 4, 6, 6, 6], 83)


# In[ ]:


solve_s(26, [12, 12, 6, 6, 6, 6, 6, 6, 9, 8, 8], 13)


# In[ ]:


solve_s(36, [17, 16, 8, 8, 8, 8, 8, 12, 12, 12], 3)
solve_s(36, [17, 16, 8, 8, 8, 8, 8, 12, 12, 12], 3803)
solve_s(36, [17, 16, 8, 8, 8, 8, 8, 12, 12, 12], 0)


# In[ ]:


solve_s(79, [36, 36, 18, 18, 18, 18, 18, 26, 26, 26], 317)


# *computation below is still not ready for prime time...*

# # The Hirzebruch surface $\mathbb F_2$ blown up at 9 points

# In[ ]:


solve_h([0, 4], [1, 2, 2, 2, 2, 2, 2, 2, 2], 37)

