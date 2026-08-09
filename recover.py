"""
Reconstruction algorithms for the t-chromatic symmetric function.

This module implements the t-chromatic symmetric function and the
reconstruction algorithms developed in [REFERENCE] for certain families
of trees. In particular, it contains algorithms for reconstructing
caterpillars with three spine vertices and elongated bistars from the
third principal specialization of the t-chromatic symmetric function.

The remaining functions are auxiliary routines used by these
reconstruction algorithms.

Authors:
    [Author names]

Related paper:
    [Paper title]
    [arXiv link, once available]
"""

from sage.rings.polynomial.polydict import ETuple
from collections import defaultdict

def qtchromatic(G,k):
    CSF = m(G.chromatic_symmetric_function())
    f = 0
    for lam in CSF.monomial_coefficients():
        if len(lam) > k:
            continue
        f += t**len(lam) * m(lam).principal_specialization(n = k,q = q)*CSF[lam]
    return f
    
def caterpillar(comp):
    r"""
    Return the caterpillar graph indexed by ``comp``.
    """
    partial_sums=[sum([comp[j] for j in range(i)]) for i in range(1,len(comp)+1)]
    segments=[[j for j in range(1,comp[0]+1)]]+[[j+1 for j in range(partial_sums[i],partial_sums[i+1])] for i in range(len(comp)-1)]
    Edges=[]
    for i in range(len(segments)):
        Edges+=[[j,segments[i][-1]] for j in segments[i] if j!=segments[i][-1]]
    Edges+=[[partial_sums[i],partial_sums[i+1]] for i in range(len(partial_sums)-1)]
    return(Graph(Edges))

def recover_elongated(f, verbose = False):
    r"""
    Algorithm 1.
    """
    mc = get_mc(f)
    bicolors = [a[0] for a in mc.keys() if a[1] == 2]
    tricolors = [a[0] for a in mc.keys() if a[1] == 3]
    d2,d3 = min(bicolors),min(tricolors)
    k = Integer((min(bicolors) + max(bicolors))/2)
    if verbose:
        print(f"d2 = {d2}, d3 = {d3}, #V = {k}")
    if d3 - d2 < 1: # r is even and b > 2
        r = 2 * d3 - 6
        b = 3 - (d3 - d2)
        a = k - b - r
    else: # is odd or b = 2
        cd33 = f.coefficient([d3,3])
        if d2 == cd33: # r is odd, most difficult case!
            r = 2 * d3 - 5
            if k - r == 4:
                a = 2
                b = 2
            else:
                c1 = f.coefficient([(r+7)/2,3])
                val = 2 * k - 3 + binomial((r+1)/2,2)
                if r >= 2:
                    val += 1
                if c1 == val: # b = 2
                    b = 2
                    a = k - b - r
                elif k - r == 6:
                    a = 3
                    b = 3
                else: # a > 3, b >= 3
                    cplus5 = f.coefficient([(r+9)/2,3])
                    val2 = cplus5 - big_F(k - r - 2, r)
                    if verbose:
                        print(f"final case a > b >= 3: cplus5 = {cplus5}, q^{(r+9)/2} F = {big_F(k - r - 2, r)}, val2 = {val2}")
                    if val2 > binomial(k - r - 4, 2) + 1:
                        b = 3
                        a = k - r - b
                    else: # b > 3
                        a2 = 2
                        a1 = -2*k + 4 + 2 * r
                        a0 = (k-2-r) * (k-r-3)- 2 * val2
                        if verbose:
                            print(f"solve quadratic {a2}x^2+{a1}x+{a0} = 0; x = a-1")
                        roots = solve_quadratic(a2,a1,a0)
                        a = max(roots) + 1
                        b = min(roots) + 1
        else: # b = 2 and r is even
            r = 2 * d3 - 6
            b = 3 - (d3 - d2)
            a = k - b - r
    return [a,r,b]

def recover_three_internal(f, verbose = False):
    r"""
    Algorithm 2.
    """
    mc = get_mc(f)
    bicolors = [a[0] for a in mc.keys() if a[1] == 2]
    k = Integer((min(bicolors) + max(bicolors))/2)
    multiset = [min(bicolors)]
    multiset.append(k-min(bicolors))
    if verbose:
        print(f"Total number of vertices = {k}; Multiset {{a+c-1,b+1}}: {multiset}")
    c43,c53 = f.coefficient([4,3]),f.coefficient([5,3])
    if f.coefficient([3,3]): # b = 1
        a_plus_c = k - 1
        x = a_plus_c - 2
        if verbose:
            print(f"Entering case (1): b = 1, a + c = {a_plus_c}")
        if c53 == 14:
            return [2,1,2]
        elif c53 == 18:
            return [3,1,2]
        elif c53 == 15:
            return  [3,1,3]
        elif c53 == 3 * x + 2 + binomial(x-1,2):
            return [x,1,2]
        elif c53 == 2 * x + 3 + binomial(x-2,2) + 1:
            return [x-1,1,3]
        else:
            if verbose:
                print(f"Quadratic equation {c53} = {2*x + 1} + binomial(c-1,2) + binomial(c-1,2)")
            a2 = 2
            a1 = -2 * x - 4
            a0 = x ** 2 + 5 * x + 4 - 2 * c53
            roots = solve_quadratic(a2,a1,a0)
            return [max(roots),1,min(roots)]
    else: # b > 1
        if verbose:
            print(f"Entering case (2): b > 1")
        if c43 > 1: # min = 2
            if verbose:
                print(f" Entering case (2a): min = 2")
            if c43 == 11:
                return [2,2,2]
            elif c43 == 8:
                return [2,k-4,2]
            elif c43 == 6:
                return [k-4,2,2]
            elif c43 == 4: #
                a_plus_c = k - 2
                if verbose:
                    print(f"  Entering case (2a-iv): b = 2, a + c = {k-2}")
                if c53 == 2 * k + 1:
                    return [3,2,3]
                elif c53 == 2 * k - 1:
                    return [k-5,2,3]
                elif c53 == 2 * k - 3:
                    if verbose:
                        print(f"   Entering case (2a-iv-c)")
                    c63 = f.coefficient([6,3])
                    if c63 == 46:
                        return [4,2,4]
                    elif c63 == 17 + 6 * (k-6) + binomial(k-7,2):
                        return [k-6,2,4]
                    else:
                        a2 = 2
                        a1 = -2 * k + 4
                        a0 = k ^ 2 + 5 * k - 34 - 2 * c63
                        if verbose:
                            print(f"Quadratic a2 = {a2}, a1 = {a1}, a0 = {a0}")
                        roots = solve_quadratic(a2,a1,a0)
                        return [max(roots),2,min(roots)]
            else: # c43 = 3, c = 2
                sub_multiset = [r-1 for r in multiset]
                if verbose:
                    print(f"   Entering case (2a-v) with multiset(a,b) = {sub_multiset} w/ c53 = {c53}")
                if sub_multiset.count(3) == 2:
                    return [3,3,2]
                elif sub_multiset.count(3) == 1:
                    y = sub_multiset[0] if sub_multiset[0] != 3 else sub_multiset[1]
                    if c53 == 2 * y + 9:
                        return [3,k-5,2]
                    elif c53 == y + 10:
                        return [k-5,3,2]
                    else: 
                        print(f"Impossible case")
                else: # no 3 in multiset, c = 2, a,b >= 4
                    return [2*sum(sub_multiset)-c53,c53-sum(sub_multiset),2]
        else: # min >= 3
            b, a_plus_c = mid_and_ends(f,multiset)
            if verbose:
                print(f"Entering case (2b): min >= 3, b = {b} and a + c = {a_plus_c}")
            for try_m in range(3,min(b,a_plus_c//2)+1):
                output = plus_two(b,a_plus_c,try_m,verbose = False)
                val = f.coefficient([try_m+2,3])-output
                if val > 0:
                    mm = try_m
                    break
            mul = Integer(val/2)
            if verbose:
                print(f"minimum value = {mm} and multiplicity is {mul}")
            if mul == 3:
                return [mm,mm,mm]
            elif mul == 2:
                if b == mm:
                    return [k-2*mm,mm,mm]
                else:
                    return [mm,k-2*mm,mm]
            else: # one occurrence
                if b > mm:
                    return [k - b - mm, b,mm]
                output = plus_four(b,a_plus_c,mm,verbose = False)
                val = f.coefficient([mm+4,3]) - output - a_plus_c + 2
                if val == 4 * (b - 1) ^ 2 + 10 * (b - 1) + 6 and (2 * mm + 2 == a_plus_c): # case 1
                    return [mm + 1,mm,mm + 1]
                elif val == 4 * (b - 1) ^ 2 + 8 * (b - 1) + 7 and (2 * mm + 3 == a_plus_c): # case 2
                    return [mm+2,mm,mm+1]
                elif val == 2 * (b - 1) ^ 2 + 3 * (b - 1) + 2 + binomial(a_plus_c-2,2): # case 3
                    return [k - 2 * mm - 1, mm, mm + 1]
                elif val == 4 * (b - 1) ^ 2 + 6 * (b - 1) + 6:# case 4
                    return [mm + 2, mm, mm + 2]
                elif val == 2 * (b - 1) ^ 2 + 3 * (b - 1) + 3 + binomial(a_plus_c-4,2): # case 5
                    return [k - 2 * mm - 2,mm,mm + 2]
                else: # case 6:
                    a2 = 2
                    a1 = -2 * a_plus_c
                    a0 = 2 * (b - 2) * (b - 3) + a_plus_c ^ 2 + (2 * b - 5) * a_plus_c - 2 * val
                    if verbose:
                        print(f"Quadratic a2 = {a2}, a1 = {a1}, a0 = {a0}")
                    roots = solve_quadratic(a2,a1,a0)
                    return [max(roots),mm,min(roots)]

def mid_and_ends(f,multiset):
    r"""
    Implement Algorithm 3: Proposition 5.17 that recover the values of b & a+c from [q^5t^3] & [q^6t^3] using Lemma 5.15; assume min{a,b,c} >=3.
    """
    c53 = f.coefficient([5,3])
    if 4 in multiset:
        b = 3
    elif 5 in multiset:
        if c53 >= 8:
            b = c53 - 4
        elif c53 == 6 or c53 == 4:
            b = 4
        else:
            print(f"Impossible case @multiset = {multiset}")
    elif 6 in multiset:
        if multiset[1] == 6:
            b = 5
        else:
            if c53 > 7:
                b = c53 - 2
            else:
                b = 5
    else: # 
        vals = set()
        vals.update([multiset[0]+1,multiset[0]-1,multiset[1]+1,multiset[1]-1])
        if c53 == multiset[1] + 1:
            b = c53 - 2
        elif c53 == multiset[0] - 1:
            b = c53
        elif multiset[1] - multiset[0] != 2:
            if c53 == multiset[1] - 1:
                b = c53
            else:
                b = c53 - 2
        else: # final case where two values in multiset differ by exactly 2
            # print(f"most difficult case")
            c63 = f.coefficient([6,3])
            x = (sum(multiset)-4)/2
            test_val = binomial(x-1,2)+4*x+7
            # print(f"test_val = {test_val} with x = {x}")
            if c63 == test_val:
                b = c53 - 2 # also know c = 3
            else:
                b = c53
    a_plus_c = sum(multiset)-b
    return int(b), int(a_plus_c)


def plus_two(b,a_plus_c,mm,verbose = False):
    r"""
    Implement Proposition 5.19 that compute the contribution to [t^3q^{m+2}] from:
    101/202/121/212, given the value of b and a+c.
    """
    contribution = 0
    if b == mm:
        contribution += b-1
    for i in range(2*b-mm,b): # 202
        part = binomial(b-1,i) * binomial(a_plus_c-2, mm - 2 * b + i)
        if verbose:
            print(f"Case 2-0-2 @ i = {i}, contribute {part}")
        contribution += part
    for i in range(floor(mm/2)): # 121
        part = binomial(a_plus_c-2,i) * binomial(b-1,mm-2-2*i)
        if verbose:
            print(f"Case 1-2-1 @ i = {i}, contribute {part}")
        contribution += part
    for i in range(floor((mm-3)/2)+1): #212
        part = binomial(b-1,i) * binomial(a_plus_c-2,mm-3-2*i)
        if verbose:
            print(f"Case 2-1-2 @ i = {i}, contribute {part}")
        contribution += part
    return contribution


def plus_four(b,a_plus_c,mm,verbose = False):
    r"""
    Implement Proposition 5.22 that 
    compute the contribution to [t^3q^{m+4}] from:
    101/202/121/212/010/020 given the value of b and a+c. 

    Note: this is only for when [t^3q^{m+2}] can not recover abc. 
    This happens exacly when there is exactly one m in {a,b,c}, 
    i.e., we are actually trying to recover (1) (a,m,c) -- 
    involves solving equations.
    """
    contribution = 0
    for i in range(max(2*b-mm-4,0),b): # (1) 101
        remain = mm + 4 - 2 * b + i
        if i == b-1 and remain < 1:
            continue
        if remain % 2 == 0:
            part = binomial(b-1,i) * binomial(a_plus_c-2, remain/2)
            if verbose:
                print(f"Case 1-0-1 @ i = {i}, contribute {part}")
            contribution += part
    for i in range(2*b-mm-2,b): # 202
        part = binomial(b-1,i) * binomial(a_plus_c-2, mm - 2 * b + 2 + i)
        if verbose and part:
            print(f"Case 2-0-2 @ i = {i}, contribute {part}")
        contribution += part
    for i in range(floor(mm/2)+1): # 121 todo: double check
        # i = number of 2's on ac-leaves
        part = binomial(a_plus_c-2,i) * binomial(b-1,mm-2*i)
        if verbose and part:
            print(f"Case 1-2-1 @ i = {i}, contribute {part}")
        contribution += part
    for i in range(floor((mm-1)/2)+1): #212
        part = binomial(b-1,i) * binomial(a_plus_c-2,mm-1-2*i)
        if verbose and part:
            print(f"Case 2-1-2 @ i = {i}, contribute {part}")
        contribution += part
    if mm >= 4:
        return contribution
    # handle m = 3 cases
    for i in range(min(a_plus_c-2,mm+4-a_plus_c)+1): # 020, only applies when m = 3
        remain = mm + 4 - a_plus_c - i
        part = binomial(a_plus_c-2,i) * binomial(b-1,remain)
        if verbose and part:
            print(f"Case 0-2-0 @ i = {i}, contribute {part}")
        contribution += part
    for i in range(a_plus_c-1): # 010, only applies when m = 3
        remain = mm + 5 - a_plus_c - i
        if i == 0 and remain < 1:
            continue
        if remain % 2 == 0:
            part = binomial(a_plus_c-2,i) * binomial(b-1,remain/2)
            if verbose and part:
                print(f"Case 0-1-0 @ i = {i}, contribute {part}")
    return contribution

def solve_quadratic(a2,a1,a0):
    r"""
    Solve for the quations a2 x^2 + a1 x + a0 = 0.
    """
    x = var('x')
    eqn = a2 * x ** 2 + a1 * x + a0 == 0
    solutions = solve(eqn, x)
    roots = [Integer(r.rhs()) for r in solutions]
    roots = sorted(roots)
    return roots

def get_mc(f):
    r"""
    Since an older version of sagemath does not have f.monomial_coefficients() implemented already. 
    I code it here.
    """
    mc_dict = dict()
    for mon in f.monomials():
        mc_dict[ETuple(mon.degrees())] = f.monomial_coefficient(mon)
    return mc_dict

def membership(alpha):
    if alpha[0] == 1 or alpha[-1] == 1:
        return False
    if alpha[0] < alpha[-1]:
        return False
    return True

def big_F(s,r):
    r"""
    Implement F(s,r) from Lemma A.3. It is only for odd r values.
    """
    half_r = (r-1)/2
    f =  2 * s + half_r * (2 * s + 8) + 8 * binomial(half_r,2) + binomial(half_r,3) + 1 - (r == 3)
    return f