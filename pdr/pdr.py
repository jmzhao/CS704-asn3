# -*- coding: utf-8 -*-
"""
A implementation of roperty-directed reachability (PDR) algorithm based on Z3 
SMT solver.

@author: jmzhao
"""

import z3
from z3 import Bool, Bools, And, Or, Xor, Implies, Not
from z3 import Solver, sat, unsat

SAFE = 1
UNSAFE = 0
UNKNOWN = -1

def is_tautology(formula) :
    s = Solver()
    s.add(Not(formula))
    if s.check() == unsat :
        return True, None
    return False, s.model()

def is_equal(formula1, formula2) :
    return is_tautology(formula1 == formula2)

class PDR :
    def __init__(self, bool_pairs, trans) :
        self.bool_pairs = (bool_pairs)
        self.bools = [x for x, xp in bool_pairs]
        self.boolps = [xp for x, xp in bool_pairs]
        self.trans = trans
    
    def to_prime(self, formula) :
        return z3.substitute(formula, self.bool_pairs)
    
    def induct(self, R) :
        clauses = list()
        for c in R :
            if self.is_implied(R, c)[0] :
                clauses.append(c)
        return And(clauses)
        
    def is_implied(self, f1, f2) :
        return is_tautology(Implies(And(f1, self.trans), self.to_prime(f2)))

    def back_prop(self, Rs, init, trans, post) :
        Rn = Rs[-1]
        R0s = Rs[:-1]
        while True :
            res, counterexample = is_tautology(Implies(And(Rn, trans), self.to_prime(post)))
    
    def forward_prop(self, R1, maxlen, trans) :
        pass
    
    
    def pdr(self, init, trans, post) :
        """
        Determine the reachabilty given a set of initial states, a transition rela-
        tion and a postcondition. Namely, if $init ->^*_{trans} post$, where 
        $->^*_{trans}$ is the transitive closure of relatoin $trans$.
        
        Parameters
        ----------
        init -- The set of inintial sates.
        
        trans -- The transition relation.
        
        post -- The postcondition.
        
        Returns
        ----------
        check_res -- check_res is SAFE if starting from init will
        not violate post according to trans; otherwise UNSAFE.
        
        inv -- If check_res is SAFE, inv will be the inductive invariant.
        
        counter_seq -- If check_res is UNSAFE, 
        counter_seq will be a sequence of states beginning in init and ending in 
        ~post(x).
        """
        Rs = list(True)
        
        while True :
            n = len(Rs)
            check_res, clause, counterexample = back_prop(Rs, init, trans, post)
            if check_res == UNSAFE :
                return UNSAFE, None, self.extend(counterexample, trans, post)
            R1 = self.cleanse(And(R1, clause))
            Rs = self.forward_prop(R1, n + 1, trans)
            if is_equal(Rs[-1], Rs[-2])[0] :
                return SAFE, Rs[-1], None
            
x, y, z = Bools("x y z")
xp, yp, zp = Bools("x' y' z'")
init = And(x, y, z)
trans = And(zp == Xor(x, y), xp == y, yp == Or(x, z))
post = x
check_res = SAFE
inv = And(x, y)
pdr = PDR([(x, xp), (y, yp), (z, zp)])