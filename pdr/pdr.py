# -*- coding: utf-8 -*-
"""
A implementation of roperty-directed reachability (PDR) algorithm based on Z3 
SMT solver.

@author: jmzhao
"""

import z3
from z3 import Bool, Bools, And, Or, Xor, Implies, Not
from z3 import Solver, sat, unsat
import logging

#logging.basicConfig(level=logging.DEBUG)

SAFE = 1
UNSAFE = 0
UNKNOWN = -1

def is_tautology(formula) :
    """Check whether the formula is a tautology, and give a counterexample
    if it is not.
    """
    s = Solver()
    s.add(Not(formula))
    if s.check() == unsat :
        return True, None
    return False, s.model()
    
def state_to_cube(state) :
    return And([b == v 
                for b, v in state.items() if v is not None])

class PDR :
    def __init__(self, bool_pairs) :
        self.bools = [x for x, xp in bool_pairs]
        self.boolps = [xp for x, xp in bool_pairs]
        self.bool_pairs = list(zip(self.bools, self.boolps))
        self.boolp_pairs =  list(zip(self.boolps, self.bools))
#        self.trans = trans
    
    def to_prime(self, formula) :
        return z3.substitute(formula, self.bool_pairs)
    
    def to_origin(self, formula) :
        return z3.substitute(formula, self.boolp_pairs)
        
    def get_state_origin(self, model) :
        return dict((b, model[b]) for b in self.bools)
        
    def get_state_prime(self, model) :
        return dict((b, model[bp]) for b, bp in self.bool_pairs)
    
    def induct(self, R) :
        clauses = list()
        for c in R :
            if self.is_implied(R, c)[0] :
                clauses.append(c)
        return And(clauses)
        
    def is_implied(self, f1, f2, trans) :
        return is_tautology(Implies(And(f1, trans), self.to_prime(f2)))

    def back_prop(self, Rs, init, trans, post, level=0) :
        logging.debug("back_prop(%d): come in with"%(level))
        logging.debug("  init=%s"%init)
        logging.debug("  post=%s"%post)
        logging.debug("  Rs=%s"%Rs)
#        logging.debug("  trans=%s"%trans)
#        logging.debug("waited for keyboard" + str(input("Press anykey...")))
        if len(Rs) == 0 :
            res, counterexample = self.is_implied(init, post, trans)
            logging.debug("back_prop(%d): return from is_implied"%(level))
            logging.debug("  res=%s"%res)
            logging.debug("  counterexample=%s"%counterexample)
            if res : 
                return SAFE, [], None
            else :
                return UNSAFE, None, [
                    self.get_state_origin(counterexample),
                    self.get_state_prime(counterexample),
                ]
        Rn = Rs[-1]
        R0s = Rs[:-1]
        nR0s = R0s
        while True :
            res, counterexample = (self.is_implied(And(*Rn), post, trans)
                if level > 0 else is_tautology(Implies(And(*Rn), post)))
            logging.debug("back_prop(%d): return from is_implied"%(level))
            logging.debug("  res=%s"%res)
            logging.debug("  counterexample=%s"%counterexample)
            if res : break
            state_origin = self.get_state_origin(counterexample)            
            cube = state_to_cube(state_origin)
            Rn = Rn + [(Not(cube))]
            check_res, nR0s, ce_seq = self.back_prop(R0s, init, trans, And(*Rn), level+1)
            logging.debug("back_prop(%d): return from back_prop"%(level))
            logging.debug("  check_res=%s"%check_res)
            logging.debug("  nR0s=%s"%nR0s)
            logging.debug("  ce_seq=%s"%ce_seq)
            if check_res == UNSAFE :
                cube_prev = state_to_cube(ce_seq[-1])
                res, counterexample = self.is_implied(cube_prev, And(*Rn), trans)
#                assert not res
                if level > 0 : ce_seq.append(self.get_state_prime(counterexample))
                return UNSAFE, None, ce_seq
        return SAFE, nR0s + [Rn], None
    
    def forward_prop(self, R0, maxlen, trans) :
        """
        """
        logging.debug("forward_prop: come in with")
        logging.debug("  maxlen=%d"%maxlen)
        logging.debug(" R0=%s"%R0)
        Rs = [R0]
        R = R0
        for _ in range(1, maxlen) :
            nR = list()
            for clause in R :
                res, ce = self.is_implied(And(*R), clause, trans)
                if res : 
                    nR.append(clause)
            Rs.append(nR)
            if is_tautology(And(*R) == And(*nR))[0] :
                break
            R = nR
        return Rs
    
    
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
        Rs = [[]]
        
        while True :
#            input("Press anykey...")
            n = len(Rs)
            check_res, nRs, ce_seq = self.back_prop(Rs, init, trans, post)
            logging.info("pdr: return from back_prop")
            logging.info("  check_res=%s"%check_res)
            logging.info("  nRs=%s"%nRs)
            logging.info("  ce_seq=%s"%ce_seq)
            if check_res == UNSAFE :
                return UNSAFE, None, ce_seq
#            R1 = self.cleanse(And(R1, clause))
            Rs = self.forward_prop(nRs[0], n + 1, trans)
            logging.debug("pdr: return from forward_prop")
            logging.debug("  Rs=%s"%Rs)
            if is_tautology(And(*Rs[-1]) == And(*Rs[-2]))[0] :
                return SAFE, And(*Rs[-1]), None
