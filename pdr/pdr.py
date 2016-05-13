# -*- coding: utf-8 -*-
"""
A implementation of roperty-directed reachability (PDR) algorithm based on Z3 
SMT solver.

@author: jmzhao

Types
----------
@CheckRes in (SAFE, UNSAFE, UNKNOWN) # the checking result

@Var = @z3.Bool(...) # state variable

@Cube = @z3.And(...) # a conjunction

@Clause = @z3.Not(Cube) # negation of a conjunction

@Formula (Var, Cube, Clause) = z3.BoolRef 

@TraceElem = [Clause] # represents a CNF

@Trace = [TraceElem] # the trace mentioned in [1]

@Model = z3.ModelRef # models returns by z3.Solver.model()

@State = @{Var : bool} # represents a particular program state.
# Note this does not neccessarily assign to all state variables.

References
----------
[1] Een, Niklas, Alan Mishchenko, and Robert Brayton. "Efficient implementation
of property directed reachability." Formal Methods in Computer-Aided Design 
(FMCAD), 2011. IEEE, 2011.
"""

import z3
from z3 import Bool, Bools, And, Or, Xor, Implies, Not
from z3 import Solver, sat, unsat
import logging

__all__ = ['SAFE', 'UNSAFE', 'UNKNOWN', 'is_tautology', 'state_to_cube', 'PDR']

#logging.basicConfig(level=logging.DEBUG)

SAFE = 1
UNSAFE = 0
UNKNOWN = -1

def is_tautology(formula) :
    """Check whether the formula is a tautology, and give a counterexample
    if it is not.
    
    Parameters
    ----------
    formula@Formula - The formula to be tested.
    
    Returns
    ----------
    check_res@bool - Whether the formula is a tautology.
    
    counterexample@Model - None if the formula is a tautology, otherwise a 
    counterexample.
    """
    s = Solver()
    s.add(Not(formula))
    if s.check() == unsat :
        return True, None
    return False, s.model()
    
def state_to_cube(state) :
    """Convert a program state to a cube.
    
    Parameters
    ----------
    state@State - A (possibly partial) program state.
    
    Returns
    ----------
    cube@Cube - The cube (conjunction) that fits exactly with the given state.
    """
    return And([b == v 
                for b, v in state.items() if v is not None])

class PDR :
    """A implementation of roperty-directed reachability (PDR) algorithm that 
    tries to prove the safety."""
    
    def __init__(self, bool_pairs) :
        self.bools = [x for x, xp in bool_pairs]
        self.boolps = [xp for x, xp in bool_pairs]
        self.bool_pairs = list(zip(self.bools, self.boolps))
        self.boolp_pairs =  list(zip(self.boolps, self.bools))
#        self.trans = trans
    
    def to_prime(self, formula) :
        """Convert all original state variables into primed state variables."""
        return z3.substitute(formula, self.bool_pairs)
    
    def to_origin(self, formula) :
        """Convert all primed state variables into original state variables."""
        return z3.substitute(formula, self.boolp_pairs)
        
    def get_state_origin(self, model) :
        """Generate the program state that corresponds to all the **original** 
        variables in the given model."""
        return dict((b, model[b]) for b in self.bools)
        
    def get_state_prime(self, model) :
        """Generate the program state that corresponds to all the **prime** 
        variables in the given model."""
        return dict((b, model[bp]) for b, bp in self.bool_pairs)
    
    def induct_naive(self, R, trans) :
        """One step of clause-based induction among trance elements.
        
        Namely, $R' = {clause | clause <- R, R ->_{trans} clause}$.
        
        Parameters
        ----------
        R@TraceElem - A trace element to compute its induction.
        
        trans@Formula - The transition.
        
        Returns
        ----------
        nR@TraceElem - The trace element after one step of induction.
        """
        nR = list()
        for c in R :
            if self.is_implied(And(*R), c, trans)[0] :
                nR.append(c)
        return nR
        
    def is_implied(self, f1, f2, trans) :
        """Check if f2 can be implied by f1 after one step of transition.
        
        Returns
        ----------
        check_res@bool - Whether the implication holds.
        
        counterexample@Model - None if the implication holds, otherwise a 
        counterexample.
        """
        return is_tautology(Implies(And(f1, trans), self.to_prime(f2)))

    def back_prop(self, Rs, init, trans, post, level=0) :
        """Back-propagation of the trace. Refines from the back of the trace
        regarding the postcondition.
        
        Parameters
        ----------
        Rs@Trace - Current trace.
        
        init@Formula - Inintial condition.
        
        trans@Formula - Transition. This is the only place that involves prime
        variables.
        
        post@Formula - Postcondition.
        
        level@Int (interal) - Track the depth of recursion.
        
        Returns
        ----------
        check_res@CheckRes - SAFE or UNSAFE.
        
        nRs@Trace - Updated trace if check_res == SAFE. Otherwise None.
        
        ce_seq@[State] - The counterexample sequence from the initial condition
        to the negation of the postcondition, if check_res == UNSAFE. Otherwise
        None.
        """
        logging.debug("back_prop(%d): come in with"%(level))
        logging.debug("  init=%s"%init)
        logging.debug("  post=%s"%post)
        logging.debug("  Rs=%s"%Rs)
#        logging.debug("  trans=%s"%trans)
#        logging.debug("waited for keyboard" + str(input("Press anykey...")))
        if len(Rs) == 0 : ## If we reached the initial condition during backing 
            res, counterexample = self.is_implied(init, post, trans)
            logging.debug("back_prop(%d): return from is_implied"%(level))
            logging.debug("  res=%s"%res)
            logging.debug("  counterexample=%s"%counterexample)
            if res : ## The new obligation is not contradictory to the initial
                return SAFE, [], None
            else : ## The new obligation is not satisfiable
                return UNSAFE, None, [
                    self.get_state_origin(counterexample), ## a counterexample state starting from the initial
                    self.get_state_prime(counterexample),
                ]
        Rn = Rs[-1]
        R0s = Rs[:-1]
        nR0s = R0s
        while True :
            res, counterexample = (self.is_implied(And(*Rn), post, trans)
                if level > 0 else is_tautology(Implies(And(*Rn), post)))
            ## refine for $Rn -> post$ if this is the top level
            ## otherwise for $Rn ->_{trans} post$
            logging.debug("back_prop(%d): return from is_implied"%(level))
            logging.debug("  res=%s"%res)
            logging.debug("  counterexample=%s"%counterexample)
            if res : break ## exit if the last trace element agree with post
            state_origin = self.get_state_origin(counterexample)            
            cube = state_to_cube(state_origin)
            Rn = Rn + [(Not(cube))] ## eclude the counterexample from the last trace element
            check_res, nR0s, ce_seq = self.back_prop(R0s, init, trans, And(*Rn), level+1)
            ## recursively refine back to the rest of trace
            logging.debug("back_prop(%d): return from back_prop"%(level))
            logging.debug("  check_res=%s"%check_res)
            logging.debug("  nR0s=%s"%nR0s)
            logging.debug("  ce_seq=%s"%ce_seq)
            if check_res == UNSAFE : ## violates the initla while recursion
                cube_prev = state_to_cube(ce_seq[-1])
                res, counterexample = self.is_implied(cube_prev, And(*Rn), trans)
                ## find a counterexample state for the current step
#                assert not res
                if level > 0 : ce_seq.append(self.get_state_prime(counterexample))
                return UNSAFE, None, ce_seq
        return SAFE, nR0s + [Rn], None
    
    def forward_prop(self, R0, maxlen, trans) :
        """Generate a new trace from trace element R0.
        
        Parameters
        ----------
        R0@TraceElem - Starting trace element.
        
        maxlen@Int - Maximum length of the trace.
        
        trans@Formula - Transition. This is the only place that involves prime
        variables.
        
        Returns
        ----------
        Rs@Trace - The constructed trace. Either len(Rs) == maxlen or 
        Rs[-1] is implicationally equivalent to Rs[-2].
        """
        logging.debug("forward_prop: come in with")
        logging.debug("  maxlen=%d"%maxlen)
        logging.debug(" R0=%s"%R0)
        Rs = [R0]
        R = R0
        for _ in range(1, maxlen) :
            nR = self.induct_naive(R, trans)
#            nR = list()
#            for clause in R :
#                res, ce = self.is_implied(And(*R), clause, trans)
#                if res : 
#                    nR.append(clause)
            Rs.append(nR)
            if is_tautology(And(*R) == And(*nR))[0] :
                break ## when the newly generated trace elements are equivalent
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
        
        ## main loop
        while True : 
            ## loop until:
            ## 1. the last element in the trace are equivalent; or
            ## 2. found something disagree with the initial condition.
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
