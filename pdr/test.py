# -*- coding: utf-8 -*-
"""
A implementation of roperty-directed reachability (PDR) algorithm based on Z3 
SMT solver.

@author: jmzhao
"""

import z3
from pdr import *
import logging

logging.basicConfig(level=logging.INFO)

x, y, z = Bools("x y z")
xp, yp, zp = Bools("x' y' z'")
  
test_cases = list()

case = {
    'name' : "easy-safe",
    'description' : "An easy safe case used while debugging",
    'bool_pairs' : [(x, xp), (y, yp), (z, zp)],
    'init' : And(x, y, z),
    'post' : x,
    'trans' : And(zp == Xor(x, y), xp == y, yp == Or(x, z)),
    'expected_result' : {
        'check_res' : SAFE,
        'inv' : And(x, y),
    },
}
test_cases.append(case)  

case = dict(test_cases[-1])
case.update({
    'name' : "easy-unsafe",
    'description' : "An easy unsafe case used while debugging",
    'init' : Not(Or(x, y, z)),
    'expected_result' : {
        'check_res' : UNSAFE,
        'ce_start' : {z: False, y: False, x: False},
    },
})
test_cases.append(case) 

safty_names = {
    SAFE : "SAFE",
    UNSAFE : "UNSAFE",
    UNKNOWN : "UNKNOWN",
}

for i_case, case in enumerate(test_cases) :
    print("checking for test case %d..."%i_case)
    print("case name: %s"%case['name'])
    print("case description:", case['description'])
    print("init:", case['init'])
    print("trans:", case['trans'])
    print("post:", case['post'])
    
    pdr = PDR(case['bool_pairs'])
    check_res, inv, ce_seq = pdr.pdr(case['init'], case['trans'], case['post'])
    logging.info("return from pdr.pdr:")
    logging.info("  check_res=%s"%check_res)
    logging.info("  inv=%s"%inv)
    logging.info("  ce_seq=%s"%ce_seq)
    
    print("checking safety...", end=" ")
    got = check_res
    exp = case['expected_result'].get('check_res')
    if got == exp :
        print("Correct!")
    else :
        print("Unexpected.")
        print("Expected:", safty_names[exp])
    print("Returned:", safty_names[got])
    if check_res == SAFE :
        print("checking invariant...", end=" ")
        got = z3.simplify(inv)
        exp = case['expected_result'].get('inv')
        if is_tautology(inv == exp) :
            print("Correct!")
        else :
            print("Unexpected.")
            print("Expected:", exp)
        print("Returned:", got)
    if check_res == UNSAFE :
        print("checking counterexample sequence...", end=" ")
        got = ce_seq
        exp = (case['expected_result'].get('ce_start'))
        if is_tautology(state_to_cube(ce_seq[0]) == state_to_cube(exp)) :
            print("Correct!")
        else :
            print("Unexpected.")
            print("Expected:", exp)
        print("Returned:", got)
        