# -*- coding: utf-8 -*-
"""
Test script for the implemented PDR solver.

@author: jmzhao
"""

import z3
from pdr import *
from testcases import test_cases
import logging

logging.basicConfig(level=logging.INFO)

safty_names = {
    SAFE : "SAFE",
    UNSAFE : "UNSAFE",
    UNKNOWN : "UNKNOWN",
}

print("start testing..")

for i_case, case in enumerate(test_cases) :
    input("Press <Enter> to continue...")
    print("checking for test case %d..."%i_case)
    print("case name: %s"%case['name'])
    print("case description:", case['description'])
    print("init:", case.get('init'))
    print("trans:", case.get('trans'))
    print("post:", case.get('post'))
    if case.get('note') :
        print("Note:", case.get('note'))
    s = input("Input 's(kip)' to skip. Press <Enter> to continue...")
    if case.get('skip') or s in ('s', 'skip') :
        print("Skipped.")
        if case.get('skip-reason') :
            print("Reason: ", case.get('skip-reason'))
        continue
    
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
        if exp is not None and is_tautology(Implies(got, exp))[0] :
            print("Correct!")
        else :
            print("Unexpected.")
            print("Expected:", exp)
        print("Returned:", got)
    if check_res == UNSAFE :
        print("checking counterexample sequence...", end=" ")
        got = ce_seq
        exp = (case['expected_result'].get('ce_start'))
        if exp is not None and is_tautology(Implies(state_to_cube(ce_seq[0]), state_to_cube(exp)))[0] :
            print("Correct!")
        else :
            print("Unexpected.")
            print("Expected:", exp)
        print("Returned:", got)
    if case.get('explanation') :
        print("Explanation:", case.get('explanation'))
        