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

a, b, c, d, e, f, x, y, z = Bools("a b c d e f x y z")
ap, bp, cp, dp, ep, fp, xp, yp, zp = Bools("a' b' c' d' e' f' x' y' z'")
  
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


case = {
    'name' : "easy-adder-safe",
    'description' : """An safe case for an adder that increases two to the
  binary representation $\hat{abcd}$ upon each step. The equivalent program is
  <pseudocode>
  assert abcd == 0
  forever {
    abcd += 2  # overflow bit is ignored
  }
  assert mod(abcd, 2) == 0
  </pseudocode>""",
    'bool_pairs' : [(a, ap), (b, bp), (c, cp), (d, dp)],
    'init' : And(Not(a), Not(b), Not(c), Not(d)),
    'post' : Not(d),
    'trans' : And(dp == d, cp == Xor(c, True), bp == Xor(b, c), ap == Xor(a, And(b, c))),
    'expected_result' : {
        'check_res' : SAFE,
        'inv' : Not(d),
    },
}
test_cases.append(case)  

case = {
    'name' : "easy-adder-unsafe",
    'description' : """An unsafe case for an adder that increases two to the
  binary representation $\hat{abcd}$ upon each step. The equivalent program is
  <pseudocode>
  assert abcd == 1  # the place that makes the program unsafe
  forever {
    abcd += 2  # overflow bit is ignored
  }
  assert mod(abcd, 2) == 0
  </pseudocode>""",
    'bool_pairs' : test_cases[-1]['bool_pairs'],
    'init' : And(Not(a), Not(b), Not(c), (d)),
    'post' : Not(d),
    'trans' : test_cases[-1]['trans'],
    'expected_result' : {
        'check_res' : UNSAFE,
        'ce_start' : {d: True},
    },
}
test_cases.append(case)  

case = {
    'name' : "marginal-algebra-safe",
    'description' : """An safe case for some combination of algebra operations.
  The equivalent program is
  <pseudocode>
  assert abcdef < 16
  forever {
    abcdef += 24
    abcdef >>= 1
  }
  assert abcdef <= 24
  </pseudocode>""",
    'bool_pairs' : [(a, ap), (b, bp), (c, cp), (d, dp), (e, ep), (f, fp)],
    'init' : And(Not(a), Not(b)),
    'post' : And(Not(a), Implies(And(b, c), Not(Or(d, e, f)))),
    'trans' : And(fp == e, ep == d, dp == Xor(c, True), cp == Xor(b, c),
                  bp == Xor(a, And(b, c)), ap == False),
    'expected_result' : {
        'check_res' : SAFE,
        'inv' : "sorry, I don't know. Maybe the same as the initial. Or abcdef <= 23 ", 
    },
}
test_cases.append(case)  

case = {
    'name' : "marginal-algebra-unsafe",
    'description' : """An unsafe case for some combination of algebra operations.
  The equivalent program is
  <pseudocode>
  assert abcdef < 16
  forever {
    abcdef += 28 # the place that makes the program unsafe
    abcdef >>= 1
  }
  assert abcdef <= 24
  </pseudocode>""",
    'bool_pairs' : test_cases[-1]['bool_pairs'],
    'init' : test_cases[-1]['init'],
    'post' : And(Not(a), Implies(And(b, c), Not(Or(d, e, f)))),
    'trans' : And(fp == e, ep == Xor(d, True), dp == Xor(c, d), 
                  cp == Xor(b, And(c, d)),
                  bp == Xor(a, And(b, c, d)), ap == False),
    'expected_result' : {
        'check_res' : UNSAFE,
        'ce_seq' : {}, # any state within the initial state
    },
}
test_cases.append(case)  

safty_names = {
    SAFE : "SAFE",
    UNSAFE : "UNSAFE",
    UNKNOWN : "UNKNOWN",
}

for i_case, case in enumerate(test_cases[-2:]) :
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
        if is_tautology(Implies(state_to_cube(ce_seq[0]), state_to_cube(exp))) :
            print("Correct!")
        else :
            print("Unexpected.")
            print("Expected:", exp)
        print("Returned:", got)
        