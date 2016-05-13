# -*- coding: utf-8 -*-
"""
Test cases.

@author: jmzhao
"""

from z3 import Bool, Bools, And, Or, Xor, Not, Implies
from pdr import SAFE, UNSAFE, UNKNOWN

a, b, c, d, e, f, x, y, z = Bools("a b c d e f x y z")
ap, bp, cp, dp, ep, fp, xp, yp, zp = Bools("a' b' c' d' e' f' x' y' z'")

class SearchableList (list) :
    def get_by(self, **kvargs) :
        for obj in self :
            if all(obj.get(k) == v for k, v in kvargs.items()) :
                return obj
  
test_cases = SearchableList()

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
    'name' : "easy-counter-safe",
    'description' : """An safe case for a counter that increases two to the
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
    'name' : "easy-counter-unsafe",
    'description' : """An unsafe case for a counter that increases two to the
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
    'trans' : And(fp == e, ep == d, 
                  dp == Xor(c, True), 
                  cp == Not(Xor(b, c)),
                  bp == Xor(a, Or(b, c)), 
                  ap == False),
    'expected_result' : {
        'check_res' : SAFE,
        'inv' : And(Not(a), Implies(And(b, c), Not(Or(d, e)))), 
        'explanation' : """
  Sorry, I was not sure about the loosest invariant. Maybe it is abcdef <= 25.
  However, my program seems to give abcdef <= 24, which is the same as the 
  postscondition.
  """
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
    abcdef += 26 # the place that makes the program unsafe
    abcdef >>= 1
  }
  assert abcdef <= 24
  </pseudocode>""",
    'bool_pairs' : test_cases[-1]['bool_pairs'],
    'init' : test_cases[-1]['init'],
    'post' : And(Not(a), Implies(And(b, c), Not(Or(d, e, f)))),
    'trans' : And(fp == Xor(e, True), 
                  ep == Xor(d, e), 
                  dp == Not(Xor(c, And(d, e))), 
                  cp == Not(Xor(b, Or(c, And(d, e)))),
                  bp == Xor(a, Or(b, c, And(d, e))), 
                  ap == False),
    'expected_result' : {
        'check_res' : UNSAFE,
        'ce_start' : {a: False, b: False}, 
        'explanation' : "Any state within the initial condition."
    },
    'note' : "This will last >10s on my laptop.",
#    'skip' : True,
}
test_cases.append(case)  

def add_out(x, y, c) :
    return Xor(Xor(x, y), c)
def add_carry(x, y, c) :
    return Or(And(x, y), And(y, c), And(x, c))

case = {
    'name' : "adder",
    'description' : """A 3-bit adder. This is a template for other adder cases.
  <pseudocode>
  forever {
    abc += def
  }
  </pseudocode>""",
    'bool_pairs' : [(a, ap), (b, bp), (c, cp), (d, dp), (e, ep), (f, fp)],
    'trans' : And(fp == f, 
                  ep == e, 
                  dp == d, 
                  cp == add_out(c, f, False), z == add_carry(c, f, False),
                  bp == add_out(b, e, z), y == add_carry(b, e, z), 
                  ap == add_out(a, d, y)),
    'note' : "This will be skipped because it is a case template.",
    'skip' : True,
    'skip-reason' : "This is a case template rather than a real test case."
}
test_cases.append(case)  

case = {
    'name' : "adder-safe",
    'description' : """A 3-bit adder. The equivalent program is
  <pseudocode>
  assert abc == 0
  forever {
    abc += def
  }
  assert True
  </pseudocode>""",
    'bool_pairs' : test_cases.get_by(name="adder")['bool_pairs'],
    'init' : Not(Or(a, b, c)),
    'post' : And(),
    'trans' : test_cases.get_by(name="adder")['trans'],
    'expected_result' : {
        'check_res' : SAFE,
        'inv' : True, 
        'explanation' : "Any set of states."
    },
}
test_cases.append(case)  

case = {
    'name' : "adder-unsafe",
    'description' : """A 3-bit adder. The equivalent program is
  <pseudocode>
  assert abc != 0 and f == 1
  forever {
    abc += def
  }
  assert abc != 0
  </pseudocode>""",
    'bool_pairs' : test_cases.get_by(name="adder")['bool_pairs'],
    'init' : And(Or(a, b, c), f),
    'post' : Or(a, b, c),
    'trans' : test_cases.get_by(name="adder")['trans'],
    'expected_result' : {
        'check_res' : UNSAFE,
        'inv' : None,
        'ce_start' : {f: True}, 
        'explanation' : "Any state that def is odd.",
    },
}
test_cases.append(case)  

case = {
    'name' : "adder-unsafe2",
    'description' : """a 3-bit adder. The equivalent program is
  <pseudocode>
  assert abc == 0 and f == 0
  forever {
    abc += def
  }
  assert abc != 0
  </pseudocode>""",
    'bool_pairs' : test_cases.get_by(name="adder")['bool_pairs'],
    'init' : And(Or(a, b, c), Not(f)),
    'post' : Or(a, b, c),
    'trans' : test_cases.get_by(name="adder")['trans'],
    'expected_result' : {
        'check_res' : UNSAFE,
        'inv' : None,
        'ce_start' : dict.fromkeys((e, f, b, c), False), # all zero
    },
}
test_cases.append(case) 

case = {
    'name' : "adder-safe2",
    'description' : """A 3-bit adder. The equivalent program is
  <pseudocode>
  assert abc == 7 and def == 2
  forever {
    abc += def
  }
  assert abc > 0
  </pseudocode>""",
    'bool_pairs' : test_cases.get_by(name="adder")['bool_pairs'],
    'init' : And(a, b, c, Not(d), e, Not(f)),
    'post' : Or(a, b, c),
    'trans' : test_cases.get_by(name="adder")['trans'],
    'expected_result' : {
        'check_res' : SAFE,
        'inv' : True, 
        'explanantion' : "Sorry, I don't know the loosest invariant."
    },
    'note' : "**This case will run for a while (maybe > 60s).**"
}
test_cases.append(case)  