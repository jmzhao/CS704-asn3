# -*- coding: utf-8 -*-
"""
@author: jmzhao
"""

import random

def generalize(literal_iterable, tester) :
    l = list(literal_iterable)
    inds = random.sample(range(len(l)), len(l))
    for i in inds :
        new_l = l[:i] + l[i+1:]
        if tester(new_l) :
            return generalize(new_l, tester)
    return l