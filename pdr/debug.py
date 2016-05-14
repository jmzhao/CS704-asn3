# -*- coding: utf-8 -*-
"""
@author: jmzhao
"""

import test 
import logging

logging.basicConfig(level=logging.DEBUG)

#test.test([test.test_cases.get_by(name="marginal-algebra-safe")])
test.test([case for case in test.test_cases if case['name'] != "marginal-algebra-unsafe"])