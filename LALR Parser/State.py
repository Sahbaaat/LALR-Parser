# -*- coding: utf-8 -*-
"""


@author: Sahba
"""

from copy import deepcopy

class State:
    state_count = -1
    def __init__(self,new_state):
        self.state= deepcopy(new_state)
        self.actions ={}
        self.parent = ()
        State.state_count +=1
        self.state_num=self.state_count

    def update_goto(self, symbol, i):
        self.actions[symbol] = i.state_num

    def update_parentName(self,I,symbol):
        self.parent = (I.state_num, symbol)


