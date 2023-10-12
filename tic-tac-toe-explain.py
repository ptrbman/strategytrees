#!/usr/bin/env python3
from StrategyTree import *
from StrategyTree import Root

inout = qtbl2inout_max("tictactoe.qtbl", 9)

inout = [
            ([0, 0, 0, 0], [0]),
            ([0, 0, 0, 1], [0]),
            ([0, 0, 1, 0], [0]),
            ([0, 0, 1, 1], [0]),

            ([0, 1, 0, 0], [0]),
            ([0, 1, 0, 1], [0]),
            ([0, 1, 1, 0], [0]),
            ([0, 1, 1, 1], [0]),


            ([1, 0, 0, 0], [1]),
            ([1, 0, 0, 1], [1]),
            ([1, 0, 1, 0], [1]),
            ([1, 0, 1, 1], [1]),

            ([1, 1, 0, 0], [2]),
            ([1, 1, 0, 1], [2]),
            ([1, 1, 1, 0], [3]),
        ]

print(inout)
root = Root.fromInput(inout)
root.setTemplate("tictactoe")
print(root)

def tryMerge(root):
    for i in range(root.len()):
        for j in range(i+1, root.len()):
            print(".", end='')
            if root.merge_leaves(i, j):
                return True
    return False

while(tryMerge(root)):
    print(".", end='')
    print(root)
