def qtbl2inout_max(filename, STATES=1, THRESHOLD=0.5):
    f = open(filename, "r")
    qtable = []

    for l in f.readlines():
        s = l.strip().split(",")
        states = s[0:STATES]
        actions = s[STATES:]
        qtable.append((states, actions))


    qtable = qtable

    inouts = []
    for (states, actions) in qtable:
        factions = list(map(float, actions))
        fmax = max(factions)
        if fmax >= THRESHOLD:
            actmax = factions.index(max(factions))
            outs = []
            outs.append(actmax)
            inouts.append((list(map(int,states)), outs))
    return inouts


#inout = qtbl2inout_max("tictactoe.qtbl", 9)
#guide = {}
#print(inout)
#for s, a in inout:
#    guide[tuple(s)] = a
#board = [0, 1, 0,
#         2, 2, 0,
#         1, 1, 0]
#print(guide[tuple(board)])
#
###
##   CONDITION
##

from FormulaFinder import FormulaFinder

class Condition():
    def merge_mins(mins1, mins2):
        mins = []
        assert(len(mins1) == len(mins2))
        for i in range(len(mins1)):
            mins.append(min(mins1[i], mins2[i]))
        return mins


    def merge_maxs(maxs1, maxs2):
        maxs = []
        assert(len(maxs1) == len(maxs2))
        for i in range(len(maxs1)):
            maxs.append(max(maxs1[i], maxs2[i]))
        return maxs

    def union(self, cond2):
        allPoints = self.get_points() + cond2.get_points()
        return Multiple(allPoints, Condition.merge_mins(self.mins, cond2.mins), Condition.merge_maxs(self.maxs, cond2.maxs), self.inout + cond2.inout)

class Single(Condition):
    def __init__(self, point, inout):
        self.inout = inout
        self.point = point
        self.mins = point
        self.maxs = point

    def __str__(self):
        return "(x = " + str(self.point) + ")"

    def get_points(self):
        return [self.point]

class Multiple(Condition):
    def __init__(self, points, mins, maxs, inout):
        self.inout = inout
        self.mins = mins
        self.maxs = maxs
        self.points = points

        # Try to create formula
        self.formula = FormulaFinder.find_boolean(self.points, self.mins, self.maxs, 5000)

    def __str__(self):
        return "x in [" + str(self.points) + "] ... (" + FormulaFinder.printBoolean(self.formula, len(self.mins)) + ")"

    def get_points(self):
        return self.points

##
##   TREE
##

class Node():
    def __init__(self, label):
        self.label = label
        self.children = []

    def __str__(self):
        return "Node(" + str(self.label) + ")"

class Leaf():
    def __init__(self):
        self.children = []

    def __str__(self):
        return "Leaf(" + self.label + ")"

class Constants(Leaf):
    def __init__(self, values):
        self.values = values
        self.label = str(values)

    def intersection(self, leaf):
        if type(leaf) is Constants:
            newValues = list(set(self.values).intersection(set(leaf.values)))
            if not newValues:
                return None
            else:
                return Constants(newValues)
        raise Exception("Unhandled intersection: ", self, leaf)

class Formula(Leaf):
    def __init__(self, formula):
        self.formula = formula
        self.label = FormulaFinder.printFormula(formula)


class Root(Node):
    def fromInput(input):
        root = Root("root")
        for i, os in input:
            if os:
                root.children.append((Single(i, [(i, os)]), Constants(os)))
        return root

    def len(self):
        return len(self.children)

    def __str__(self):
        ret = []
        ret.append(self.label)
        if len(self.children) < 10:
            for l, c in self.children:
                ret.append("\t" + str(l) + " --> " + str(c))
        else:
            for l, c in self.children[0:10]:
                ret.append("\t" + str(l) + " --> " + str(c))
            ret.append("\t ...")
        return "\n".join(ret)

    def merge(self, idx, jdx):
        #print("Mering branches ", idx, " and ", jdx)
        assert(idx < jdx)
        cond1 = self.children[idx][0]
        cond2 = self.children[jdx][0]

        newLeaf = self.children[idx][1].intersection(self.children[jdx][1])
        if not newLeaf:
            return False
            raise Exception("leaf intersection failed:", str(self.children[idx][1]), str(self.children[jdx][1]))

        cond = cond1.union(cond2)
        if not cond.formula:
            return False
            raise Exception("Cond union failed:", str(cond1), str(cond2))

        #print("Cond.formula: ", FormulaFinder.printBoolean(cond.formula))
        #print("Cond.inout: ", cond.inout)
        newChild = (cond, newLeaf)
        newChildren = self.children[0:idx] + [newChild] + self.children[idx+1:jdx] + self.children[jdx+1:]
        self.children = newChildren
        return True
        #f = FormulaFinder.find_integer(cond.inout)
        if f:
            #print("---->", f)
            #print("Found: ", FormulaFinder.printFormula(f))
            newChild = (cond, Formula(f))
            newChildren = self.children[0:idx] + [newChild] + self.children[idx+1:jdx] + self.children[jdx+1:]
            self.children = newChildren
            return True
        else:
            return False
