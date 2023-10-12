from FormulaFinder import FormulaFinder
# Used to convert Q-table to an input-output format. For each row
# we pick the action with the highest reward.
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



class Condition():
    ()

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
    def __init__(self, points, mins, maxs, inout, formula):
        self.inout = inout
        self.mins = mins
        self.maxs = maxs
        self.points = points
        self.formula = formula

    def __str__(self):
        return "x in [" + str(self.points) + "] ... (" + FormulaFinder.print_boolean(self.formula, len(self.mins)) + ")"

    def get_points(self):
        return self.points

##
##   STRATEGY TREE
##

#
##  Internal node
#
class Node():
    def __init__(self, label):
        self.label = label
        self.children = []

    def __str__(self):
        return "Node(" + str(self.label) + ")"


#
#  Leaves
#
class Leaf():
    def __init__(self, values):
        self.children = []
        self.values = values
        self.label = str(values)

    def __str__(self):
        return "Leaf(" + self.label + ")"

#
#  Root
#
class Root(Node):
    def fromInput(input):
        root = Root("root")
        for i, os in input:
            if os:
                root.children.append((Single(i, [(i, os)]), Leaf(os)))
        return root

    def len(self):
        return len(self.children)

    def setTemplate(self, template):
        if template not in ["nim", "tictactoe"]:
            raise Exception("Unknown template: ", template)
        else:
            self.template = template
            FormulaFinder.template = template

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



    def merge_conditions(self, cond1, cond2):
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

        points = cond1.get_points() + cond2.get_points()
        mins = merge_mins(cond1.mins, cond2.mins)
        maxs = merge_maxs(cond1.maxs, cond2.maxs)
        inout = cond1.inout + cond2.inout
        formula = FormulaFinder.find_boolean(self.template, points, mins, maxs, 5000)
        return Multiple(points, mins, maxs, inout, formula)

    def merge_leaves(self, idx, jdx):
        assert(idx < jdx)
        l1,l2 = self.children[idx], self.children[jdx]

        # Ensure they have the same values
        if not l1[1].values == l2[1].values:
            return False

        newCond = self.merge_conditions(l1[0], l2[0])

        if not newCond:
            return False

        newChild = (newCond, l1[1])
        newChildren = self.children[0:idx] + [newChild] + self.children[idx+1:jdx] + self.children[jdx+1:]
        self.children = newChildren
        return True
