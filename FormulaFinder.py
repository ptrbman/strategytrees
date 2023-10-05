def op_multiplication(op1, op2):
    return "(* " + str(op1) + " " + str(op2) + ")"

def op_if(op1, op2):
    return "(ite (= " + op1 + " 0) 0 " + op2 + ")"

def op_remainder(op1, op2):
    return "(mod " + str(op1) + " " + str(op2) + ")"

def op_def_div(node, opcode, op, op1, op2, pairs):
    lines = []
    lines.append("(assert (=> " + op_eq(node, opcode) + " (and\n")
    for i in range(pairs):
        lines.append("\t" + op_eq(node + "val_" + str(i), op(op1 + "val_" + str(i), op2 + "val_" + str(i))) + "\n")
        lines.append("\t(not " + op_eq(op2 + "val_" + str(i), str(0)) + ")\n")
    lines.append(")))\n")
    return "".join(lines)

def gen_points(mins, maxs):
    assert(len(mins) == len(maxs))
    if len(mins) == 0:
        return [[]]
    points = []
    min, max = mins[0], maxs[0]
    rec = gen_points(mins[1:], maxs[1:])
    for r in rec:
        for m in range(min, max+1):
            points.append([m] + r)

    return points


from z3 import *

class FormulaFinder():
    def op_addition(op1, op2):
        return Int(op1) + Int(op2)

    def op_subtraction(op1, op2):
        return Int(op1) - Int(op2)

    def op_remainder(op1, op2):
        return Int(op1) % Int(op2)

    def rel_equality(op1, op2):
        return Int(op1) == Int(op2)

    def rel_leq(op1, op2):
        return Int(op1) <= Int(op2)

    # |+,-,*,rem,if| = 4
    OPS = 3
    def add_node(s, name, child1, child2, pairs):
        node_vals = [Int(name + "val_" + str(i)) for i in range(pairs)]
        s.add(0 <= Int(name))
        s.add(Int(name) <= FormulaFinder.OPS-1)

        #ops = [(0, op_addition), (1, op_subtraction), (2, op_multiplication), (3, op_if)]
        ops = [(0, FormulaFinder.op_addition), (1, FormulaFinder.op_subtraction)]
        div_ops = [(2, FormulaFinder.op_remainder)]

        for (opcode, op) in ops:
            lhs = Int(name) == opcode
            rhs = And([Int(name + "val_" + str(i)) == op(child1 + "val_" + str(i), child2 + "val_" + str(i)) for i in range(pairs)])
            s.add(Implies(lhs, rhs))

        for (opcode, op) in div_ops:
            lhs = Int(name) == opcode
            rhs = And([And(Int(name + "val_" + str(i)) == op(child1 + "val_" + str(i), child2 + "val_" + str(i)), Int(child1 + "val_" + str(i)) > 0, Int(child2 + "val_" + str(i)) > 0) for i in range(pairs)])
            s.add(Implies(lhs, rhs))


    # |=,<=| = 2
    RELS = 1
    def add_node_rel(s, name, child1, child2, pairs):
        node_vals = [Int(name + "val_" + str(i)) for i in range(pairs)]
        s.add(0 <= Int(name))
        s.add(Int(name) <= FormulaFinder.RELS-1)

        #ops = [(0, op_addition), (1, op_subtraction), (2, op_multiplication), (3, op_if)]
        rels = [(0, FormulaFinder.rel_equality), (1, FormulaFinder.rel_leq)]
        #div_ops = [(4, op_remainder)]

        for (opcode, op) in rels:
            lhs = Int(name) == opcode
            rhs = And([Bool(name + "val_" + str(i)) == op(child1 + "val_" + str(i), child2 + "val_" + str(i)) for i in range(pairs)])
            s.add(Implies(lhs, rhs))




    # |input, const| = 2
    LEAFS = 2
    def add_leaf(s, name, pairs):
        leaf = Int(name)
        leaf_const = Int(name + "const")
        leaf_vals = [Int(name + "val_" + str(i)) for i in range(pairs)]
        s.add(0 <= leaf)
        s.add(leaf <= FormulaFinder.LEAFS-1)
        ### INPUT
        s.add(Implies(Int(name) == 0, And([Int(name + "val_" + str(i)) == Int("input_" + str(i)) for i in range(pairs)])))

        ### CONST
        s.add(Implies(Int(name) == 1, And([Int(name + "val_" + str(i)) == Int(name + "const") for i in range(pairs)])))

    def add_leaf(s, name, dim, pairs):
        leaf = Int(name)
        leaf_const = Int(name + "const")
        leaf_vals = [Int(name + "val_" + str(i)) for i in range(pairs)]
        s.add(0 <= leaf)
        s.add(leaf <= dim)
        ### INPUT
        disjunction = []
        for d in range(dim):
            disjunction.append(Implies(Int(name) == d, And([Int(name + "val_" + str(i)) == Int("input_" + str(i) + "_" + str(d)) for i in range(pairs)])))
        s.add(And(disjunction))
        ### CONST
        s.add(Implies(Int(name) == dim, And([Int(name + "val_" + str(i)) == Int(name + "const") for i in range(pairs)])))



    def add_output(s, name, inout):
        outs = list(map(lambda x : x[1], inout))
        for idx, out in enumerate(outs):
            if len(out) >= 1:
                s.add(Or([Int(name + "val_" + str(idx)) == Int("output_" + str(idx) + "_" + str(jdx)) for jdx in range(len(out))]))

    def add_bool_output(s, name, count):
        for i in range(count):
            s.add(Bool(name + "val_" + str(i)) == Bool("output_" + str(i)))

    def find_integer(inout):
        print("find_integer:", inout)
        s = Solver()
        s.set("timeout", 5000)
        # First create input-output-nodes
        pairs = len(inout)

        # Generate input/output variables
        inputs = []
        outputs = []
        for (idx, (i, outs)) in enumerate(inout):
            new_input = Int("input_" + str(idx))
            inputs.append(new_input)
            s.add(new_input == i)
            os = []
            const = []
            for jdx, o in enumerate(outs):
                new_output = Int("output_" + str(idx) + "_" + str(jdx))
                const.append(new_output == o)
            s.add(Or(const))


        FormulaFinder.add_leaf(s, "l1", pairs)
        FormulaFinder.add_leaf(s, "l2", pairs)
        FormulaFinder.add_node(s, "root", "l1", "l2", pairs)
        FormulaFinder.add_output(s, "root", inout)
        if s.check() == sat:
            model = s.model()
            interest = ["root",
                    "l1", "l1const",
                    "l2", "l2const",
                   ]
            ret = {}
            for x in interest:
                ret[x] = model[Int(x)]
            return ret

        else:
            return None


    ##      root
    ##    n1    l3
    ##  l1  l2

    def find_boolean_single(points, mins, maxs, timeout=5000):
        print("find_boolean", points, mins, maxs, timeout)
        s = Solver()
        s.set("timeout", timeout)
        # Generate input/output variables
        inputs = []
        outputs = []
        pairs = 0

        idx = 0
        for point in gen_points(mins, maxs):
            if len(point) == 1:
                new_input = Int("input_" + str(idx))
                inputs.append(new_input)
                s.add(new_input == point[0])
                os = []
                const = []
                new_output = Bool("output_" + str(idx))
                pairs += 1
                idx += 1
                if point in points:
                    s.add(new_output)
                else:
                    s.add(Not(new_output))
            else:
                new_inputs = []
                for dim in range(len(point)):
                    new_inputs.append(Int("input_" + str(idx) + "_" + str(dim)))
                inputs.append(new_inputs)

                raise Exception("Unhandled len more than 1")


        FormulaFinder.add_leaf(s, "l1", pairs)
        FormulaFinder.add_leaf(s, "l2", pairs)
        FormulaFinder.add_leaf(s, "l3", pairs)
        FormulaFinder.add_node(s, "n1", "l1", "l2", pairs)
        FormulaFinder.add_node_rel(s, "root", "n1", "l3", pairs)
        if not len(mins) == 1:
            raise Exception("Unsupported dimension")
        FormulaFinder.add_bool_output(s, "root", mins[0], maxs[0])

        #print(s)

        if s.check() == sat:
            model = s.model()
            #print(model)
            interest = ["root",
                    "n1",
                    "l1", "l1const",
                    "l2", "l2const",
                    "l3", "l3const",
                   ]
            ret = {}
            for x in interest:
                ret[x] = model[Int(x)]
            return ret

        else:
            return None



    def printFormula(formula):
        def leaf2str(leaf, leafconst):
            if leaf == 0:
                return "x"
            if leaf == 1:
                return str(leafconst)

        def node2str(node):
            if node == 0:
                return '+'
            if node == 1:
                return '-'
            if node == 2:
                return '%'

        l1str = leaf2str(formula['l1'], formula['l1const'])
        l2str = leaf2str(formula['l2'], formula['l2const'])
        nodestr = node2str(formula['root'])
        return l1str + " " + nodestr + " " + l2str

    def printBoolean(formula, dim):
        if not formula:
            return "n/a"

        def leaf2str(leaf, leafconst):
            if int(str(leaf)) < dim:
                return "x_" + str(leaf)
            elif int(str(leaf)) == dim:
                return str(leafconst)
            else:
                raise Exception("Strange leaf value:", leaf)

        def node2str(node):
            if node == 0:
                return '=='
            if node == 1:
                return '<='
            if node == 2:
                return '%'

        l1str = leaf2str(formula['l1'], formula['l1const'])
        l2str = leaf2str(formula['l2'], formula['l2const'])
        l3str = leaf2str(formula['l3'], formula['l3const'])
        n1str = node2str(formula['n1'])
        rootstr = node2str(formula['root'])
        return "(" + l1str + " " + n1str + " " + l2str + ") " + rootstr + " " + l3str





    def find_boolean(points, mins, maxs, timeout=5000):
        #print("find_boolean", points, mins, maxs, timeout)
        s = Solver()
        s.set("timeout", timeout)
        # Generate input/output variables
        inputs = []
        outputs = []
        pairs = 0
        dim = len(points[0])
        idx = 0
        for point in gen_points(mins, maxs):
                new_inputs = []
                for d in range(dim):
                    new_inputs.append(Int("input_" + str(idx) + "_" + str(d)))
                inputs.append(new_inputs)
                for d in range(dim):
                    s.add(new_inputs[d] == point[d])
                os = []
                const = []
                new_output = Bool("output_" + str(idx))
                pairs += 1
                idx += 1
                if point in points:
                    s.add(new_output)
                else:
                    s.add(Not(new_output))

        FormulaFinder.add_leaf(s, "l1", dim, pairs)
        FormulaFinder.add_leaf(s, "l2", dim, pairs)
        FormulaFinder.add_leaf(s, "l3", dim, pairs)
        FormulaFinder.add_node(s, "n1", "l1", "l2", pairs)
        FormulaFinder.add_node_rel(s, "root", "n1", "l3", pairs)
        FormulaFinder.add_bool_output(s, "root", idx)

        #print(s)

        if s.check() == sat:
            model = s.model()
            interest = ["root",
                    "n1",
                    "l1", "l1const",
                    "l2", "l2const",
                    "l3", "l3const",
                   ]
            ret = {}
            for x in interest:
                ret[x] = model[Int(x)]
            return ret

        else:
            return None
